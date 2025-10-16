"use strict";
const cluster = require('cluster');
const net = require('net');
const tls = require('tls');
const http = require('http');
const moment = require('moment');
const fs = require('fs');
const async = require('async');
const support = require('./lib/support.js')();
global.config = require('./config.json');

const PROXY_VERSION = "0.28.2";
const DEFAULT_ALGO      = [ "rx/0" ];
const DEFAULT_ALGO_PERF = { "rx/0": 1, "rx/loki": 1 };

/*
 General file design/where to find things.

 Internal Variables
 IPC Registry
 Combined Functions
 Pool Definition
 Master Functions
 Miner Definition
 Slave Functions
 API Calls (Master-Only)
 System Init

 */
let debug = {
    pool: require('debug')('pool'),
    diff: require('debug')('diff'),
    blocks: require('debug')('blocks'),
    shares: require('debug')('shares'),
    miners: require('debug')('miners'),
    workers: require('debug')('workers'),
    balancer: require('debug')('balancer'),
    misc: require('debug')('misc')
};
global.threadName = '';
const nonceCheck32 = new RegExp("^[0-9a-f]{8}$");
const nonceCheck64 = new RegExp("^[0-9a-f]{16}$");
let activePorts = [];
let httpResponse = ' 200 OK\nContent-Type: text/plain\nContent-Length: 19\n\nMining Proxy Online';
let activeMiners = {};
let activeCoins = {};
let bans = {};
let activePools = {};
let activeWorkers = {};
let defaultPools = {};
let accessControl = {};
let lastAccessControlLoadTime = null;
let masterStats = {shares: 0, blocks: 0, hashes: 0};

// IPC Registry
function masterMessageHandler(worker, message, handle) {
    if (typeof message !== 'undefined' && 'type' in message){
        switch (message.type) {
            case 'blockFind':
            case 'shareFind':
                if (message.host in activePools){
                    activePools[message.host].sendShare(worker, message.data);
                }
                break;
            case 'needPoolState':
                worker.send({
                    type: 'poolState',
                    data: Object.keys(activePools)
                });
                for (let hostname in activePools){
                    if (activePools.hasOwnProperty(hostname)){
                        if (!is_active_pool(hostname)) continue;
                        let pool = activePools[hostname];
                        worker.send({
                            host: hostname,
                            type: 'newBlockTemplate',
                            data: pool.coinFuncs.getMasterJob(pool, worker.id)
                        });
                    }
                }
                break;
            case 'workerStats':
                activeWorkers[worker.id][message.minerID] = message.data;
                break;
        }
    }
}

function slaveMessageHandler(message) {
    switch (message.type) {
        case 'newBlockTemplate':
            if (message.host in activePools){
                if(activePools[message.host].activeBlocktemplate){
                    debug.workers(`Received a new block template for ${message.host} and have one in cache.  Storing`);
                    activePools[message.host].pastBlockTemplates.enq(activePools[message.host].activeBlocktemplate);
                } else {
                    debug.workers(`Received a new block template for ${message.host} do not have one in cache.`);
                }
                activePools[message.host].activeBlocktemplate = new activePools[message.host].coinFuncs.BlockTemplate(message.data);
                for (let miner in activeMiners){
                    if (activeMiners.hasOwnProperty(miner)){
                        let realMiner = activeMiners[miner];
                        if (realMiner.pool === message.host){
                            realMiner.pushNewJob();
                        }
                    }
                }
            }
            break;
        case 'poolState':
            message.data.forEach(function(hostname){
                if(!(hostname in activePools)){
                    global.config.pools.forEach(function(poolData){
                        if (!poolData.coin) poolData.coin = "xmr";
                        if (hostname === poolData.hostname){
                            activePools[hostname] = new Pool(poolData);
                        }
                    });
                }
            });
            break;
        case 'changePool':
            if (activeMiners.hasOwnProperty(message.worker) && activePools.hasOwnProperty(message.pool)){
                activeMiners[message.worker].pool = message.pool;
                activeMiners[message.worker].pushNewJob(true);
            }
            break;
        case 'disablePool':
            if (activePools.hasOwnProperty(message.pool)){
                activePools[message.pool].active = false;
                checkActivePools();
            }
            break;
        case 'enablePool':
            if (activePools.hasOwnProperty(message.pool)){
                activePools[message.pool].active = true;
                process.send({type: 'needPoolState'});
            }
            break;
    }
}

// Combined Functions
function readConfig() {
    let local_conf = JSON.parse(fs.readFileSync('config.json'));
    if (typeof global.config === 'undefined') {
        global.config = {};
    }
    for (let key in local_conf) {
        if (local_conf.hasOwnProperty(key) && (typeof global.config[key] === 'undefined' || global.config[key] !== local_conf[key])) {
            global.config[key] = local_conf[key];
        }
    }
    if (!cluster.isMaster) {
        activatePorts();
    }
}

// Pool Definition
function Pool(poolData){
    /*
    Pool data is the following:
     {
     "hostname": "pool.supportxmr.com",
     "port": 7777,
     "ssl": false,
     "share": 80,
     "username": "",
     "password": "",
     "keepAlive": true,
     "coin": "xmr"
     }
     Client Data format:
     {
        "method":"submit",
        "params":{
            "id":"12e168f2-db42-4eea-b56a-f1e7d57f94c9",
            "job_id":"/4FIQEI/Qq++EzzH1e03oTrWF5Ed",
            "nonce":"9e008000",
            "result":"4eee0b966418fdc3ec1a684322715e65765554f11ff8f7fed3f75ac45ef20300"
        },
        "id":1
     }
     */
    this.hostname = poolData.hostname;
    this.port = poolData.port;
    this.ssl = poolData.ssl;
    this.share = poolData.share;
    this.username = poolData.username;
    this.password = poolData.password;
    this.keepAlive = poolData.keepAlive;
    this.default = poolData.default;
    this.devPool = poolData.hasOwnProperty('devPool') && poolData.devPool === true;
    this.coin = poolData.coin;
    this.pastBlockTemplates = support.circularBuffer(4);
    this.coinFuncs = require(`./lib/${this.coin}.js`)();
    this.activeBlocktemplate = null;
    this.active = true;
    this.sendId = 1;
    this.sendLog = {};
    this.poolJobs = {};
    this.socket = null;
    this.allowSelfSignedSSL = true;
    // Partial checks for people whom havn't upgraded yet
    if (poolData.hasOwnProperty('allowSelfSignedSSL')){
        this.allowSelfSignedSSL = !poolData.allowSelfSignedSSL;
    }
    const algo_arr = poolData.algo ? (poolData.algo instanceof Array ? poolData.algo : [poolData.algo]) : DEFAULT_ALGO;
    this.default_algo_set = {};
    this.algos            = {};
    for (let i in algo_arr) this.algos[algo_arr[i]] = this.default_algo_set[algo_arr[i]] = 1;
    this.algos_perf = this.default_algos_perf = poolData.algo_perf && poolData.algo_perf instanceof Object ? poolData.algo_perf : DEFAULT_ALGO_PERF;
    this.blob_type  = poolData.blob_type;


    setInterval(function(pool) {
        if (pool.keepAlive && pool.socket && is_active_pool(pool.hostname)) pool.sendData('keepalived');
    }, 30000, this);

    this.close_socket = function(){
        try {
            if (this.socket !== null){
                this.socket.end();
                this.socket.destroy();
            }
        } catch (e) {
            console.warn(global.threadName + "Had issues murdering the old socket. Om nom: " + e)
        }
        this.socket = null;
    };

    this.disable = function(){
        for (let worker in cluster.workers){
            if (cluster.workers.hasOwnProperty(worker)){
                cluster.workers[worker].send({type: 'disablePool', pool: this.hostname});
            }
        }
        this.active = false;

        this.close_socket();
    };

    this.connect = function(hostname){
	function connect2(pool) {
                pool.close_socket();

	        if (pool.ssl){
	            pool.socket = tls.connect(pool.port, pool.hostname, {rejectUnauthorized: pool.allowSelfSignedSSL})
		    .on('connect', () => { poolSocket(pool.hostname); })
		    .on('error', (err) => {
	                setTimeout(connect2, 30*1000, pool);
	                console.warn(`${global.threadName}SSL pool socket connect error from ${pool.hostname}: ${err}`);
	            });
	        } else {
	            pool.socket = net.connect(pool.port, pool.hostname)
		    .on('connect', () => { poolSocket(pool.hostname); })
		    .on('error', (err) => {
	                setTimeout(connect2, 30*1000, pool);
	                console.warn(`${global.threadName}Plain pool socket connect error from ${pool.hostname}: ${err}`);
	            });
	        }
	}

	let pool = activePools[hostname];
        pool.disable();
	connect2(pool);
    };
    this.sendData = function (method, params) {
        if (typeof params === 'undefined'){
            params = {};
        }
        let rawSend = {
            method: method,
            id: this.sendId++,
        };
        if (typeof this.id !== 'undefined'){
            params.id = this.id;
        }
        rawSend.params = params;
        if (this.socket === null || !this.socket.writable){
            return false;
        }
        this.socket.write(JSON.stringify(rawSend) + '\n');
        this.sendLog[rawSend.id] = rawSend;
        debug.pool(`Sent ${JSON.stringify(rawSend)} to ${this.hostname}`);
    };
    this.login = function () {
        this.sendData('login', {
            login: this.username,
            pass: this.password,
            agent: 'xmr-node-proxy/' + PROXY_VERSION,
            "algo": Object.keys(this.algos),
            "algo-perf": this.algos_perf
        });
        this.active = true;
        for (let worker in cluster.workers){
            if (cluster.workers.hasOwnProperty(worker)){
                cluster.workers[worker].send({type: 'enablePool', pool: this.hostname});
            }
        }
    };

    this.update_algo_perf = function (algos, algos_perf) {
        // do not update not changed algo/algo-perf
        const prev_algos          = this.algos;
        const prev_algos_perf     = this.algos_perf;
        const prev_algos_str      = JSON.stringify(Object.keys(prev_algos));
        const prev_algos_perf_str = JSON.stringify(prev_algos_perf);
        const algos_str           = JSON.stringify(Object.keys(algos));
        const algos_perf_str      = JSON.stringify(algos_perf);
        if ( algos_str === prev_algos_str && algos_perf_str === prev_algos_perf_str) return;
        const curr_time = Date.now();
        if (!this.last_common_algo_notify_time || curr_time - this.last_common_algo_notify_time > 5*60*1000 || algos_str !== prev_algos_str) {
            console.log("Setting common algo: " + algos_str + " with algo-perf: " + algos_perf_str + " for pool " + this.hostname);
            this.last_common_algo_notify_time = curr_time;
        }
        this.sendData('getjob', {
            "algo": Object.keys(this.algos = algos),
            "algo-perf": (this.algos_perf = algos_perf)
        });
    };
    this.sendShare = function (worker, shareData) {
        //btID - Block template ID in the poolJobs circ buffer.
        let job = this.poolJobs[worker.id].toarray().filter(function (job) {
            return job.id === shareData.btID;
        })[0];
        if (job) {
            let submitParams = {
                job_id:      job.masterJobID,
                nonce:       shareData.nonce,
                workerNonce: shareData.workerNonce,
                poolNonce:   job.poolNonce
            };
            if (shareData.resultHash) submitParams.result = shareData.resultHash;
            if (shareData.pow)        submitParams.pow    = shareData.pow;
            this.sendData('submit', submitParams);
        }
    };
}

// Master Functions
/*
The master performs the following tasks:
1. Serve all API calls.
2. Distribute appropriately modified block template bases to all pool servers.
3. Handle all to/from the various pool servers.
4. Manage and suggest miner changes in order to achieve correct h/s balancing between the various systems.
 */
function connectPools(){
    global.config.pools.forEach(function (poolData) {
        if (!poolData.coin) poolData.coin = "xmr";
        if (activePools.hasOwnProperty(poolData.hostname)){
            return;
        }
        activePools[poolData.hostname] = new Pool(poolData);
        activePools[poolData.hostname].connect(poolData.hostname);
    });
    let seen_coins = {};
    if (global.config.developerShare > 0){
        for (let pool in activePools){
            if (activePools.hasOwnProperty(pool)){
                if (seen_coins.hasOwnProperty(activePools[pool].coin)){
                    return;
                }
                let devPool = activePools[pool].coinFuncs.devPool;
                if (activePools.hasOwnProperty(devPool.hostname)){
                    return;
                }
                activePools[devPool.hostname] = new Pool(devPool);
                activePools[devPool.hostname].connect(devPool.hostname);
                seen_coins[activePools[pool].coin] = true;
            }
        }
    }
    for (let coin in seen_coins){
        if (seen_coins.hasOwnProperty(coin)){
            activeCoins[coin] = true;
        }
    }
}

let poolStates = {};

function balanceWorkers(){
    /*
    This function deals with handling how the pool deals with getting traffic balanced to the various pools.
    Step 1: Enumerate all workers (Child servers), and their miners/coins into known states
    Step 1: Enumerate all miners, move their H/S into a known state tagged to the coins and pools
    Step 2: Enumerate all pools, verify the percentages as fractions of 100.
    Step 3: Determine if we're sharing with the developers (Woohoo!  You're the best if you do!)
    Step 4: Process the state information to determine splits/moves.
    Step 5: Notify child processes of other pools to send traffic to if needed.

    The Master, as the known state holder of all information, deals with handling this data.
     */
    let minerStates = {};
    poolStates = {};
    for (let poolName in activePools){
        if (activePools.hasOwnProperty(poolName)){
            let pool = activePools[poolName];
            if (!poolStates.hasOwnProperty(pool.coin)){
                poolStates[pool.coin] = { 'totalPercentage': 0, 'activePoolCount': 0, 'devPool': false};
            }
            poolStates[pool.coin][poolName] = {
                miners: {},
                hashrate: 0,
                percentage: pool.share,
                devPool: pool.devPool,
                idealRate: 0
            };
            if(pool.devPool){
                poolStates[pool.coin].devPool = poolName;
                debug.balancer(`Found a developer pool enabled.  Pool is: ${poolName}`);
            } else if (is_active_pool(poolName)) {
                poolStates[pool.coin].totalPercentage += pool.share;
                ++ poolStates[pool.coin].activePoolCount;
            } else {
                console.error(`${global.threadName}Pool ${poolName} is disabled due to issues with it`);
            }
            if (!minerStates.hasOwnProperty(pool.coin)){
                minerStates[pool.coin] = {
                    hashrate: 0
                };
            }
        }
    }
    /*
    poolStates now contains an object that looks approximately like:
    poolStates = {
        'xmr':
            {
                'mine.xmrpool.net': {
                    'miners': {},
                    'hashrate': 0,
                    'percentage': 20,
                    'devPool': false,
                    'amtChange': 0
                 },
                 'donations.xmrpool.net': {
                     'miners': {},
                     'hashrate': 0,
                     'percentage': 0,
                     'devPool': true,
                     'amtChange': 0
                 },
                 'devPool': 'donations.xmrpool.net',
                 'totalPercentage': 20
            }
    }
     */
    for (let coin in poolStates){
        if(poolStates.hasOwnProperty(coin)){
            if (poolStates[coin].totalPercentage !== 100){
                debug.balancer(`Pools on ${coin} are using ${poolStates[coin].totalPercentage}% balance.  Adjusting.`);
                // Need to adjust all the pools that aren't the dev pool.
                if (poolStates[coin].totalPercentage) {
                    let percentModifier = 100 / poolStates[coin].totalPercentage;
                    for (let pool in poolStates[coin]){
                        if (poolStates[coin].hasOwnProperty(pool) && activePools.hasOwnProperty(pool)){
                            if (poolStates[coin][pool].devPool || !is_active_pool(pool)) continue;
                            poolStates[coin][pool].percentage *= percentModifier;
                        }
                    }
                } else if (poolStates[coin].activePoolCount) {
                    let addModifier = 100 / poolStates[coin].activePoolCount;
                    for (let pool in poolStates[coin]){
                        if (poolStates[coin].hasOwnProperty(pool) && activePools.hasOwnProperty(pool)){
                            if (poolStates[coin][pool].devPool || !is_active_pool(pool)) continue;
                            poolStates[coin][pool].percentage += addModifier;
                        }
                    }
                } else {
                    debug.balancer(`No active pools for ${coin} coin, so waiting for the next cycle.`);
                    continue;
                }

            }
            delete(poolStates[coin].totalPercentage);
            delete(poolStates[coin].activePoolCount);
        }
    }
    /*
     poolStates now contains an object that looks approximately like:
     poolStates = {
         'xmr':
         {
             'mine.xmrpool.net': {
                 'miners': {},
                 'hashrate': 0,
                 'percentage': 100,
                 'devPool': false
             },
             'donations.xmrpool.net': {
                 'miners': {},
                 'hashrate': 0,
                 'percentage': 0,
                 'devPool': true
             },
             'devPool': 'donations.xmrpool.net',
         }
     }
     */
    for (let workerID in activeWorkers){
        if (activeWorkers.hasOwnProperty(workerID)){
            for (let minerID in activeWorkers[workerID]){
                if (activeWorkers[workerID].hasOwnProperty(minerID)){
                    let miner = activeWorkers[workerID][minerID];
                    try {
                        let minerCoin = miner.coin;
                        if (!minerStates.hasOwnProperty(minerCoin)){
                            minerStates[minerCoin] = {
                                hashrate: 0
                            };
                        }
                        minerStates[minerCoin].hashrate += miner.avgSpeed;
                        poolStates[minerCoin][miner.pool].hashrate += miner.avgSpeed;
                        poolStates[minerCoin][miner.pool].miners[`${workerID}_${minerID}`] = miner.avgSpeed;
                    } catch (err) {}
                }
            }
        }
    }
    /*
    poolStates now contains the hashrate per pool.  This can be compared against minerStates/hashRate to determine
    the approximate hashrate that should be moved between pools once the general hashes/second per pool/worker
    is determined.
     */

    for (let coin in poolStates){
        if (poolStates.hasOwnProperty(coin) && minerStates.hasOwnProperty(coin)){
            let coinMiners = minerStates[coin];
            let coinPools = poolStates[coin];
            let devPool = coinPools.devPool;
            let highPools = {};
            let lowPools = {};
            delete(coinPools.devPool);
            if (devPool){
                let devHashrate = Math.floor(coinMiners.hashrate * (global.config.developerShare/100));
                coinMiners.hashrate -= devHashrate;
                coinPools[devPool].idealRate = devHashrate;
                debug.balancer(`DevPool on ${coin} is enabled.  Set to ${global.config.developerShare}% and ideally would have ${coinPools[devPool].idealRate}.  Currently has ${coinPools[devPool].hashrate}`);
                if (is_active_pool(devPool) && coinPools[devPool].idealRate > coinPools[devPool].hashrate){
                    lowPools[devPool] = coinPools[devPool].idealRate - coinPools[devPool].hashrate;
                    debug.balancer(`Pool ${devPool} is running a low hashrate compared to ideal.  Want to increase by: ${lowPools[devPool]} h/s`);
                } else if (!is_active_pool(devPool) || coinPools[devPool].idealRate < coinPools[devPool].hashrate){
                    highPools[devPool] = coinPools[devPool].hashrate - coinPools[devPool].idealRate;
                    debug.balancer(`Pool ${devPool} is running a high hashrate compared to ideal.  Want to decrease by: ${highPools[devPool]} h/s`);
                }
            }
            for (let pool in coinPools){
                if (coinPools.hasOwnProperty(pool) && pool !== devPool && activePools.hasOwnProperty(pool)){
                    coinPools[pool].idealRate = Math.floor(coinMiners.hashrate * (coinPools[pool].percentage/100));
                    if (is_active_pool(pool) && coinPools[pool].idealRate > coinPools[pool].hashrate){
                        lowPools[pool] = coinPools[pool].idealRate - coinPools[pool].hashrate;
                        debug.balancer(`Pool ${pool} is running a low hashrate compared to ideal.  Want to increase by: ${lowPools[pool]} h/s`);
                    } else if (!is_active_pool(pool) || coinPools[pool].idealRate < coinPools[pool].hashrate){
                        highPools[pool] = coinPools[pool].hashrate - coinPools[pool].idealRate;
                        debug.balancer(`Pool ${pool} is running a high hashrate compared to ideal.  Want to decrease by: ${highPools[pool]} h/s`);
                    }
                    //activePools[pool].share = coinPools[pool].percentage;
                }
            }
            if (Object.keys(highPools).length === 0 && Object.keys(lowPools).length === 0){
                debug.balancer(`No high or low ${coin} coin pools, so waiting for the next cycle.`);
                continue;
            }
            let freed_miners = {};
            if (Object.keys(highPools).length > 0){
                for (let pool in highPools){
                    if (highPools.hasOwnProperty(pool)){
                        for (let miner in coinPools[pool].miners){
                            if (coinPools[pool].miners.hasOwnProperty(miner)){
                                if ((!is_active_pool(pool) || coinPools[pool].miners[miner] <= highPools[pool]) && coinPools[pool].miners[miner] !== 0){
                                    highPools[pool] -= coinPools[pool].miners[miner];
                                    freed_miners[miner] = coinPools[pool].miners[miner];
                                    debug.balancer(`Freeing up ${miner} on ${pool} for ${freed_miners[miner]} h/s`);
                                    delete(coinPools[pool].miners[miner]);
                                }
                            }
                        }
                    }
                }
            }
            let minerChanges = {};
            if (Object.keys(lowPools).length > 0){
                for (let pool in lowPools){
                    if (lowPools.hasOwnProperty(pool)){
                        minerChanges[pool] = [];
                        // fit low pools without overflow
                        if (Object.keys(freed_miners).length > 0){
                            for (let miner in freed_miners){
                                if (freed_miners.hasOwnProperty(miner)){
                                    if (freed_miners[miner] <= lowPools[pool]){
                                        minerChanges[pool].push(miner);
                                        lowPools[pool] -= freed_miners[miner];
                                        debug.balancer(`Snagging up ${miner} for ${pool} for ${freed_miners[miner]} h/s`);
                                        delete(freed_miners[miner]);
                                    }
                                }
                            }
                        }
                        if(lowPools[pool] > 100){
                            for (let donatorPool in coinPools){
                                if(coinPools.hasOwnProperty(donatorPool) && !lowPools.hasOwnProperty(donatorPool)){
                                    for (let miner in coinPools[donatorPool].miners){
                                        if (coinPools[donatorPool].miners.hasOwnProperty(miner)){
                                            if (coinPools[donatorPool].miners[miner] <= lowPools[pool] && coinPools[donatorPool].miners[miner] !== 0){
                                                minerChanges[pool].push(miner);
                                                lowPools[pool] -= coinPools[donatorPool].miners[miner];
                                                debug.balancer(`Moving ${miner} for ${pool} from ${donatorPool} for ${coinPools[donatorPool].miners[miner]} h/s`);
                                                delete(coinPools[donatorPool].miners[miner]);
                                            }
                                            if (lowPools[pool] < 50){
                                                break;
                                            }
                                        }
                                    }
                                    if (lowPools[pool] < 50){
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
                // fit low pools with overflow except devPool
                if (Object.keys(freed_miners).length > 0){
                    for (let pool in lowPools){
                        if (lowPools.hasOwnProperty(pool) && pool !== devPool){
                            if (!(pool in minerChanges)) minerChanges[pool] = [];
                            for (let miner in freed_miners){
                                if (freed_miners.hasOwnProperty(miner)){
                                    minerChanges[pool].push(miner);
                                    lowPools[pool] -= freed_miners[miner];
                                    debug.balancer(`Moving overflow ${miner} for ${pool} for ${freed_miners[miner]} h/s`);
                                    delete(freed_miners[miner]);
                                }
                            }
                        }
                    }
                }
            }
            for (let pool in minerChanges){
                if(minerChanges.hasOwnProperty(pool) && minerChanges[pool].length > 0){
                    minerChanges[pool].forEach(function(miner){
                        let minerBits = miner.split('_');
                        if (cluster.workers[minerBits[0]]) cluster.workers[minerBits[0]].send({
                            type: 'changePool',
                            worker: minerBits[1],
                            pool: pool
                        });
                    });
                }
            }
        }
    }
}

let hs_algo = ""; // common algo for human_hashrate

function enumerateWorkerStats() {
    let stats, global_stats = {miners: 0, hashes: 0, hashRate: 0, diff: 0};
    let pool_algos = {};
    let pool_algos_perf = {};
    for (let poolID in activeWorkers){
        if (activeWorkers.hasOwnProperty(poolID)){
            stats = {
                miners: 0,
                hashes: 0,
                hashRate: 0,
                diff: 0
            };
            let inactivityDeadline = (typeof global.config.minerInactivityTime === 'undefined') ? Math.floor((Date.now())/1000) - 120
                : (global.config.minerInactivityTime <= 0 ? 0 : Math.floor((Date.now())/1000) - global.config.minerInactivityTime);
            for (let workerID in activeWorkers[poolID]){
                if (activeWorkers[poolID].hasOwnProperty(workerID)) {
                    let workerData = activeWorkers[poolID][workerID];
                    if (typeof workerData !== 'undefined') {
                        try{
                            if (workerData.lastContact < inactivityDeadline){
                                delete activeWorkers[poolID][workerID];
                                continue;
                            }
                            ++ stats.miners;
                            stats.hashes += workerData.hashes;
                            stats.hashRate += workerData.avgSpeed;
                            stats.diff += workerData.diff;
                            // process smart miners and assume all other miners to only support pool algo
                            let miner_algos = workerData.algos;
                            if (!miner_algos) miner_algos = activePools[workerData.pool].default_algo_set;
    		            if (workerData.pool in pool_algos) { // compute union of miner_algos and pool_algos[workerData.pool]
			        for (let algo in pool_algos[workerData.pool]) {
			           if (!(algo in miner_algos)) delete pool_algos[workerData.pool][algo];
			       }
                            } else {
                                pool_algos[workerData.pool] = miner_algos;
                                pool_algos_perf[workerData.pool] = {};
                            }
                            if (workerData.algos_perf) { // only process smart miners and add algo_perf from all smart miners
                                for (let algo in workerData.algos_perf) {
                                    if (algo in pool_algos_perf[workerData.pool]) pool_algos_perf[workerData.pool][algo] += workerData.algos_perf[algo];
                                    else pool_algos_perf[workerData.pool][algo] = workerData.algos_perf[algo];
                                }
                            }
                        } catch (err) {
                            delete activeWorkers[poolID][workerID];
                        }
                    } else {
                        delete activeWorkers[poolID][workerID];
                    }
                }
            }
            global_stats.miners += stats.miners;
            global_stats.hashes += stats.hashes;
            global_stats.hashRate += stats.hashRate;
            global_stats.diff += stats.diff;
            debug.workers(`Worker: ${poolID} currently has ${stats.miners} miners connected at ${stats.hashRate} h/s with an average diff of ${Math.floor(stats.diff/stats.miners)}`);
        }
    }

    let pool_hs = "";
    for (let coin in poolStates) {
        if (!poolStates.hasOwnProperty(coin)) continue;
        for (let pool in poolStates[coin]) {
            if (!poolStates[coin].hasOwnProperty(pool) || !activePools.hasOwnProperty(pool) || poolStates[coin][pool].devPool || poolStates[coin][pool].hashrate === 0) continue;
            if (pool_hs != "") pool_hs += ", ";
            pool_hs += `${pool}/${poolStates[coin][pool].percentage.toFixed(2)}%`;
        }
    }
    if (pool_hs != "") pool_hs = " (" + pool_hs + ")";

    // do update of algo/algo-perf if it was changed
    hs_algo = ""; // common algo for human_hashrate
    for (let pool in pool_algos) {
        let pool_algos_perf2 = pool_algos_perf[pool];
        if (Object.keys(pool_algos_perf2).length === 0) pool_algos_perf2 = activePools[pool].default_algos_perf;
        activePools[pool].update_algo_perf(pool_algos[pool], pool_algos_perf2);
        if (Object.keys(pool_algos[pool]).length == 1) {
            if      ("c29s" in pool_algos[pool]) hs_algo = (hs_algo === "c29s" || hs_algo === "") ? "c29s" : "h/s";
            else if ("c29v" in pool_algos[pool]) hs_algo = (hs_algo === "c29v" || hs_algo === "") ? "c29v" : "h/s";
            else hs_algo = "h/s";
        } else {
            hs_algo = "h/s";
        }
    }

    const hs = support.human_hashrate(global_stats.hashRate, hs_algo);
    console.log(`The proxy currently has ${global_stats.miners} miners connected at ${hs}${pool_hs}` + (global_stats.miners ? ` with an average diff of ${Math.floor(global_stats.diff/global_stats.miners)}` : ""));
}

function poolSocket(hostname){
    let pool = activePools[hostname];
    let socket = pool.socket;
    let dataBuffer = '';
    socket.on('data', (d) => {
        dataBuffer += d;
        if (dataBuffer.indexOf('\n') !== -1) {
            let messages = dataBuffer.split('\n');
            let incomplete = dataBuffer.slice(-1) === '\n' ? '' : messages.pop();
            for (let i = 0; i < messages.length; i++) {
                let message = messages[i];
                if (message.trim() === '') {
                    continue;
                }
                let jsonData;
                try {
                    jsonData = JSON.parse(message);
                }
                catch (e) {
                    if (message.indexOf('GET /') === 0) {
                        if (message.indexOf('HTTP/1.1') !== -1) {
                            socket.end('HTTP/1.1' + httpResponse);
                            break;
                        }
                        else if (message.indexOf('HTTP/1.0') !== -1) {
                            socket.end('HTTP/1.0' + httpResponse);
                            break;
                        }
                    }

                    console.warn(`${global.threadName}Pool wrong reply error from ${pool.hostname}: ${message}`);
                    socket.destroy();

                    break;
                }
                handlePoolMessage(jsonData, pool.hostname);
            }
            dataBuffer = incomplete;
        }
    }).on('error', (err) => {
        console.warn(`${global.threadName}Pool socket error from ${pool.hostname}: ${err}`);
        activePools[pool.hostname].disable();
        setTimeout(activePools[pool.hostname].connect, 30*1000, pool.hostname);
    }).on('close', () => {
        console.warn(`${global.threadName}Pool socket closed from ${pool.hostname}`);
        activePools[pool.hostname].disable();
        setTimeout(activePools[pool.hostname].connect, 30*1000, pool.hostname);
    });
    socket.setKeepAlive(true);
    socket.setEncoding('utf8');
    console.log(`${global.threadName}Connected to pool: ${pool.hostname}`);
    pool.login();
}

function handlePoolMessage(jsonData, hostname){
    let pool = activePools[hostname];
    debug.pool(`Received ${JSON.stringify(jsonData)} from ${pool.hostname}`);
    if (jsonData.hasOwnProperty('method')){
        // The only time method is set, is with a push of data.  Everything else is a reply/
        if (jsonData.method === 'job'){
            handleNewBlockTemplate(jsonData.params, hostname);
        }
    } else {
        if (jsonData.error !== null){
            console.error(`${global.threadName}Error response from pool ${pool.hostname}: ${JSON.stringify(jsonData.error)}`);
            if ((jsonData.error instanceof Object) && (typeof jsonData.error.message === 'string') && jsonData.error.message.includes("Unauthenticated")) activePools[hostname].disable();
            return;
        }
        let sendLog = pool.sendLog[jsonData.id];
        switch(sendLog.method){
            case 'login':
                pool.id = jsonData.result.id;
                handleNewBlockTemplate(jsonData.result.job, hostname);
                break;
            case 'getjob':
                // null for same job
                if (jsonData.result !== null) handleNewBlockTemplate(jsonData.result, hostname);
                break;
            case 'submit':
                sendLog.accepted = true;
                break;
        }
    }
}

function handleNewBlockTemplate(blockTemplate, hostname){
    if (!blockTemplate) {
        console.error(`${global.threadName}Empty response from pool ${hostname}`);
        activePools[hostname].disable();
        return;
    }
    let pool = activePools[hostname];
    let algo_variant = "";
    if (blockTemplate.algo) algo_variant += "algo: " + blockTemplate.algo;
    if (blockTemplate.variant) {
        if (algo_variant != "") algo_variant += ", ";
        algo_variant += "variant: " + blockTemplate.variant;
    }
    if (algo_variant != "") algo_variant = " (" + algo_variant + ")";
    console.log(`Received new block template on ${blockTemplate.height} height${algo_variant} with ${blockTemplate.target_diff} target difficulty from ${pool.hostname}`);
    if(pool.activeBlocktemplate){
        if (pool.activeBlocktemplate.job_id === blockTemplate.job_id){
            debug.pool('No update with this job, it is an upstream dupe');
            return;
        }
        debug.pool('Storing the previous block template');
        pool.pastBlockTemplates.enq(pool.activeBlocktemplate);
    }
    if (!blockTemplate.algo)      blockTemplate.algo = pool.coinFuncs.detectAlgo(pool.default_algo_set, 16 * parseInt(blockTemplate.blocktemplate_blob[0]) + parseInt(blockTemplate.blocktemplate_blob[1]));
    if (!blockTemplate.blob_type) blockTemplate.blob_type = pool.blob_type;
    pool.activeBlocktemplate = new pool.coinFuncs.MasterBlockTemplate(blockTemplate);
    for (let id in cluster.workers){
        if (cluster.workers.hasOwnProperty(id)){
            cluster.workers[id].send({
                host: hostname,
                type: 'newBlockTemplate',
                data: pool.coinFuncs.getMasterJob(pool, id)
            });
        }
    }
}

function is_active_pool(hostname) {
    let pool = activePools[hostname];
    if ((cluster.isMaster && !pool.socket) || !pool.active || pool.activeBlocktemplate === null) return false;

    let top_height = 0;
    for (let poolName in activePools){
        if (!activePools.hasOwnProperty(poolName)) continue;
        let pool2 = activePools[poolName];
        if (pool2.coin != pool.coin) continue;
        if ((cluster.isMaster && !pool2.socket) || !pool2.active || pool2.activeBlocktemplate === null) continue;
        if (Math.abs(pool2.activeBlocktemplate.height - pool.activeBlocktemplate.height) > 1000) continue; // different coin templates, can't compare here
        if (pool2.activeBlocktemplate.height > top_height) top_height = pool2.activeBlocktemplate.height;
    }

    if (pool.activeBlocktemplate.height < top_height - 5) return false;
    return true;
}

// Miner Definition
function Miner(id, params, ip, pushMessage, portData, minerSocket) {
    // Arguments
    // minerId, params, ip, pushMessage, portData
    // Username Layout - <address in BTC or XMR>.<Difficulty>
    // Password Layout - <password>.<miner identifier>.<payment ID for XMR>
    // Default function is to use the password so they can login.  Identifiers can be unique, payment ID is last.
    // If there is no miner identifier, then the miner identifier is set to the password
    // If the password is x, aka, old-logins, we're not going to allow detailed review of miners.

    const login_diff_split = params.login ? params.login.split("+") : "";
    if (!params.pass) params.pass = "x";
    const pass_algo_split = params.pass.split("~");
    const pass_split = pass_algo_split[0].split(":");

    // Miner Variables
    this.coin = portData.coin;
    this.coinFuncs = require(`./lib/${this.coin}.js`)();
    this.coinSettings = global.config.coinSettings[this.coin];
    this.login = login_diff_split[0];  // Documentation purposes only.
    this.user = login_diff_split[0];  // For accessControl and workerStats.
    this.password = pass_split[0];  // For accessControl and workerStats.
    this.agent = params.agent;  // Documentation purposes only.
    this.ip = ip;  // Documentation purposes only.

    if (pass_algo_split.length == 2) {
       const algo_name = pass_algo_split[1];
       params.algo = [ algo_name ];
       params["algo-perf"] = {};
       params["algo-perf"][algo_name] = 1;
    }

    if (params.algo && (params.algo instanceof Array)) { // To report union of defined algo set to the pool for all its miners
        for (let i in params.algo) {
            this.algos = {};
            for (let i in params.algo) this.algos[params.algo[i]] = 1;
        }
    }
    this.algos_perf = params["algo-perf"]; // To report sum of defined algo_perf to the pool for all its miners
    this.socket = minerSocket;
    this.pushMessage = pushMessage;
    this.getNewJob = function (bashCache) {
       return this.coinFuncs.getJob(this, activePools[this.pool].activeBlocktemplate, bashCache);
    };
    this.pushNewJob = function (bashCache) {
       const job = this.getNewJob(bashCache);
       if (this.protocol === "grin") {
           this.pushMessage({method: 'getjobtemplate', result: job});
       } else {
           this.pushMessage({method: 'job', params: job});
       }
    };
    this.error = "";
    this.valid_miner = true;
    this.incremented = false;
    this.fixed_diff = false;
    this.difficulty = portData.diff;
    this.connectTime = Date.now();

    if (!defaultPools.hasOwnProperty(portData.coin) || !is_active_pool(defaultPools[portData.coin])) {
        for (let poolName in activePools){
            if (activePools.hasOwnProperty(poolName)){
                let pool = activePools[poolName];
                if (pool.coin != portData.coin || pool.devPool) continue;
		if (is_active_pool(poolName)) {
                    this.pool = poolName;
                    break;
                }
            }
        }
    }
    if (!this.pool) this.pool = defaultPools[portData.coin];

    if (login_diff_split.length === 2) {
        this.fixed_diff = true;
        this.difficulty = Number(login_diff_split[1]);
        this.user = login_diff_split[0];
    } else if (login_diff_split.length > 2) {
        this.error = "Too many options in the login field";
        this.valid_miner = false;
    }

    if (activePools[this.pool].activeBlocktemplate === null){
        this.error = "No active block template";
        this.valid_miner = false;
    }

    // Verify if user/password is in allowed client connects
    if (!isAllowedLogin(this.user, this.password)) {
        this.error = "Unauthorized access";
        this.valid_miner = false;
    }

    this.id = id;
    this.heartbeat = function () {
        this.lastContact = Date.now();
    };
    this.heartbeat();

    // VarDiff System
    this.lastShareTime = Date.now() / 1000 || 0;

    this.shares = 0;
    this.blocks = 0;
    this.hashes = 0;

    this.validJobs = support.circularBuffer(5);

    this.cachedJob = null;

    this.identifier = global.config.addressWorkerID ? this.user : pass_split[0];

    this.logString = (this.identifier && this.identifier != "x") ? this.identifier + " (" + this.ip + ")" : this.ip;

    if (this.algos) {
        const pool = activePools[this.pool];
        if (pool) {
            const blockTemplate = pool.activeBlocktemplate;
            if (blockTemplate && blockTemplate.blob) {
                const pool_algo = pool.coinFuncs.detectAlgo(pool.default_algo_set, 16 * parseInt(blockTemplate.blob[0]) + parseInt(blockTemplate.blob[1]));
                if (!(pool_algo in this.algos)) {
                    console.warn("Your miner " + this.logString + " does not have " + pool_algo + " algo support. Please update it.");
                }
            }
        }
    }

    this.minerStats = function(){
        if (this.socket.destroyed && !global.config.keepOfflineMiners){
            delete activeMiners[this.id];
            return;
        }
        return {
	    active: !this.socket.destroyed,
            shares: this.shares,
            blocks: this.blocks,
            hashes: this.hashes,
            avgSpeed: this.hashes/(Math.floor((Date.now() - this.connectTime)/1000)),
            diff: this.difficulty,
            connectTime: this.connectTime,
            lastContact: Math.floor(this.lastContact/1000),
            lastShare: this.lastShareTime,
            coin: this.coin,
            pool: this.pool,
            id: this.id,
            identifier: this.identifier,
            ip: this.ip,
            agent: this.agent,
            algos: this.algos,
            algos_perf: this.algos_perf,
            logString: this.logString,
        };
    };

    // Support functions for how miners activate and run.
    this.updateDifficulty = function(){
        if (this.hashes > 0 && !this.fixed_diff) {
            const new_diff = Math.floor(this.hashes / (Math.floor((Date.now() - this.connectTime) / 1000))) * this.coinSettings.shareTargetTime;
            if (this.setNewDiff(new_diff)) {
                this.pushNewJob();
            }
        }
    };

    this.setNewDiff = function (difficulty) {
        this.newDiff = Math.round(difficulty);
        if (this.newDiff > this.coinSettings.maxDiff) {
            this.newDiff = this.coinSettings.maxDiff;
        }
        if (this.newDiff < this.coinSettings.minDiff) {
            this.newDiff = this.coinSettings.minDiff;
        }
        if (this.difficulty === this.newDiff) {
            return false;
        }
        debug.diff(global.threadName + "Difficulty change to: " + this.newDiff + " For: " + this.logString);
        if (this.hashes > 0){
            debug.diff(global.threadName + "Hashes: " + this.hashes + " in: " + Math.floor((Date.now() - this.connectTime)/1000) + " seconds gives: " +
                Math.floor(this.hashes/(Math.floor((Date.now() - this.connectTime)/1000))) + " hashes/second or: " +
                Math.floor(this.hashes/(Math.floor((Date.now() - this.connectTime)/1000))) *this.coinSettings.shareTargetTime + " difficulty versus: " + this.newDiff);
        }
        return true;
    };
}

// Slave Functions
function isAllowedLogin(username, password) {
    // If controlled login is not enabled, everybody can connnect (return true)
    if (typeof global.config['accessControl'] !== 'object'
        || global.config['accessControl'].enabled !== true) {
        return true;
    }

    // If user is in the list (return true)
    if (isInAccessControl(username, password)) {
        return true;
    }
    // If user is not in the list ...
    else {

        // ... and accessControl has not been loaded in last minute (prevent HD flooding in case of attack)
        if (lastAccessControlLoadTime === null
            || (Date.now() - lastAccessControlLoadTime) / 1000 > 60) {

            // Take note of new load time
            lastAccessControlLoadTime = Date.now();

            // Re-load file from disk and inject in accessControl
            accessControl = JSON.parse(fs.readFileSync(global.config['accessControl']['controlFile']));

            // Re-verify if the user is in the list
            return isInAccessControl(username, password);
        }

        // User is not in the list, and not yet ready to re-load from disk
        else {
            // TODO Take notes of IP/Nb of rejections.  Ultimately insert IP in bans after X threshold
            return false;
        }
    }
}
function isInAccessControl(username, password) {
    return typeof accessControl[username] !== 'undefined' && accessControl[username] === password;
}

function handleMinerData(minerSocket, id, method, params, ip, portData, sendReply, sendReplyFinal, pushMessage) {
    switch (method) {
        case 'login': { // grin and default
            if (ip in bans) {
                sendReplyFinal("IP Address currently banned");
                return;
            }
            if (!params) {
                sendReplyFinal("No params specified");
                return;
            }
            let difficulty = portData.difficulty;
            const minerId = support.get_new_id();
            if (!portData.coin) portData.coin = "xmr";
            let miner = new Miner(minerId, params, ip, pushMessage, portData, minerSocket);
            if (!miner.valid_miner) {
                console.warn(global.threadName + "Invalid miner: " + miner.logString + ", disconnecting due to: " + miner.error);
                sendReplyFinal(miner.error);
                return;
            }
            process.send({type: 'newMiner', data: miner.port});
            activeMiners[minerId] = miner;
            minerSocket.minerId = minerId;
            // clean old miners with the same name/ip/agent
            if (global.config.keepOfflineMiners) {
                for (let miner_id in activeMiners) {
                    if (activeMiners.hasOwnProperty(miner_id)) {
                        let realMiner = activeMiners[miner_id];
                        if (realMiner.socket.destroyed && realMiner.identifier === miner.identifier && realMiner.ip === miner.ip && realMiner.agent === miner.agent) {
                            delete activeMiners[miner_id];
                        }
                    }
                }
            }
            if (id === "Stratum") {
                sendReply(null, "ok");
                miner.protocol = "grin";
            } else {
                sendReply(null, { id: minerId, job: miner.getNewJob(), status: 'OK' });
                miner.protocol = "default";
            }
            break;
        }

        case 'getjobtemplate': { // grin only
            const minerId = minerSocket.minerId ? minerSocket.minerId : "";
            let miner = activeMiners[minerId];
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            sendReply(null, miner.getNewJob());
            break;
        }

        case 'getjob': {
            if (!params) {
                sendReplyFinal("No params specified");
                return;
            }
            let miner = activeMiners[params.id];
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            sendReply(null, miner.getNewJob());
            break;
        }

        case 'submit': { // grin and default
            if (!params) {
                sendReplyFinal("No params specified");
                return;
            }
            const minerId = params.id ? params.id : (minerSocket.minerId ? minerSocket.minerId : "");
            let miner = activeMiners[minerId];
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            if (typeof (params.job_id) === 'number') params.job_id = params.job_id.toString(); // for grin miner

            let job = miner.validJobs.toarray().filter(function (job) {
                return job.id === params.job_id;
            })[0];

            if (!job) {
                sendReply('Invalid job id');
                return;
            }

            const blob_type_num = job.blob_type;
            const is_bad_nonce = miner.coinFuncs.blobTypeGrin(blob_type_num) ?
                                 (typeof params.nonce !== 'number') || !(params.pow instanceof Array) || (params.pow.length != miner.coinFuncs.c29ProofSize(blob_type_num)) :
                                 (typeof params.nonce !== 'string') || !(miner.coinFuncs.nonceSize(blob_type_num) == 8 ? nonceCheck64.test(params.nonce) : nonceCheck32.test(params.nonce) );

            if (is_bad_nonce) {
                console.warn(global.threadName + 'Malformed nonce: ' + JSON.stringify(params) + ' from ' + miner.logString);
                sendReply('Duplicate share');
                return;
            }

            if (job.submissions.indexOf(params.nonce) !== -1) {
                console.warn(global.threadName + 'Duplicate share: ' + JSON.stringify(params) + ' from ' + miner.logString);
                sendReply('Duplicate share');
                return;
            }

            const nonce_test = miner.coinFuncs.blobTypeGrin(blob_type_num) ? params.pow.join(':') : params.nonce;

            job.submissions.push(nonce_test);
            let activeBlockTemplate = activePools[miner.pool].activeBlocktemplate;
            let pastBlockTemplates = activePools[miner.pool].pastBlockTemplates;

            let blockTemplate = activeBlockTemplate.id === job.templateID ? activeBlockTemplate : pastBlockTemplates.toarray().filter(function (t) {
                return t.id === job.templateID;
            })[0];

            if (!blockTemplate) {
                console.warn(global.threadName + 'Block expired, Height: ' + job.height + ' from ' + miner.logString);
                if (miner.incremented === false){
                    miner.newDiff = miner.difficulty + 1;
                    miner.incremented = true;
                } else {
                    miner.newDiff = miner.difficulty - 1;
                    miner.incremented = false;
                }
                miner.pushNewJob(true);
                sendReply('Block expired');
                return;
            }

            let shareAccepted = miner.coinFuncs.processShare(miner, job, blockTemplate, params);

            if (!shareAccepted) {
                sendReply('Low difficulty share');
                return;
            }

            miner.lastShareTime = Date.now() / 1000 || 0;

            if (miner.protocol === "grin") {
                sendReply(null, "ok");
            } else {
                sendReply(null, {status: 'OK'});
            }
            break;
        }

        case 'keepalived': {
            if (!params) {
                sendReplyFinal("No params specified");
                return;
            }
            let miner = activeMiners[params.id];
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            sendReply(null, { status: 'KEEPALIVED' });
            break;
        }
    }
}

function activateHTTP() {
	var jsonServer = http.createServer((req, res) => {
		if (global.config.httpUser && global.config.httpPass) {
			var auth = req.headers['authorization'];  // auth is in base64(username:password)  so we need to decode the base64
			if (!auth) {
				res.statusCode = 401;
				res.setHeader('WWW-Authenticate', 'Basic realm="Secure Area"');
				res.end('<html><body>Unauthorized XNP access.</body></html>');
				return;
			}
			debug.misc("Authorization Header is: ", auth);
			var tmp = auth.split(' ');
	                var buf = Buffer.from(tmp[1], 'base64');
        	        var plain_auth = buf.toString();
			debug.misc("Decoded Authorization ", plain_auth);
			var creds = plain_auth.split(':');
			var username = creds[0];
			var password = creds[1];
			if (username !== global.config.httpUser || password !== global.config.httpPass) {
				res.statusCode = 401;
				res.setHeader('WWW-Authenticate', 'Basic realm="Secure Area"');
				res.end('<html><body>Wrong login.</body></html>');
				return;
			}
		}

		if (req.url == "/") {
			let totalWorkers = 0, totalHashrate = 0;
			let poolHashrate = [];
			let poolData = [];
		    let miners = {};
		    let offline_miners = {};
			let miner_names = {};
			let hashHistory = []; // For storing hashrate history data
			let onlineMinersCount = 0; 
			let offlineMinersCount = 0; 
    		
			for (let workerID in activeWorkers) {
				if (!activeWorkers.hasOwnProperty(workerID)) continue;
				for (let minerID in activeWorkers[workerID]){
                	if (!activeWorkers[workerID].hasOwnProperty(minerID)) continue;
					let miner = activeWorkers[workerID][minerID];
					if (typeof(miner) === 'undefined' || !miner) continue;
					if (miner.active) {
  						miners[miner.id] = miner;
						const name = miner.logString;
                        miner_names[name] = 1;
						++ totalWorkers;
						totalHashrate += miner.avgSpeed;
						if (!poolHashrate[miner.pool]) poolHashrate[miner.pool] = 0;
						poolHashrate[miner.pool] += miner.avgSpeed;
                        onlineMinersCount++; 
                    } else {
						offline_miners[miner.id] = miner;
                        offlineMinersCount++; 
					}
				}
			}
    		
			for (let offline_miner_id in offline_miners) {
				const miner = offline_miners[offline_miner_id];
				const name = miner.logString;
				if (name in miner_names) continue;
				miners[miner.id] = miner;
				miner_names[name] = 1;
			}
			
			let tableBody = "";
    		for (let miner_id in miners) {
				const miner = miners[miner_id];
				const name = miner.logString;
				let avgSpeed = miner.active ? support.human_hashrate(miner.avgSpeed, activePools[miner.pool].activeBlocktemplate.algo) : "offline";
				let agent_parts = miner.agent.split(" ");
				let statusClass = miner.active ? "text-success" : "text-danger";
				
				tableBody += `
				<tr>
					<td>${name}</td>
					<td><span class="${statusClass}">${avgSpeed}</span></td>
					<td>${miner.diff}</td>
					<td>${miner.shares}</td>
					<td>${miner.hashes}</td>
					<td>${moment.unix(miner.lastShare).fromNow(true)} ago</td>
					<td>${moment.unix(miner.lastContact).fromNow(true)} ago</td>
					<td>${moment(miner.connectTime).fromNow(true)} ago</td>
					<td>${miner.pool}</td>
					<td><div class="tooltip-wrapper" data-bs-toggle="tooltip" title="${miner.agent}">${agent_parts[0]}</div></td>
				</tr>
				`;
			}
			
			// Prepare pool data for visualization
			let poolCardsHtml = "";
    		for (let poolName in poolHashrate) {
				let poolPercentage = totalHashrate ? (100*poolHashrate[poolName]/totalHashrate).toFixed(2) : "100.0";
				let targetDiff = activePools[poolName].activeBlocktemplate ? activePools[poolName].activeBlocktemplate.targetDiff : "?";
                let walletId = activePools[poolName].username;
                const hs = support.human_hashrate(poolHashrate[poolName], activePools[poolName].activeBlocktemplate.algo);
				
				// Format algo variant info
				let algo_variant = "";
                if (activePools[poolName].activeBlocktemplate.algo) algo_variant += "algo: " + activePools[poolName].activeBlocktemplate.algo;
                if (activePools[poolName].activeBlocktemplate.variant) {
                    if (algo_variant != "") algo_variant += ", ";
                    algo_variant += "variant: " + activePools[poolName].activeBlocktemplate.variant;
                }
                if (algo_variant != "") algo_variant = " (" + algo_variant + ")";
				
				// Add pool data for chart
				poolData.push({
					name: poolName,
					hashrate: poolHashrate[poolName],
					percentage: poolPercentage
				});
				
				// Create card for each pool
				let cardClass = poolName.includes("C3Pool") ? "border-primary" : "border-secondary";
				let dashboardLink = poolName.includes("C3Pool") 
					? `<a href="https://c3pool.com/oldui/cn/#/dashboard?addr=${walletId}" class="btn btn-sm btn-outline-primary mt-2" target="_blank">C3Pool Dashboard</a>` 
					: "";
				
				poolCardsHtml += `
				<div class="col-md-6 col-lg-4 mb-3">
					<div class="card ${cardClass} h-100">
						<div class="card-header">
							<h5 class="card-title">${poolName}</h5>
						</div>
						<div class="card-body">
							<div class="d-flex justify-content-between mb-2">
								<span>Hashrate:</span>
								<span class="fw-bold">${hs}</span>
							</div>
							<div class="d-flex justify-content-between mb-2">
								<span>Pool Share:</span>
								<span class="fw-bold">${poolPercentage}%</span>
							</div>
							<div class="d-flex justify-content-between mb-2">
								<span>Difficulty:</span>
								<span class="fw-bold">${targetDiff}</span>
							</div>
							<div class="text-muted small">${algo_variant}</div>
							${dashboardLink}
						</div>
					</div>
				</div>`;
			}

      // Config defaults
      if (!global.config.theme) global.config.theme = "light";
      if (!global.config.refreshTime) global.config.refreshTime = "60";

      totalHashrate = support.human_hashrate(totalHashrate, hs_algo);

      // Set up favicon
      let icon = `data:image/jpeg;base64,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jTTsz9DvEd4bzV7hs5CnYPw/+vmv5i4uxrxucVtdIe6v+3d/xufd5bS9lho+ev3/APAM2vjD0woAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKACgAoAKAPzp/4LCTF7f4QIf4DrGPx+w1/TfBuNeNyenzPWF4v5bfg0fC5nS9liZW66/18z9GJX8yV3PViTX824mr7evOq/tNv73c+3hHkio9htcxYUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFAH5x/wDBYDr8Jf8AuLf+2VfuXh1VvQxNLs4v701+h8rnUbShL1/r8T9HK/DT6oKACgAoAKACgAoAKACgAoAKACgAoAKACgBCcUAG4UwE3UWFdC7qBgDmkAtABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFACUABOKYCbhRYLigg0BcWkAUAFABQAUAFABQAUAFABQAUAFABQAUAFAH5yf8Fgf+aS/9xf8A9sq/afDj/mL/AO3P/bz5jO/+Xfz/AEP0br8WPpwoAKACgAoAKACgAoAKACgAoAKACgAoAKAGtTA8a/az+N03wC+DOpeJ7Lym1bzoraxjnXcjys2SCPTYr/pX03DuVLNsfDDz+HVt+Vv8zz8biPq9JzW585/CT/gqj4Z10w2fjvQ59Aujx9tsczQZ91+8PrX2mY8AYminLBVOZdnozy6GbwelVWPsbwJ8UvCfxM05L7wvr9jrVuwyDazBmHY5XqOc9RX5rjMBisDPkxFNxfme7SrU6qvB3OqBxXnG10O3Ux7gDmkAtABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFABQAUAFMBCQKLBca7AAk8Ackmmk27Cujx34qftb/AAt+EAePXPE9tLfKAfsNgftExBz2XjqPWvpcv4czPMWnRovlfV6I4K2NoUdJS1PlfxD/AMFYLJ/E+n22heEmTQzcot3e38v73ydwDsiL325IBr72h4ezVKU69X37OyW1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`;
      
      // Custom stylesheet with Bootstrap integration
      let stylesheet = `
      /* Custom styles on top of Bootstrap */
      .chart-container {
          position: relative;
          height: 250px;
          margin-bottom: 1rem;
      }
      .tooltip-wrapper {
          cursor: pointer;
          text-decoration: underline dotted;
      }
      .card-stats {
          transition: all 0.3s ease;
      }
      .card-stats:hover {
          transform: translateY(-5px);
          box-shadow: 0 5px 15px rgba(0,0,0,0.1);
      }
      .stats-icon {
          font-size: 2rem;
          opacity: 0.2;
      }
      /* Dark theme overrides */
      body.dark {
          background-color: #222;
          color: #eee;
      }
      body.dark .card {
          background-color: #333;
          border-color: #444;
      }
      body.dark .table {
          color: #eee;
      }
      body.dark .table-striped > tbody > tr:nth-of-type(odd) {
          background-color: rgba(255,255,255,0.05);
      }
      body.dark .modal-content {
          background-color: #333;
      }
      `;

      res.writeHead(200, {'Content-type':'text/html'});
      res.write(`
<!DOCTYPE html>
<html lang="en">
<head>
    <title>XNP v${PROXY_VERSION} Hashrate Monitor</title>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta name="mobile-web-app-capable" content="yes">
    <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.2.3/dist/css/bootstrap.min.css" rel="stylesheet">
    <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.2.1/css/all.min.css" rel="stylesheet">
    <link rel="icon" sizes="192x192" href="${icon}">
    <link rel="shortcut icon" href="${icon}">
    <style>${stylesheet}</style>
</head>
<body class="${global.config.theme}">
    <nav class="navbar navbar-expand-lg navbar-${global.config.theme} bg-${global.config.theme === 'light' ? 'light' : 'dark'}">
        <div class="container">
            <a class="navbar-brand" href="#">
                <img src="${icon}" alt="XNP Logo" width="30" height="30" class="d-inline-block align-top me-2">
                XNP v${PROXY_VERSION}
            </a>
            <button class="btn btn-sm ms-auto" onclick="toggleTheme()">
                <i id="themeIcon" class="fas ${global.config.theme === 'light' ? 'fa-moon' : 'fa-sun'}"></i>
            </button>
        </div>
    </nav>

    <div class="container py-4" id="content">
        <!-- Summary Stats -->
        <div class="row mb-4">
            <div class="col-md-4 mb-3">
                <div class="card card-stats h-100 border-success">
                    <div class="card-body">
                        <div class="d-flex justify-content-between">
                            <div>
                                <h5 class="card-title">Total Workers</h5>
                                <h2 class="display-6">${totalWorkers}</h2>
                            </div>
                            <div class="d-flex align-items-center">
                                <i class="fas fa-users stats-icon text-success"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
            <div class="col-md-4 mb-3">
                <div class="card card-stats h-100 border-primary">
                    <div class="card-body">
                        <div class="d-flex justify-content-between">
                            <div>
                                <h5 class="card-title">Total Hashrate</h5>
                                <h2 class="display-6">${totalHashrate}</h2>
                            </div>
                            <div class="d-flex align-items-center">
                                <i class="fas fa-tachometer-alt stats-icon text-primary"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
            <div class="col-md-4 mb-3">
                <div class="card card-stats h-100 border-info">
                    <div class="card-body">
                        <div class="d-flex justify-content-between">
                            <div>
                                <h5 class="card-title">Active Pools</h5>
                                <h2 class="display-6">${Object.keys(poolHashrate).length}</h2>
                            </div>
                            <div class="d-flex align-items-center">
                                <i class="fas fa-server stats-icon text-info"></i>
                            </div>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <!-- Charts Section -->
        <div class="row mb-4">
            <div class="col-md-6 mb-3">
                <div class="card h-100">
                    <div class="card-header">
                        <h5 class="card-title">Hashrate Distribution</h5>
                    </div>
                    <div class="card-body">
                        <div class="chart-container">
                            <canvas id="poolDistChart"></canvas>
                        </div>
                    </div>
                </div>
            </div>
            <div class="col-md-6 mb-3">
                <div class="card h-100">
                    <div class="card-header">
                        <h5 class="card-title">Pool Stats Overview</h5>
                    </div>
                    <div class="card-body">
                        <div class="chart-container">
                            <canvas id="workerStatusChart"></canvas>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <!-- Pool Cards -->
        <h4 class="mb-3">Pool Information</h4>
        <div class="row mb-4">
            ${poolCardsHtml}
        </div>

        <!-- Miners Table -->
        <div class="card mb-4">
            <div class="card-header d-flex justify-content-between align-items-center">
                <h5 class="mb-0">Miners</h5>
                <div class="input-group w-50">
                    <span class="input-group-text"><i class="fas fa-search"></i></span>
                    <input type="text" id="minerSearch" class="form-control" placeholder="Search miners...">
                </div>
            </div>
            <div class="card-body">
                <div class="table-responsive">
                    <table class="table table-striped table-hover" id="minersTable">
                        <thead>
                            <tr>
                                <th>Name</th>
                                <th>Hashrate</th>
                                <th>Difficulty</th>
                                <th>Shares</th>
                                <th>Hashes</th>
                                <th>Share Received</th>
                                <th>Ping Received</th>
                                <th>Connected</th>
                                <th>Pool</th>
                                <th>Agent</th>
                            </tr>
                        </thead>
                        <tbody>
                            ${tableBody}
                        </tbody>
                    </table>
                </div>
            </div>
        </div>
    </div>

    <!-- Footer -->
    <footer class="footer mt-auto py-3 bg-${global.config.theme === 'light' ? 'light' : 'dark'}">
        <div class="container text-center">
            <span class="text-muted">XMR Node Proxy v${PROXY_VERSION} | Auto-refresh: ${global.config.refreshTime}s</span>
        </div>
    </footer>
    
    <!-- Scripts -->
    <script src="https://cdn.jsdelivr.net/npm/jquery@3.6.0/dist/jquery.min.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/bootstrap@5.2.3/dist/js/bootstrap.bundle.min.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/chart.js@3.9.1/dist/chart.min.js"></script>

    <script>
        // Enable Bootstrap tooltips
        var tooltipTriggerList = [].slice.call(document.querySelectorAll('[data-bs-toggle="tooltip"]'))
        var tooltipList = tooltipTriggerList.map(function (tooltipTriggerEl) {
            return new bootstrap.Tooltip(tooltipTriggerEl)
        });
        
        // Theme toggle
        function toggleTheme() {
            const body = document.body;
            const icon = document.getElementById('themeIcon');
            if (body.classList.contains('light')) {
                body.classList.remove('light');
                body.classList.add('dark');
                icon.classList.remove('fa-moon');
                icon.classList.add('fa-sun');
            } else {
                body.classList.remove('dark');
                body.classList.add('light');
                icon.classList.remove('fa-sun');
                icon.classList.add('fa-moon');
            }
            localStorage.setItem('xnp-theme', body.classList.contains('light') ? 'light' : 'dark');
        }
        
        // Load saved theme from localStorage
        document.addEventListener('DOMContentLoaded', function() {
            const savedTheme = localStorage.getItem('xnp-theme');
            if (savedTheme && savedTheme !== document.body.classList[0]) {
                toggleTheme();
            }
        });
        
        // Table search functionality
        document.getElementById('minerSearch').addEventListener('keyup', function() {
            const value = this.value.toLowerCase();
            const table = document.getElementById('minersTable');
            const rows = table.getElementsByTagName('tr');
            
            for (let i = 1; i < rows.length; i++) {
                let found = false;
                const cells = rows[i].getElementsByTagName('td');
                
                for (let j = 0; j < cells.length; j++) {
                    if (cells[j].textContent.toLowerCase().indexOf(value) > -1) {
                        found = true;
                        break;
                    }
                }
                
                rows[i].style.display = found ? '' : 'none';
            }
        });
        
        // Chart JS Setup
        const poolData = ${JSON.stringify(poolData)};
        
        // Initialize charts function
        function initializeCharts() {
            // Pool distribution chart
            const poolCtx = document.getElementById('poolDistChart').getContext('2d');
            const poolLabels = poolData.map(pool => pool.name);
            const poolValues = poolData.map(pool => pool.hashrate);
            const poolColors = poolData.map((_, index) => {
                const colors = [
                    'rgba(54, 162, 235, 0.7)',
                    'rgba(255, 99, 132, 0.7)',
                    'rgba(255, 206, 86, 0.7)',
                    'rgba(75, 192, 192, 0.7)',
                    'rgba(153, 102, 255, 0.7)'
                ];
                return colors[index % colors.length];
            });
            
            if (window.poolChart) {
                window.poolChart.destroy();
            }
            
            window.poolChart = new Chart(poolCtx, {
                type: 'pie',
                data: {
                    labels: poolLabels,
                    datasets: [{
                        data: poolValues,
                        backgroundColor: poolColors,
                        borderWidth: 1
                    }]
                },
                options: {
                    responsive: true,
                    maintainAspectRatio: false,
                    plugins: {
                        legend: {
                            position: 'right',
                        }
                    }
                }
            });
            
            // Worker Status Chart
            const workerCtx = document.getElementById('workerStatusChart').getContext('2d');
            
            // Count online/offline miners
            const onlineMiners = ${onlineMinersCount};
            const offlineMiners = ${offlineMinersCount};
            
            if (!window.minerHistory) {
                window.minerHistory = {
                    time: [],
                    online: [],
                    offline: []
                };
            }
            
            const now = new Date();
            const timeLabel = now.getHours() + ':' + (now.getMinutes() < 10 ? '0' : '') + now.getMinutes();
            
            if (window.minerHistory.time.length >= 8) {
                window.minerHistory.time.shift();
                window.minerHistory.online.shift();
                window.minerHistory.offline.shift();
            }
            
            window.minerHistory.time.push(timeLabel);
            window.minerHistory.online.push(onlineMiners);
            window.minerHistory.offline.push(offlineMiners);
            
            if (window.workerChart) {
                window.workerChart.destroy();
            }
            
            window.workerChart = new Chart(workerCtx, {
                type: 'line',
                data: {
                    labels: window.minerHistory.time,
                    datasets: [
                        {
                            label: 'Online Miners',
                            data: window.minerHistory.online,
                            borderColor: 'rgba(40, 167, 69, 1)',
                            backgroundColor: 'rgba(40, 167, 69, 0.2)',
                            fill: true,
                            tension: 0.4,
                            pointRadius: 4,
                            pointHoverRadius: 6
                        },
                        {
                            label: 'Offline Miners',
                            data: window.minerHistory.offline,
                            borderColor: 'rgba(220, 53, 69, 1)',
                            backgroundColor: 'rgba(220, 53, 69, 0.2)',
                            fill: true,
                            tension: 0.4,
                            pointRadius: 4,
                            pointHoverRadius: 6
                        }
                    ]
                },
                options: {
                    responsive: true,
                    maintainAspectRatio: false,
                    scales: {
                        y: {
                            beginAtZero: true,
                            ticks: {
                                precision: 0
                            }
                        }
                    },
                    interaction: {
                        intersect: false,
                        mode: 'index'
                    },
                    plugins: {
                        tooltip: {
                            enabled: true
                        },
                        legend: {
                            position: 'top'
                        }
                    }
                }
            });
        }
        
        // Initialize charts on page load
        initializeCharts();
        
        // Auto refresh with fade effect
        window.setInterval(function(){
            $("#content").fadeOut(500, function() {
                $(this).load("/ #content", function() {
                    $(this).fadeIn(500);
                    
                    // Reinitialize tooltips after refresh
                    var tooltipTriggerList = [].slice.call(document.querySelectorAll('[data-bs-toggle="tooltip"]'))
                    tooltipList = tooltipTriggerList.map(function (tooltipTriggerEl) {
                        return new bootstrap.Tooltip(tooltipTriggerEl)
                    });
                    
                    // Reinitialize charts after content refresh
                    initializeCharts();
                });
            });
        }, ${global.config.refreshTime} * 1000);
    </script>
</body>
</html>
`);
			res.end();
		} else if(req.url.substring(0, 5) == "/json") {
			res.writeHead(200, {'Content-type':'application/json'});
			res.write(JSON.stringify(activeWorkers) + "\r\n");
			res.end();
		} else {
			res.writeHead(404);
			res.end();
		}
	});

	jsonServer.listen(global.config.httpPort || "8081", global.config.httpAddress || "localhost")
}

function activatePorts() {
    /*
     Reads the current open ports, and then activates any that aren't active yet
     { "port": 80, "ssl": false, "diff": 5000 }
     and binds a listener to it.
     */
    async.each(global.config.listeningPorts, function (portData) {
        if (activePorts.indexOf(portData.port) !== -1) {
            return;
        }
        let handleMessage = function (socket, jsonData, pushMessage) {
            if (!jsonData.id) {
                console.warn(global.threadName + 'Miner RPC request missing RPC id');
                return;
            }
            else if (!jsonData.method) {
                console.warn(global.threadName + 'Miner RPC request missing RPC method');
                return;
            }

            let sendReply = function (error, result) {
                if (!socket.writable) return;
                let reply = {
                    jsonrpc: "2.0",
                    id:      jsonData.id,
                    error:   error ? {code: -1, message: error} : null,
                    result:  result
                };
                if (jsonData.id === "Stratum") reply.method = jsonData.method;
                socket.write(JSON.stringify(reply) + "\n");
            };
            let sendReplyFinal = function (error) {
                setTimeout(function() {
                  if (!socket.writable) return;
                  let reply = {
                    jsonrpc: "2.0",
                    id:      jsonData.id,
                    error:   {code: -1, message: error},
                    result:  null
                  };
                  if (jsonData.id === "Stratum") reply.method = jsonData.method;
                  socket.end(JSON.stringify(reply) + "\n");
                }, 9 * 1000);
            };

            handleMinerData(socket, jsonData.id, jsonData.method, jsonData.params, socket.remoteAddress, portData, sendReply, sendReplyFinal, pushMessage);
        };

        function socketConn(socket) {
            socket.setKeepAlive(true);
            socket.setEncoding('utf8');

            let dataBuffer = '';

            let pushMessage = function (body) {
                if (!socket.writable) return;
                body.jsonrpc = "2.0";
                debug.miners(`Data sent to miner (pushMessage): ` + JSON.stringify(body));
                socket.write(JSON.stringify(body) + "\n");
            };

            socket.on('data', function (d) {
                dataBuffer += d;
                if (Buffer.byteLength(dataBuffer, 'utf8') > 102400) { //10KB
                    dataBuffer = null;
                    console.warn(global.threadName + 'Excessive packet size from: ' + socket.remoteAddress);
                    socket.destroy();
                    return;
                }
                if (dataBuffer.indexOf('\n') !== -1) {
                    let messages = dataBuffer.split('\n');
                    let incomplete = dataBuffer.slice(-1) === '\n' ? '' : messages.pop();
                    for (let i = 0; i < messages.length; i++) {
                        let message = messages[i];
                        if (message.trim() === '') {
                            continue;
                        }
                        let jsonData;
                        debug.miners(`Data from miner: ${message}`);
                        try {
                            jsonData = JSON.parse(message);
                        }
                        catch (e) {
                            if (message.indexOf('GET /') === 0) {
                                if (message.indexOf('HTTP/1.1') !== -1) {
                                    socket.end('HTTP/1.1' + httpResponse);
                                    break;
                                }
                                else if (message.indexOf('HTTP/1.0') !== -1) {
                                    socket.end('HTTP/1.0' + httpResponse);
                                    break;
                                }
                            }
                            console.warn(global.threadName + "Malformed message from " + socket.remoteAddress + " Message: " + message);
                            socket.destroy();
                            break;
                        }
                        handleMessage(socket, jsonData, pushMessage);
                    }
                    dataBuffer = incomplete;
                }
            }).on('error', function (err) {
                if (err.code !== 'ECONNRESET') {
                    console.warn(global.threadName + "Miner socket error from " + socket.remoteAddress + ": " + err);
                }
                socket.end();
                socket.destroy();
            }).on('close', function () {
                pushMessage = function () {};
                debug.miners('Miner disconnected via standard close');
                socket.end();
                socket.destroy();
            });
        }

        if ('ssl' in portData && portData.ssl === true) {
            let server = tls.createServer({
                key: fs.readFileSync('cert.key'),
                cert: fs.readFileSync('cert.pem')
            }, socketConn);
	    server.listen(portData.port, global.config.bindAddress, function (error) {
                if (error) {
                    console.error(global.threadName + "Unable to start server on: " + portData.port + " Message: " + error);
                    return;
                }
                activePorts.push(portData.port);
                console.log(global.threadName + "Started server on port: " + portData.port);
            });
            server.on('error', function (error) {
                console.error(global.threadName + "Can't bind server to " + portData.port + " SSL port!");
            });
        } else {
            let server = net.createServer(socketConn);
	    server.listen(portData.port, global.config.bindAddress, function (error) {
                if (error) {
                    console.error(global.threadName + "Unable to start server on: " + portData.port + " Message: " + error);
                    return;
                }
                activePorts.push(portData.port);
                console.log(global.threadName + "Started server on port: " + portData.port);
            });
            server.on('error', function (error) {
                console.error(global.threadName + "Can't bind server to " + portData.port + " port!");
            });
        }
    });
}

function checkActivePools() {
    for (let badPool in activePools){
        if (activePools.hasOwnProperty(badPool) && !activePools[badPool].active) {
            for (let pool in activePools) {
                if (activePools.hasOwnProperty(pool) && !activePools[pool].devPool && activePools[pool].coin === activePools[badPool].coin && activePools[pool].active) {
                    for (let miner in activeMiners) {
                        if (activeMiners.hasOwnProperty(miner)) {
                            let realMiner = activeMiners[miner];
                            if (realMiner.pool === badPool) {
                                realMiner.pool = pool;
                                realMiner.pushNewJob();
                            }
                        }
                    }
                    break;
                }
            }
        }
    }
}

// API Calls

// System Init

if (cluster.isMaster) {
    console.log("Xmr-Node-Proxy (XNP) v" + PROXY_VERSION);
    let numWorkers;
    try {
        let argv = require('minimist')(process.argv.slice(2));
        if (typeof argv.workers !== 'undefined') {
            numWorkers = Number(argv.workers);
        } else {
            numWorkers = require('os').cpus().length;
        }
    } catch (err) {
        console.error(`${global.threadName}Unable to set the number of workers via arguments.  Make sure to run npm install!`);
        numWorkers = require('os').cpus().length;
    }
    global.threadName = '[MASTER] ';
    console.log('Cluster master setting up ' + numWorkers + ' workers...');
    cluster.on('message', masterMessageHandler);
    for (let i = 0; i < numWorkers; i++) {
        let worker = cluster.fork();
        worker.on('message', slaveMessageHandler);
    }

    cluster.on('online', function (worker) {
        console.log('Worker ' + worker.process.pid + ' is online');
        activeWorkers[worker.id] = {};
    });

    cluster.on('exit', function (worker, code, signal) {
        console.error('Worker ' + worker.process.pid + ' died with code: ' + code + ', and signal: ' + signal);
        console.log('Starting a new worker');
        worker = cluster.fork();
        worker.on('message', slaveMessageHandler);
    });
    connectPools();
    setInterval(enumerateWorkerStats, 15*1000);
    setInterval(balanceWorkers, 90*1000);
    if (global.config.httpEnable) {
        console.log("Activating Web API server on " + (global.config.httpAddress || "localhost") + ":" + (global.config.httpPort || "8081"));
        activateHTTP();
    }
} else {
    /*
    setInterval(checkAliveMiners, 30000);
    setInterval(retargetMiners, global.config.pool.retargetTime * 1000);
    */
    process.on('message', slaveMessageHandler);
    global.config.pools.forEach(function(poolData){
        if (!poolData.coin) poolData.coin = "xmr";
        activePools[poolData.hostname] = new Pool(poolData);
        if (poolData.default){
            defaultPools[poolData.coin] = poolData.hostname;
        }
        if (!activePools.hasOwnProperty(activePools[poolData.hostname].coinFuncs.devPool.hostname)){
            activePools[activePools[poolData.hostname].coinFuncs.devPool.hostname] = new Pool(activePools[poolData.hostname].coinFuncs.devPool);
        }
    });
    process.send({type: 'needPoolState'});
    setInterval(function(){
        for (let minerID in activeMiners){
            if (activeMiners.hasOwnProperty(minerID)){
                activeMiners[minerID].updateDifficulty();
            }
        }
    }, 45000);
    setInterval(function(){
        for (let minerID in activeMiners){
            if (activeMiners.hasOwnProperty(minerID)){
                process.send({minerID: minerID, data: activeMiners[minerID].minerStats(), type: 'workerStats'});
            }
        }
    }, 10000);
    setInterval(checkActivePools, 90000);
    activatePorts();
}