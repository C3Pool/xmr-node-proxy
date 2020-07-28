# xmr-node-proxy

Supports all known cryptonight/heavy/light/pico coins:

* Monero (XMR), MoneroV (XMV), Monero Original (XMO), Monero Classic (XMC), ...
* Wownero (WOW), Masari (MSR), Electroneum (ETN), Graft (GRFT), Intense (ITNS)
* Stellite (XTL)
* Aeon (AEON), Turtlecoin (TRTL), IPBC/BitTube (TUBE)
* Sumokoin (SUMO), Haven (XHV), Loki (LOKI)
* ...

## Setup Instructions

Based on a clean Ubuntu 16.04 LTS minimal install

## Switching from other xmr-node-proxy repository

```bash
cd xmr-node-proxy
git remote set-url origin https://github.com/C3Pool/xmr-node-proxy.git && git pull -X theirs --no-edit && npm update
```

## Deployment via Installer on Linux

1. Create a user 'nodeproxy' and assign a password (or add an SSH key. If you prefer that, you should already know how to do it)

```bash
useradd -d /home/nodeproxy -m -s /bin/bash nodeproxy
passwd nodeproxy
```

2. Add your user to `/etc/sudoers`, this must be done so the script can sudo up and do it's job.  We suggest passwordless sudo.  Suggested line: `<USER> ALL=(ALL) NOPASSWD:ALL`.  Our sample builds use: `nodeproxy ALL=(ALL) NOPASSWD:ALL`

```bash
echo "nodeproxy ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers
```

3. Log in as the **NON-ROOT USER** you just created and run the [deploy script](https://raw.githubusercontent.com/C3Pool/xmr-node-proxy/master/install.sh).  This is very important!  This script will install the proxy to whatever user it's running under!

```bash
curl -L https://raw.githubusercontent.com/C3Pool/xmr-node-proxy/master/install.sh | bash
```

3. Once it's complete, copy `config_example.json` to `config.json` and edit as desired.
4. Run: `source ~/.bashrc`  This will activate NVM and get things working for the following pm2 steps.
8. Once you're happy with the settings, go ahead and start all the proxy daemon, commands follow.

```shell
cd ~/xmr-node-proxy/
pm2 start proxy.js --name=proxy --log-date-format="YYYY-MM-DD HH:mm:ss:SSS Z"
pm2 save
```
You can check the status of your proxy by either issuing

```
pm2 logs proxy
```

or using the pm2 monitor

```
pm2 monit
```

## Updating xmr-node-proxy

```bash
cd xmr-node-proxy
./update.sh
```

## Deployment via Docker on Windows 10 with the Fall Creators Update (or newer)

1. Install and run [Docker for Windows](https://docs.docker.com/docker-for-windows/install/) with Linux containers mode.

2. Get xmr-node-proxy sources by downloading and unpacking the latest [xmr-node-proxy](https://github.com/C3Pool/xmr-node-proxy/archive/master.zip)
archive to xmr-node-proxy-master directory.

3. Got to xmr-node-proxy-master directory in Windows "Command Prompt" and build xmr-node-proxy Docker image:

```
docker build . -t xmr-node-proxy
```

4. Copy config_example.json to config.json and edit config.json file as desired (do not forget to update default XMR wallet).

5. Create xnp Docker contained based on xmr-node-proxy image (make sure to update port numbers if you changed them in config.json):

```
docker create -p 3333:3333 -p 8080:8080 -p 8443:8443 --name xnp xmr-node-proxy
```

6. Copy your modified config.json to xnp Docker container:

```
docker cp config.json xnp:/xmr-node-proxy
```

7. Run xnp Docker container (or attach to already running one):

```
docker start --attach xnp
```

8. Stop xnp Docker container (to start it again with update):

```
docker stop xnp
```

9. Delete xnp Docker container (if you want to create it again with different ports):

```
docker rm xnp
```

10. Delete xmr-node-proxy Docker image (if you no longer need proxy):

```
docker rmi xmr-node-proxy
```


## Configuration BKMs

1. Specify at least one main pool with non zero share and "default: true". Sum of all non zero pool shares should be equal to 100 (percent).

2. There should be one pool with "default: true" (the last one will override previous ones with "default: true"). Default pool means pool that is used 
for all initial miner connections via proxy.

3. You can use pools with zero share as backup pools. They will be only used if all non zero share pools became down.

4. You should select pool port with difficulty that is close to hashrate of all of your miners multiplied by 10.

5. Proxy ports should have difficulty close to your individual miner hashrate multiplied by 10.

6. Algorithm names ("algo" option in pool config section) can be taken from [Algorithm names and variants](https://github.com/xmrig/xmrig-proxy/blob/dev/doc/STRATUM_EXT.md#14-algorithm-names-and-variants) table

7. Blob type ("blob_type" option in pool config section) can be as follows

	* cryptonote  - Monero forks like Sumokoin, Electroneum, Graft, Aeon, Intense

	* cryptonote2 - Masari

	* forknote    - Some old Bytecoin forks (do not even know which one)

	* forknote2   - Bytecoin forks like Turtlecoin, IPBC

## Known Issues

VMs with 512Mb or less RAM will need some swap space in order to compile the C extensions for node.
Bignum and the CN libraries can chew through some serious memory during compile.
In regards to this here is guide for T2.Micro servers: [Setup of xmr-node-proxy on free tier AWS t2.micro instance](http://C3Pool.blogspot.com/2017/10/setup-of-xmr-node-proxy-on-free-tier.html).
There is also more generic proxy instalation guide: [Complete guide to install and configure xmr-node-proxy on a Ubuntu 16.04 VPS](https://tjosm.com/7689/install-xmr-node-proxy-vps/)

If not running on an Ubuntu 16.04 system, please make sure your kernel is at least 3.2 or higher, as older versions will not work for this.

Many smaller VMs come with ulimits set very low. We suggest looking into setting the ulimit higher. In particular, `nofile` (Number of files open) needs to be raised for high-usage instances.

In your `packages.json`, do a `npm install`, and it should pass.


## Performance

The proxy gains a massive boost over a basic pool by accepting that the majority of the hashes submitted _will_ not be valid (does not exceed the required difficulty of the pool).  Due to this, the proxy doesn't bother with attempting to validate the hash state nor value until the share difficulty exceeds the pool difficulty.

In testing, we've seen AWS t2.micro instances take upwards of 2k connections, while t2.small taking 6k.  The proxy is extremely light weight, and while there are more features on the way, it's our goal to keep the proxy as light weight as possible.

## Configuration Guidelines

Please check the [wiki](https://github.com/C3Pool/xmr-node-proxy/wiki/config_review) for information on configuration

Developer Donations
===================
If you'd like to make a one time donation, the addresses are as follows:
* XMR - ```43987ATFjfFXp9yBojQoifVPK4CerTF7Zaoo4eDY2p6AEp5uewT3PsY7hYHEHvbRivKcexmSaDdXscnnNtveV56pJpCa9uV```
* BTC - ```3Q4QT5WKMzCh4WqsGF2nKxc8XoLuLLuMqk```

## Known Working Pools

* [XMRPool.net](https://xmrpool.net)
* [supportXMR.com](https://supportxmr.com)
* [pool.xmr.pt](https://pool.xmr.pt)
* [minemonero.pro](https://minemonero.pro)
* [XMRPool.xyz](https://xmrpool.xyz)
* [ViaXMR.com](https://viaxmr.com)
* [mine.MoneroPRO.com](https://mine.moneropro.com)
* [MinerCircle.com](https://www.minercircle.com)
* [xmr.p00ls.net](https://www.p00ls.net)
* [MoriaXMR.com](https://moriaxmr.com)
* [MoneroOcean.stream](https://MoneroOcean.stream)
* [SECUmine.net](https://secumine.net)
* [Chinaenter.cn](http://xmr.chinaenter.cn)
* [XMRPool.eu](https://xmrpool.eu)

If you'd like to have your pool added, please make a pull request here, or contact C3Pool at support@C3Pool.com!
