#!/bin/bash -i

## Place to install TLC, TLAPS, Apalache, ...
mkdir -p tools

## PATH below has two locations because of inconsistencies between Gitpod and Codespaces.
## Gitpod:     /workspace/...
## Codespaces: /workspaces/...

## Install TLA+ Tools (download from github instead of nightly.tlapl.us (inria) to only rely on github)
wget -qN https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -P tools/
echo "alias tlcrepl='java -cp /workspace/ewd998/tools/tla2tools.jar:/workspaces/ewd998/tools/tla2tools.jar tlc2.REPL'" >> $HOME/.bashrc
echo "alias tlc='java -cp /workspace/ewd998/tools/tla2tools.jar:/workspaces/ewd998/tools/tla2tools.jar tlc2.TLC'" >> $HOME/.bashrc

## Install TLAPS (proof system)
wget -N https://github.com/tlaplus/tlapm/releases/download/v1.4.5/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -P /tmp
chmod +x /tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin
/tmp/tlaps-1.4.5-x86_64-linux-gnu-inst.bin -d tools/tlaps
echo 'export PATH=$PATH:/workspace/ewd998/tools/tlaps/bin:/workspaces/ewd998/tools/tlaps/bin' >> $HOME/.bashrc

## Install Apalache
wget -qN https://github.com/informalsystems/apalache/releases/latest/download/apalache.tgz -P /tmp
mkdir -p tools/apalache
tar xvfz /tmp/apalache.tgz --directory tools/apalache/
echo 'export PATH=$PATH:/workspace/ewd998/tools/apalache/bin:/workspaces/ewd998/tools/apalache/bin' >> $HOME/.bashrc
tools/apalache/bin/apalache-mc config --enable-stats=true

## Install Apache Ant that builds CommunityModules (see build.xml)
sudo apt-get install -y ant

## Do initial build
ant -f build.xml