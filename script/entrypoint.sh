#!/bin/bash

echo -e "(setq warning-minimum-level :emergency)\n" > ~/.emacs
cat $1 >> ~/.emacs
cd ~/project
echo "lamport" | sudo -k -S chmod -R a+rw .
bash --login -c $2
