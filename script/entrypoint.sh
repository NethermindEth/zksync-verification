#!/bin/bash

echo -e "(setq warning-minimum-level :emergency)\n" > ~/.emacs
cat $1 >> ~/.emacs
cd ~/project
bash --login -c $2