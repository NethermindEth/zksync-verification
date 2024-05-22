#!/bin/bash

cp $1 ~/.emacs
cd ~/project
echo "lamport" | sudo -k -S chmod -R a+rw .
bash --login -c $2
