#!/bin/bash

cp $1 ~/.emacs
cd ~/project
bash --login -c emacs-gtk