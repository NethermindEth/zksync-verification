# zksync-verification

Installation
-------------


0. Make sure you have ```cargo``` and ```docker``` installed at your machine. 

1. Install ```just``` by running
```bash
cargo install just
```
2. Install  ```x11-xserver-utils``` if you want to use the GUI emacs by
```bash
sudo apt install x11-xserver-utils
```

Running
---------
Just run the command 
```bash
just bash PROJECT_DIR_TO_MOUNT
```
to run the container mount the directory ```PROJECT_DIR_TO_MOUNT``` and 
enter the container. No X11 is needed.

Just run the command 
```bash
just gui PROJECT_DIR_TO_MOUNT
```
to mount the directory ```PROJECT_DIR_TO_MOUNT``` to the container and run emacs-gtk on it.

Run 
```
just zk-code-shell DIRECTORY_OF_EASYCRYPT_ZK_CODE
```
to mount the easycrypt-zk-code by @dfirsov and land in bash.

Run 
```
just zk-code-emacs DIRECTORY_OF_EASYCRYPT_ZK_CODE
```
to mount the easycrypt-zk-code by @dfirsov and land in emacs.