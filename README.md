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
just bash
```
to run the container mount the directory ```src/``` and 
enter the container. No X11 is needed.

Just run the command 
```bash
just emacs
```
to mount the directory ```src/``` to the container and run emacs-gtk on it.