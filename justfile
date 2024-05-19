image := "crypt"
project_dir := "/home/easy/project"

build:
    @echo "Building the {{image}}."
    docker build -t {{image}} .

bash PROJECT: build 
    @echo "Entering the {{image}}."
    @docker run -h {{image}} -e DISPLAY=$DISPLAY \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f {{PROJECT}}),target={{project_dir}} \
        -it {{image}}  

xhost-docker: 
    xhost +local:docker

gui PROJECT: build xhost-docker
    docker run -h {{image}} -e DISPLAY=$DISPLAY \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f {{PROJECT}}),target={{project_dir}} \
        -it {{image}} \
        -c "cd /project; emacs-gtk"

zk-code PROJECT: build xhost-docker
    docker run -h {{image}} -e DISPLAY=$DISPLAY \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f {{PROJECT}}),target={{project_dir}} \
        --mount type=bind,source=$(readlink -f ./script),target=/tmp/script \
        -it {{image}} \
        -c "cd /tmp/script; bash entrypoint.sh ./emacs/easycrypt-zk-code"