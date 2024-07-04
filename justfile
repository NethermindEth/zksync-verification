image := "crypt"
project_dir := "/home/easy/project"

build:
    @echo "Building the {{image}}."
    docker build -t {{image}} .

xhost-docker:
    xhost +local:docker

bash: build xhost-docker
    docker run -h {{image}} -e DISPLAY=$DISPLAY \
        --net=host \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f ./src),target={{project_dir}} \
        --mount type=bind,source=$(readlink -f ./script),target=/tmp/script \
        -it {{image}} \
        -c "cd /tmp/script; bash entrypoint.sh bash"

emacs: build xhost-docker
    docker run -h {{image}} -e DISPLAY=$DISPLAY \
        --net=host \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f ./src),target={{project_dir}} \
        --mount type=bind,source=$(readlink -f ./script),target=/tmp/script \
        -it {{image}} \
        -c "cd /tmp/script; bash entrypoint.sh emacs-gtk"

test: build xhost-docker
    docker run -h {{image}} -e DISPLAY=$DISPLAY \
        --net=host \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f ./src),target={{project_dir}} \
        --mount type=bind,source=$(readlink -f ./script),target=/tmp/script \
        -it {{image}} \
        -c "cd /tmp/script; bash test.sh"
