image := "crypt"

build:
    @echo "Building the {{image}}."
    docker build -t {{image}} .

bash PROJECT: build 
    @echo "Entering the {{image}}."
    @docker run -h {{image}} -e DISPLAY=$DISPLAY \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f {{PROJECT}}),target=/project \
        -it {{image}}  

gui PROJECT: build
    docker run -h {{image}} -e DISPLAY=$DISPLAY \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f {{PROJECT}}),target=/project \
        -it {{image}} \
        -c "cd /project; emacs-gtk"

zk-code PROJECT: build
    docker run -h {{image}} -e DISPLAY=$DISPLAY \
        -v /tmp/.X11-unix:/tmp/.X11-unix \
        --env="QT_X11_NO_MITSHM=1" \
        --mount type=bind,source=$(readlink -f {{PROJECT}}),target=/project \
        -it {{image}} \
        -c "cd /project/; bash"