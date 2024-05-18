FROM ubuntu:latest
ENV EASYCRYPT_REVISION 577c882
ENV JASMIN_VERSION 2022.09.3
ENV BIGNUM_REVISION e5c3a1e
ENV EASYCRYPT_ZK_REVISION 6d35e43
ENV Z3_VERSION 4.8.7
ENV ALT_ERGO_VERSION 2.4.2
ENV WHY3_VERSION 1.4.1
RUN apt-get update
RUN apt install -y sudo opam cvc4 pkg-config libgmp-dev libpcre3-dev zlib1g-dev libmpfr-dev libppl-dev autoconf python3-pip
RUN apt install -y emacs
RUN useradd -ms /bin/bash easy
RUN echo "easy:lamport" | chpasswd
RUN usermod -aG sudo easy
USER easy
RUN pip install z3-solver==${Z3_VERSION} --break-system-packages
RUN opam init --disable-sandboxing
RUN opam update
RUN opam pin -y alt-ergo ${ALT_ERGO_VERSION}
RUN opam pin -y why3 ${WHY3_VERSION}
RUN opam pin add -y easycrypt https://github.com/EasyCrypt/easycrypt.git#${EASYCRYPT_REVISION} --update-invariant
RUN opam install -y easycrypt jasmin.${JASMIN_VERSION} --update-invariant
RUN opam install -y alt-ergo
RUN opam install -y why3
RUN echo $(opam env) > ~/.bashrc
RUN echo "export PATH=\$PATH:~/.local/bin/;" >> ~/.bashrc
SHELL ["/bin/bash", "--login" , "-c"]
RUN why3 config detect
RUN git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG && cd ~/.emacs.d/lisp/PG && make
RUN echo "(load \"~/.emacs.d/lisp/PG/generic/proof-site\")" > ~/.emacs
RUN echo "(setq proof-splash-enable nil)" >> ~/.emacs
ENTRYPOINT [ "bash" ]