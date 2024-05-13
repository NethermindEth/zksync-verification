FROM ubuntu:latest
ENV EASYCRYPT_REVISION 860dc3f
ENV JASMIN_VERSION 2022.09.3
ENV BIGNUM_REVISION e5c3a1e
ENV EASYCRYPT_ZK_REVISION 6d35e43
ENV Z3_VERSION 4.12
ENV ALT_ERGO_VERSION 2.4.0
RUN apt-get update
RUN apt install -y opam cvc4 pkg-config libgmp-dev libpcre3-dev zlib1g-dev libmpfr-dev libppl-dev autoconf python3-pip
RUN pip install z3-solver==${Z3_VERSION} --break-system-packages
RUN opam init --disable-sandboxing
RUN opam update
RUN opam pin add -y easycrypt https://github.com/EasyCrypt/easycrypt.git#${EASYCRYPT_REVISION} --update-invariant
RUN opam install -y easycrypt jasmin.${JASMIN_VERSION} --update-invariant
RUN opam install -y alt-ergo.${ALT_ERGO_VERSION}
RUN opam install -y why3
RUN echo $(opam env) > ~/.bashrc
SHELL ["/bin/bash", "--login" , "-c"]
RUN why3 config detect
RUN apt install -y emacs
RUN git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG && cd ~/.emacs.d/lisp/PG && make
RUN echo "(load \"~/.emacs.d/lisp/PG/generic/proof-site\")" > ~/.emacs
ENTRYPOINT [ "bash" ]