FROM ubuntu:jammy

USER root

# install command-line utilities
RUN apt-get update && apt-get install sudo git curl git bash-completion python3 -y && apt-get clean

# install elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# install whichever toolchain mathlib is currently using
RUN . ~/.profile && elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain)

# path to elan 
ENV PATH="$HOME/.elan/bin:${PATH}"

# update elan
RUN elan self update
