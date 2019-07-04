# Dockerfile for Seahorn

# OS image
FROM ubuntu:14.04

MAINTAINER Temesghen Kahsai <lememta@gmail.com>

ENV SEAHORN=/home/SynthHorn/build/run/bin
ENV PATH="/home/SynthHorn/build/run/bin:/home/SynthHorn:$PATH"


# Install
RUN \
  sudo apt-get update -qq && \
  sudo apt-get upgrade -qq && \
  sudo apt-get install bridge-utils && \
  apt-get install -qq build-essential clang-3.6 && \
  apt-get install -qq software-properties-common && \
  apt-get install -qq curl git ninja-build man subversion vim wget cmake && \
  apt-get install -qq libboost-program-options-dev && \
  apt-get install python2.7 python2.7-dev -y && \
  apt-get install -y libboost1.55-all-dev && \
  apt-get install --yes libgmp-dev && \
  apt-get install --yes python-pip && \
  apt-get install --yes cmake

RUN \
  export LZ="/home/" && \
  mkdir -p $LZ && \
  wget --output-document=llvm-z3.tar.gz https://www.dropbox.com/s/cipjz38k3boyd1v/llvm-3.6-z3.tar.gz?dl=1 && \
  tar xvf llvm-z3.tar.gz -C $LZ && \
  ls $LZ && \
  sudo pip install lit && \
  sudo pip install OutputCheck

RUN \
  git clone https://github.com/lijiaying/SynthHorn && \
  cd SynthHorn && \
  mkdir -p build && \
  cd build && \
	cmake -DCMAKE_INSTALL_PREFIX=run ../ && \
	cmake --build . && \
	cmake --build . --target extra && \
	cd ../llvm-seahorn/ && git reset --hard 39aa187 && cd ../llvm-dsa/ && git reset --hard fedb3e3 && cd ../sea-dsa/ && git reset --hard 246f0f5 && cd ../crab-llvm/ && git reset --hard e2fac87 && cd ../build/ && make .. && \
	cmake --build . --target crab && cmake .. && \
	cmake --build . --target install

RUN \
	cd $LZ && \
	cd SynthHorn && \
	cd libsvm && \
	make clean && \
	make

RUN \
	cd $LZ && \
	cd SynthHorn && \
	cd C50 && \
	make clean && \
	make

