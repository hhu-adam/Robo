FROM ubuntu:22.04

WORKDIR /

RUN apt-get update && apt-get install -y git curl libatomic1

# Install elan
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz\
  && ./elan-init -y --default-toolchain none
ENV PATH="${PATH}:/root/.elan/bin"

# Copy the game to `game`
COPY . ./game

RUN cd /game && lake update && lake clean && lake exe cache get &&\
    cd /game/lake-packages/GameServer/server/ && lake clean && lake build &&\
    cd /game && lake build && rm -rf /root/.cache

WORKDIR /game/lake-packages/GameServer/server/build/bin/

CMD ./gameserver --server /game/ Game Game
