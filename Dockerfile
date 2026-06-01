FROM ubuntu:26.04 AS builder

ENV DEBIAN_FRONTEND=noninteractive

RUN apt update && apt install -y --no-install-recommends pkg-config bison libfl-dev flex clang \
    build-essential python3 curl file cmake git procps ca-certificates libffi-dev zlib1g-dev \
    && apt autoclean && apt clean && apt -y autoremove \
    && rm -rf /var/lib/apt/lists/*

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --profile minimal
ENV PATH="/root/.cargo/bin:${PATH}"

WORKDIR /root
RUN git clone --recursive https://github.com/gipsyh/yosys
RUN cd yosys && make config-gcc \
    && printf 'ENABLE_ABC := 0\nENABLE_READLINE := 0\nENABLE_TCL := 0\n' >> Makefile.conf \
    && make -j28 && make install

WORKDIR /root/
RUN git clone --recursive https://github.com/gipsyh/yosys-slang
RUN cd yosys-slang && make install -j28

WORKDIR /root/
COPY . .
RUN git submodule update --init && cargo install --path . && cargo clean

FROM ubuntu:26.04

RUN apt update && apt install -y libffi8 && apt autoclean && apt clean && apt -y autoremove

COPY --from=builder /root/.cargo/bin/ric3 /usr/local/bin/ric3
COPY --from=builder /usr/local /usr/local/

WORKDIR /root/
ENTRYPOINT ["ric3"]
