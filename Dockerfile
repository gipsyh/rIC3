FROM ubuntu:24.04 AS builder
RUN apt update
RUN apt install -y curl build-essential git cmake zlib1g-dev pkg-config libssl-dev libmpfr-dev meson clang && apt-get clean
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly
ENV PATH="/root/.cargo/bin:${PATH}"
WORKDIR /root/rIC3
COPY . .
RUN git submodule update --init
RUN cargo clean && cargo build --release

FROM ghcr.io/gipsyh/yosys:latest AS yosys

FROM ubuntu:24.04
RUN apt update
RUN apt install -y libmpfr6 libgmp10 tcl libreadline-dev
RUN apt autoclean && apt clean && apt -y autoremove
RUN rm -rf /var/lib/apt/lists
COPY --from=builder /root/rIC3/target/release/ric3 /usr/local/bin/
COPY --from=yosys /usr/local/bin/yosys* /usr/local/bin/
ENTRYPOINT ["ric3"]
