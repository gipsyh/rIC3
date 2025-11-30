FROM ubuntu:latest AS builder
RUN apt update && apt install -y curl build-essential git cmake zlib1g-dev pkg-config libssl-dev libmpfr-dev meson && apt-get clean
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly
ENV PATH="/root/.cargo/bin:${PATH}"
WORKDIR /root/rIC3
COPY . .
RUN git submodule update --init
RUN cargo build --release

FROM ubuntu:latest
COPY --from=builder /root/rIC3/target/release/rIC3 /usr/local/bin/
ENTRYPOINT ["rIC3"]
