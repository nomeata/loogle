FROM ubuntu:24.04

ARG LEAN_VERSION=""

ENV DEBIAN_FRONTEND=noninteractive \
    LOOGLE_HOST=0.0.0.0 \
    LOOGLE_PORT=8088 \
    PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl \
        git \
        ca-certificates \
        build-essential \
        python3 \
        python3-prometheus-client \
    && rm -rf /var/lib/apt/lists/*

RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none --no-modify-path

WORKDIR /loogle

COPY . .

RUN if [ -n "$LEAN_VERSION" ]; then \
        echo "leanprover/lean4:$LEAN_VERSION" > lean-toolchain && \
        sed -i "s|mathlib4\" @ \"master\"|mathlib4\" @ \"$LEAN_VERSION\"|" lakefile.lean && \
        rm -f lake-manifest.json && \
        lake update ; \
    fi
RUN lean --version

RUN lake exe cache get
RUN lake build

EXPOSE 8088

CMD ["python3", "server.py"]
