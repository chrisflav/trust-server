# Build and run a trust node.
#
# Two stages, because the toolchain that compiles Lean is 2 GB and a node that
# holds people's public keys and their assertions should carry as little as
# possible.  What ships is the binary, the Lean runtime libraries it links, and
# the two subprocesses it shells out to: `gpg`, which checks every signature,
# and `curl`, which is how it reaches other nodes since Lean has no TLS.

FROM debian:bookworm-slim AS build

RUN apt-get update && apt-get install -y --no-install-recommends \
      curl ca-certificates git build-essential \
    && rm -rf /var/lib/apt/lists/*

# elan rather than a Lean image: there is no official one for a plain toolchain,
# and `lean-toolchain` is the single place that says which version this is.
ENV ELAN_HOME=/opt/elan
ENV PATH=$ELAN_HOME/bin:$PATH
RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain none \
    && rm /tmp/elan-init.sh

WORKDIR /src
COPY lean-toolchain ./
RUN elan toolchain install "$(cat lean-toolchain)" && elan default "$(cat lean-toolchain)"

# The manifest before the source, so that a change to the code does not refetch
# `aftk`, `semantic_hash` and the rest.
COPY lakefile.toml lake-manifest.json ./
RUN lake update --keep-toolchain || true

COPY . .
RUN lake build trust-server

# Collect what the binary actually needs, rather than the whole toolchain.
RUN mkdir -p /out/lib \
    && cp .lake/build/bin/trust-server /out/ \
    && TC="$(elan which lean | sed 's|/bin/lean$||')" \
    && cp -a "$TC"/lib/lean/*.so* /out/lib/ \
    && cp -a "$TC"/lib/libgcc_s.so* "$TC"/lib/libatomic.so* /out/lib/ 2>/dev/null || true

FROM debian:bookworm-slim AS runtime

# gpg checks every signature this node believes; curl is how it reaches peers,
# since Lean has no TLS of its own.  Both are load-bearing, not conveniences.
RUN apt-get update && apt-get install -y --no-install-recommends \
      gnupg curl ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=build /out/trust-server /usr/local/bin/trust-server
COPY --from=build /out/lib/ /usr/local/lib/trust/
ENV LD_LIBRARY_PATH=/usr/local/lib/trust

# The store is a directory of append-only logs.  Created here so that a named
# volume mounted over it inherits this ownership: Docker copies the image's for
# an empty volume, and a root-owned one would leave the unprivileged process
# below unable to write its own log.
RUN useradd --system --uid 10001 --home /data trust \
    && mkdir -p /data && chown trust:trust /data
VOLUME /data
ENV TRUST_STORE_DIR=/data

USER trust
EXPOSE 8080
ENV PORT=8080
# Inside a container the boundary is the isolation, so binding loopback would
# only make the node unreachable through its own published port.
ENV TRUST_BIND_ALL=true
HEALTHCHECK --interval=15s --timeout=3s --start-period=20s --retries=5 \
  CMD curl -fsS http://127.0.0.1:8080/api/health || exit 1
CMD ["trust-server"]
