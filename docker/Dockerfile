# Build and run a trust node.
#
# Two stages, because the toolchain that compiles Lean is 2 GB and a node that
# holds people's public keys and their assertions should carry as little as
# possible.  What ships is the binary, the Lean runtime libraries it links, and
# the two subprocesses it shells out to: `gpg`, which checks every signature,
# and `curl`, which is how it reaches other nodes since Lean has no TLS.

FROM debian:bookworm-slim AS build

# `build-essential` is not only Lean's linker: `leansqlite` compiles the SQLite
# amalgamation from C and links it into the binary, so the store needs a C
# compiler here.  It needs nothing in the runtime stage below, because by then
# SQLite is already inside `trust-server`.
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
#
# `check-build` and not `update`, and the difference is the whole reason this
# comment is long.  `lake update` *re-resolves* every dependency to its
# `inputRev` — `master`, for `trust` — and rewrites the manifest.  In a layer
# that Docker caches on `lakefile.toml` and `lake-manifest.json`, neither of
# which changes when `trust` does, that means the image is built against
# whatever `master` happened to be the first time this layer was built, and
# nothing in the repository says which commit that was.  A fix merged into core
# then does not reach the image, the rebuild reports success, and the only
# evidence is a symbol missing from the binary.
#
# `lake env true` resolves the workspace instead, which materialises exactly the
# revisions the manifest names and updates nothing.  (`check-build` looked like
# the honest spelling of "load the workspace" and fetches nothing at all, which
# would have left this layer a no-op.)  So the dependency versions become a
# committed fact, `lake update trust` followed by a commit is what a bump looks
# like, and the manifest changing is what invalidates this layer — which is the
# same event as the versions changing, rather than an unrelated one.
COPY lakefile.toml lake-manifest.json ./
RUN lake env true

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
#
# There is deliberately no `libsqlite3` here.  `leansqlite` bundles the SQLite
# amalgamation and links it statically, so the database engine ships inside the
# binary and this stage is exactly what it was before the store moved.
RUN apt-get update && apt-get install -y --no-install-recommends \
      gnupg curl ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=build /out/trust-server /usr/local/bin/trust-server
COPY --from=build /out/lib/ /usr/local/lib/trust/
ENV LD_LIBRARY_PATH=/usr/local/lib/trust

# The store is a directory holding one SQLite database.  Created here so that a
# named volume mounted over it inherits this ownership: Docker copies the
# image's for an empty volume, and a root-owned one would leave the
# unprivileged process below unable to write.  The directory matters as much as
# the file: SQLite puts the write-ahead log beside the database, so a store
# whose file is writable but whose directory is not cannot commit.
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
