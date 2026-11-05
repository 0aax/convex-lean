# Pinned revisions of the comparator toolchain.
ARG COMPARATOR_REV=11443b99aa874875225c16b55eaa417442a2bb30
ARG LANDRUN_REV=5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
ARG NANODA_REV=68d5ca9db226849b41a6fff59d796ff19d0a8840

# The sandbox the comparator runs every build and export inside. Go plus
# libcap/psx, built against bookworm's glibc, which the 24.04 final stage
# satisfies.
FROM golang:1.24-bookworm AS landrun-build
ARG LANDRUN_REV
RUN GOBIN=/out go install github.com/zouuup/landrun/cmd/landrun@${LANDRUN_REV}

# nanoda: an independently written Lean kernel in Rust.
FROM rust:1.83-bookworm AS nanoda-build
ARG NANODA_REV
RUN git clone https://github.com/robsimmons/nanoda_lib.git /src \
 && cd /src \
 && git checkout ${NANODA_REV} \
 && cargo build --release \
 && mkdir -p /out \
 && cp target/release/nanoda_bin /out/nanoda_bin

FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
      git ca-certificates curl ripgrep build-essential \
      tmux bash procps \
      python3 \
 && rm -rf /var/lib/apt/lists/*

RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain leanprover/lean4:v4.28.0
ENV PATH=/root/.elan/bin:$PATH

# The comparator and its exporter, built before Mathlib so that a break here
# fails the image build in minutes rather than after the Mathlib step.
#
# These binaries are NOT added to the image PATH. Only the verifier puts them
# there, so the agent's environment is unchanged by their presence.
ARG COMPARATOR_REV
ARG LANDRUN_REV
ARG NANODA_REV
RUN git clone https://github.com/leanprover/comparator.git /opt/comparator/src \
 && cd /opt/comparator/src \
 && git checkout ${COMPARATOR_REV} \
 && lake build lean4export comparator \
 && mkdir -p /opt/comparator/bin \
 && cp .lake/build/bin/comparator /opt/comparator/bin/comparator \
 && cp .lake/packages/lean4export/.lake/build/bin/lean4export /opt/comparator/bin/lean4export

COPY --from=landrun-build /out/landrun /opt/comparator/bin/landrun
COPY --from=nanoda-build /out/nanoda_bin /opt/comparator/bin/nanoda_bin

RUN cd /opt/comparator/src \
 && { echo "comparator      https://github.com/leanprover/comparator      ${COMPARATOR_REV}"; \
      echo "landrun         https://github.com/zouuup/landrun             ${LANDRUN_REV}"; \
      echo "nanoda_lib      https://github.com/robsimmons/nanoda_lib      ${NANODA_REV}"; \
      python3 -c 'import json; [print("%-15s %-45s %s" % (p["name"], p["url"], p["rev"])) for p in json.load(open("lake-manifest.json"))["packages"]]'; \
    } > /opt/comparator/PINS \
 && cat /opt/comparator/PINS

WORKDIR /app/open-eval

COPY docker/lean-mathlib-base/lakefile.toml docker/lean-mathlib-base/lean-toolchain ./

RUN mkdir -p LeanWorkspace \
 && printf 'import Mathlib\n' > LeanWorkspace.lean

RUN lake update \
 && lake exe cache get \
 && lake build LeanWorkspace

RUN mkdir -p /app/scratch

# Baked into every image; visible to the agent ONLY when a run config lists
# them under agents[].mcp_servers. Deliberately OFF PATH (under /opt/mcp), for
# the same reason the comparator binaries stay off PATH above: the no-MCP arm's
# environment must be unchanged by their presence, so one image serves both
# ablation arms. Register by absolute path:
#   { "name": "lean-lsp",  "transport": "stdio", "command": "/opt/mcp/bin/lean-lsp-mcp" }
#   { "name": "lean-beam", "transport": "stdio", "command": "/opt/mcp/bin/lean-beam-mcp" }
ARG LEAN_LSP_MCP_VERSION=0.30.0
ARG LEAN_BEAM_REV=fd26811ab7199ff059cca0768cd15596acfa90ad

# lean-lsp-mcp, local tools only
RUN apt-get update && apt-get install -y --no-install-recommends python3-venv \
 && rm -rf /var/lib/apt/lists/* \
 && python3 -m venv /opt/mcp/venv \
 && /opt/mcp/venv/bin/pip install --no-cache-dir lean-lsp-mcp==${LEAN_LSP_MCP_VERSION} \
 && mkdir -p /opt/mcp/bin \
 && printf '%s\n' \
      '#!/bin/sh' \
      'cd /app/open-eval || exit 1' \
      'LEAN_MCP_DISABLED_TOOLS="lean_leansearch,lean_loogle,lean_leanfinder,lean_state_search,lean_hammer_premise"' \
      'export LEAN_MCP_DISABLED_TOOLS' \
      'exec /opt/mcp/venv/bin/lean-lsp-mcp "$@"' \
      > /opt/mcp/bin/lean-lsp-mcp \
 && chmod +x /opt/mcp/bin/lean-lsp-mcp

# lean-beam
RUN git clone https://github.com/leanprover/lean-beam.git /opt/mcp/lean-beam-src \
 && cd /opt/mcp/lean-beam-src \
 && git checkout ${LEAN_BEAM_REV} \
 && BEAM_BIN_HOME=/opt/mcp/bin BEAM_INSTALL_ROOT=/opt/mcp/beam \
    ./scripts/install-beam.sh --dont-ask --toolchain leanprover/lean4:v4.28.0

RUN { echo "lean-lsp-mcp    https://pypi.org/project/lean-lsp-mcp         ${LEAN_LSP_MCP_VERSION}"; \
      echo "lean-beam       https://github.com/leanprover/lean-beam       ${LEAN_BEAM_REV}"; \
    } >> /opt/comparator/PINS \
 && cat /opt/comparator/PINS

WORKDIR /app/open-eval
