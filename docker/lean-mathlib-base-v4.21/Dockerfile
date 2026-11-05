# Lean v4.21.0 / Mathlib v4.21.0 variant of docker/lean-mathlib-base.
#
# The comparator is upstream's first release, which targets v4.21.0-rc3, with
# the lean4export from the same day. Both are built UNMODIFIED except that
# their lean-toolchain is set to the workspace's v4.21.0: lean4export reads
# the workspace's .olean files, which only the same Lean version can read.
ARG COMPARATOR_REV=437574bcec4e7d76fa141e98e4a72682ab580859
ARG LEAN4EXPORT_REV=e6c7eafbb83cfad518b196164ee977f7f0ba3701
ARG LANDRUN_REV=5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.21.0

# The sandbox the comparator runs every build and export inside. Go plus
# libcap/psx, built against bookworm's glibc, which the 24.04 final stage
# satisfies.
FROM golang:1.24-bookworm AS landrun-build
ARG LANDRUN_REV
RUN GOBIN=/out go install github.com/zouuup/landrun/cmd/landrun@${LANDRUN_REV}

FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
      git ca-certificates curl ripgrep build-essential \
      tmux bash procps \
      python3 \
 && rm -rf /var/lib/apt/lists/*

ARG LEAN_TOOLCHAIN
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain ${LEAN_TOOLCHAIN}
ENV PATH=/root/.elan/bin:$PATH

# The comparator and its exporter, built before Mathlib so that a break here
# fails the image build in minutes rather than after the Mathlib step.
#
# These binaries are NOT added to the image PATH. Only the verifier puts them
# there, so the agent's environment is unchanged by their presence.
ARG COMPARATOR_REV
ARG LEAN4EXPORT_REV
ARG LANDRUN_REV
RUN git clone https://github.com/leanprover/comparator.git /opt/comparator/src \
 && cd /opt/comparator/src \
 && git checkout ${COMPARATOR_REV} \
 && echo "${LEAN_TOOLCHAIN}" > lean-toolchain \
 && lake build comparator \
 && mkdir -p /opt/comparator/bin \
 && cp .lake/build/bin/comparator /opt/comparator/bin/comparator

RUN git clone https://github.com/leanprover/lean4export.git /opt/comparator/lean4export-src \
 && cd /opt/comparator/lean4export-src \
 && git checkout ${LEAN4EXPORT_REV} \
 && echo "${LEAN_TOOLCHAIN}" > lean-toolchain \
 && lake build lean4export \
 && cp .lake/build/bin/lean4export /opt/comparator/bin/lean4export

COPY --from=landrun-build /out/landrun /opt/comparator/bin/landrun

RUN { echo "toolchain       ${LEAN_TOOLCHAIN}"; \
      echo "comparator      https://github.com/leanprover/comparator      ${COMPARATOR_REV}"; \
      echo "lean4export     https://github.com/leanprover/lean4export     ${LEAN4EXPORT_REV}"; \
      echo "landrun         https://github.com/zouuup/landrun             ${LANDRUN_REV}"; \
    } > /opt/comparator/PINS \
 && cat /opt/comparator/PINS

WORKDIR /app/open-eval

COPY docker/lean-mathlib-base-v4.21/lakefile.toml docker/lean-mathlib-base-v4.21/lean-toolchain ./

RUN mkdir -p LeanWorkspace \
 && printf 'import Mathlib\n' > LeanWorkspace.lean

RUN lake update \
 && lake exe cache get \
 && lake build LeanWorkspace

RUN mkdir -p /app/scratch

# lean-lsp-mcp, local tools only. Baked in but OFF PATH, as in the v4.28 image:
# visible to the agent only when a run config registers
#   { "name": "lean-lsp", "transport": "stdio", "command": "/opt/mcp/bin/lean-lsp-mcp" }
ARG LEAN_LSP_MCP_VERSION=0.30.0
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
 && chmod +x /opt/mcp/bin/lean-lsp-mcp \
 && echo "lean-lsp-mcp    https://pypi.org/project/lean-lsp-mcp         ${LEAN_LSP_MCP_VERSION}" >> /opt/comparator/PINS

WORKDIR /app/open-eval
