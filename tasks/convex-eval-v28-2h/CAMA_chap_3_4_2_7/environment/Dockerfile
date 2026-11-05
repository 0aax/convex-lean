FROM ghcr.io/0aax/open-eval-base:v4.28.0-r4

# The base image builds its Lake package at /app/open-eval; these are textbook
# results, not open problems, so the package is issued at /app/convex-eval.
# Moving it keeps the prebuilt Mathlib oleans (the build below confirms it).
# Leave the base image's WORKDIR first: Docker recreates the current WORKDIR
# for every later RUN, which would leave an empty /app/open-eval behind.
WORKDIR /app
RUN mv /app/open-eval /app/convex-eval

COPY CAMA_chap_3_4_2_7.lean /app/convex-eval/LeanWorkspace/CAMA_chap_3_4_2_7.lean

RUN printf 'import LeanWorkspace.CAMA_chap_3_4_2_7\n' >> /app/convex-eval/LeanWorkspace.lean

RUN mkdir -p /opt/pristine  && cp /app/convex-eval/lakefile.toml        /app/convex-eval/lean-toolchain        /app/convex-eval/lake-manifest.json        /app/convex-eval/LeanWorkspace.lean        /opt/pristine/

# The comparator's trusted side, kept out of /app: the challenge is the issued
# file verbatim, sorry included. The verifier installs it as a sibling module
# only after the agent has stopped.
COPY Challenge.lean /opt/pristine/Challenge.lean
COPY comparator.json /opt/pristine/comparator.json

# `submit`: in-run verification with the same comparator (see submit.sh).
COPY submit.sh /usr/local/bin/submit
RUN chmod +x /usr/local/bin/submit

# Build the issued layout (one sorry warning expected): a broken statement
# fails HERE, not at grading time.
RUN cd /app/convex-eval && lake build LeanWorkspace

WORKDIR /app/convex-eval
