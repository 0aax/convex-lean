FROM ghcr.io/0aax/open-eval-base:v4.28.0-r4

COPY ChebyshevSet_defs.lean /app/open-eval/LeanWorkspace/ChebyshevSet_defs.lean
COPY ChebyshevSet_pos.lean /app/open-eval/LeanWorkspace/ChebyshevSet_pos.lean
COPY ChebyshevSet_neg.lean /app/open-eval/LeanWorkspace/ChebyshevSet_neg.lean
COPY statement.tex.in /app/open-eval/statement.tex

RUN printf 'import LeanWorkspace.ChebyshevSet_defs\nimport LeanWorkspace.ChebyshevSet_pos\nimport LeanWorkspace.ChebyshevSet_neg\n' >> /app/open-eval/LeanWorkspace.lean

RUN mkdir -p /opt/pristine  && cp /app/open-eval/lakefile.toml        /app/open-eval/lean-toolchain        /app/open-eval/lake-manifest.json        /app/open-eval/LeanWorkspace.lean        /opt/pristine/

# The comparator's trusted side. Both stay out of /app: the challenge is a
# self-contained copy of the definitions, the Prop, and BOTH sorried theorems,
# so one challenge module serves the POS and the NEG grading pass. The
# verifier installs it as a sibling module only after the agent has stopped.
COPY Challenge.lean /opt/pristine/Challenge.lean
COPY comparator.json /opt/pristine/comparator.json
COPY comparator_neg.json /opt/pristine/comparator_neg.json

# `submit pos|neg`: in-run verification with the same comparator (see
# submit_template.sh). Present in every image; used by the gated agent loop.
COPY submit.sh /usr/local/bin/submit
RUN chmod +x /usr/local/bin/submit

# Build the issued layout (two sorry warnings expected): a broken split fails
# HERE, not at grading time.
RUN cd /app/open-eval && lake build LeanWorkspace

WORKDIR /app/open-eval
