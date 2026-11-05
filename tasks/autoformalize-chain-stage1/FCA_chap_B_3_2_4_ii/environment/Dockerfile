FROM ghcr.io/0aax/open-eval-base:v4.28.0-r4

# The base image builds its Lake package at /app/open-eval. This is an
# autoformalization task, so the package is issued at /app/autoformalize. Leave
# the base image's WORKDIR first: Docker recreates the current WORKDIR for every
# later RUN, which would leave an empty /app/open-eval behind.
WORKDIR /app
RUN mv /app/open-eval /app/autoformalize

# The corpus: every book and paper the formalization project drew on, as PDFs,
# with an index of titles. No PDF tooling is installed on purpose; the agent
# installs what it needs.
COPY corpus/ /app/corpus/
COPY INDEX.md /app/corpus/INDEX.md

# The statement file starts as a placeholder theorem of the right name, so the
# package builds before the agent touches it.
COPY FCA_chap_B_3_2_4_ii.lean /app/autoformalize/LeanWorkspace/FCA_chap_B_3_2_4_ii.lean

# The project's definitions file.
COPY Defs.lean /app/autoformalize/LeanWorkspace/Defs.lean
RUN printf 'import LeanWorkspace.Defs\nimport LeanWorkspace.FCA_chap_B_3_2_4_ii\n' >> /app/autoformalize/LeanWorkspace.lean

RUN mkdir -p /opt/pristine /app/scratch \
 && cp /app/autoformalize/lakefile.toml \
       /app/autoformalize/lean-toolchain \
       /app/autoformalize/lake-manifest.json \
       /app/autoformalize/LeanWorkspace.lean \
       /opt/pristine/

# The format check shared by `submit` (in-run) and tests/test.sh (grading).
COPY check_statement.py /opt/pristine/check_statement.py
COPY submit.sh /usr/local/bin/submit
RUN chmod +x /usr/local/bin/submit

RUN cd /app/autoformalize && lake build LeanWorkspace

WORKDIR /app/autoformalize
