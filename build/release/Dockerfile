# The Linux image of scripts/release-dryrun.sh --linux, which builds it for linux/arm64 and runs
# the build, the tests and scripts/corpus.sh in it. The toolchain named by lean-toolchain is
# installed at run time into the named volume over /root/.elan, so it survives a cut-off run.
FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# The packages are not pinned to versions, which the Ubuntu archive drops as it updates; the base image
# is pinned by digest. python3 runs scripts/tarball.py.
RUN apt-get update \
  && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends ca-certificates curl python3 \
  && rm -rf /var/lib/apt/lists/*

# The installer script is pinned to the commit of elan's v4.2.4 release tag, as in ci.yml.
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/227caca133724d5516bee25c2aeb3e609478f2d8/elan-init.sh \
  | sh -s -- -y --default-toolchain none

ENV PATH=/root/.elan/bin:$PATH
WORKDIR /writ
