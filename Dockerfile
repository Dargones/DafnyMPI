ARG BASEPLATFORM=linux/amd64
FROM --platform=$BASEPLATFORM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates wget apt-transport-https gnupg && \
    wget -q https://packages.microsoft.com/config/ubuntu/22.04/packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    rm -f packages-microsoft-prod.deb

# Python + Open MPI + Dotnet
RUN apt-get update && \
  apt-get install -qy --no-install-recommends \
    apt-transport-https \
    make unzip wget \
    build-essential \
    python3 python3-pip python3-dev \
    time \
    openmpi-bin libopenmpi-dev \
    dotnet-sdk-8.0 && \
  rm -rf /var/lib/apt/lists/*

# Python packages
RUN pip3 install --no-cache-dir numpy mpi4py matplotlib

ARG UID=1000
ARG GID=1000
RUN if getent group ${GID} >/dev/null; then :; else groupadd -g ${GID} app; fi \
 && useradd -m -u ${UID} -g ${GID} -s /bin/bash app \
 && mkdir -p /dafnympi /work /home/app/.nuget/packages \
 && chown -R app:${GID} /dafnympi /work /home/app

USER app

ENV HOME=/home/app \
    DOTNET_CLI_HOME=/home/app \
    NUGET_PACKAGES=/home/app/.nuget/packages \
    DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 \
    DOTNET_CLI_TELEMETRY_OPTOUT=1 \
    NUGET_XMLDOC_MODE=skip

WORKDIR /dafnympi

ENV PATH="/dafnympi/dafny/Binaries/z3/bin:${PATH}"
