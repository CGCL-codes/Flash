FROM openjdk:17-jdk-slim

WORKDIR /flash

COPY ./src /flash

RUN chmod +x /flash/run.sh

RUN apt update && apt install -y procps python3 tmux