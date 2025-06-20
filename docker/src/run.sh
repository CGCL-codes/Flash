#!/bin/bash

ROOT_DIR="/flash/java-benchmarks/JDV/target"

for dir in "$ROOT_DIR"/*/; do
    TARGET_NAME=$(basename "$dir")
    CONFIG_FILE="/flash/java-benchmarks/JDV/target/$TARGET_NAME/config.yml"
    LOG_FILE="/flash/java-benchmarks/JDV/target/$TARGET_NAME/log.log"
    java -Xss1024m -Xmx8G -jar flash.jar --options-file "$CONFIG_FILE" > "$LOG_FILE" 2>&1
    cp /flash/time /flash/java-benchmarks/JDV/target/$TARGET_NAME/time
done

# nohup bash run.sh > run.log 2>&1 &