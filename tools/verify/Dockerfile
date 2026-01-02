FROM eclipse-temurin:11-jre

# Install TLA+ tools v1.7.4 (latest stable)
RUN apt-get update && apt-get install -y curl && \
    curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar \
         -o /opt/tla2tools.jar && \
    apt-get remove -y curl && apt-get autoremove -y && rm -rf /var/lib/apt/lists/*

# Create wrapper script for TLC
RUN echo '#!/bin/sh' > /usr/local/bin/tlc && \
    echo 'java -jar /opt/tla2tools.jar "$@"' >> /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc

# Set working directory
WORKDIR /work

# Default command runs TLC
ENTRYPOINT ["java", "-jar", "/opt/tla2tools.jar"]
