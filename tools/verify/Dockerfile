FROM eclipse-temurin:11-jre

# Install TLA+ tools v1.7.4 (latest stable, includes TLC 2.19 from August 2024)
RUN apt-get update && apt-get install -y curl && \
    curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar \
         -o /opt/tla2tools.jar && \
    apt-get remove -y curl && apt-get autoremove -y && rm -rf /var/lib/apt/lists/*

# Create entrypoint wrapper that handles "tlc" command
RUN echo '#!/bin/sh' > /usr/local/bin/docker-entrypoint.sh && \
    echo '# Strip "tlc" command if passed as first argument' >> /usr/local/bin/docker-entrypoint.sh && \
    echo 'if [ "$1" = "tlc" ]; then' >> /usr/local/bin/docker-entrypoint.sh && \
    echo '  shift' >> /usr/local/bin/docker-entrypoint.sh && \
    echo 'fi' >> /usr/local/bin/docker-entrypoint.sh && \
    echo 'exec java -jar /opt/tla2tools.jar "$@"' >> /usr/local/bin/docker-entrypoint.sh && \
    chmod +x /usr/local/bin/docker-entrypoint.sh

# Set working directory
WORKDIR /work

# Use wrapper script as entrypoint
ENTRYPOINT ["/usr/local/bin/docker-entrypoint.sh"]
