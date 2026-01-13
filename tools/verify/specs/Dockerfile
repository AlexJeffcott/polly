# Development environment for working with TLA+ specifications
# This is separate from the main Dockerfile used by the CLI - this one includes
# additional tools for interactive development and editing of specs.

FROM eclipse-temurin:11-jre

# Install TLA+ tools v1.7.4 (matches main Dockerfile)
RUN apt-get update && apt-get install -y curl && \
    curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar \
         -o /opt/tla2tools.jar && \
    apt-get remove -y curl && apt-get autoremove -y && rm -rf /var/lib/apt/lists/*

# Install development tools for better DX
RUN apt-get update && apt-get install -y \
    bash \
    vim \
    less \
    tree \
    && rm -rf /var/lib/apt/lists/*

# Create tlc wrapper script
RUN echo '#!/bin/bash' > /usr/local/bin/tlc && \
    echo 'java -jar /opt/tla2tools.jar "$@"' >> /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc

WORKDIR /specs

# Default command: keep container alive for interactive use
CMD ["tail", "-f", "/dev/null"]
