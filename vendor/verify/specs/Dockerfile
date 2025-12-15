FROM tlaplus/tla:latest

# Install additional tools for better DX
RUN apk add --no-cache \
    bash \
    vim \
    less \
    tree

WORKDIR /specs

# Default command: keep container alive for exec commands
CMD ["tail", "-f", "/dev/null"]
