# Verification Specifications

This directory contains formal specifications and verification configurations for the `@fairfox/polly-verify` package.

## Contents

### `verification.config.ts`
Example verification configuration demonstrating how to use the verify package with web extensions.

### `tla/`
TLA+ specifications for formal verification:
- `MessageRouter.tla` - TLA+ specification of the message routing system
- `MessageRouter.cfg` - TLC model checker configuration
- `README.md` - Documentation for running TLA+ verification

### Docker Setup
- `Dockerfile` - Container setup for TLA+ toolchain
- `docker-compose.yml` - Docker Compose configuration for running verification

## Running Verification

### With Docker (Recommended)
```bash
cd packages/verify/specs
docker-compose up
```

### With TLC Directly
```bash
cd packages/verify/specs/tla
tlc MessageRouter.tla -config MessageRouter.cfg
```

## See Also
- [Verify Package Documentation](../README.md)
- [WebSocket Example](../examples/websocket-app/README.md)
- [TLA+ Specifications](./tla/README.md)
