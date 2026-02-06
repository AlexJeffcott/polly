# Verification Specifications

This directory contains formal specifications and verification configurations for `@fairfox/polly`.

## Contents

### `verification.config.ts`
Example verification configuration demonstrating how to use the verify package with web extensions.

### `tla/`
TLA+ specifications for formal verification:
- `MessageRouter.tla` - TLA+ specification of the message routing system
- `MessageRouter.cfg` - TLC model checker configuration
- `README.md` - Documentation for running TLA+ verification

### Docker Setup
- `Dockerfile` - Development container with TLA+ tools and editing utilities (vim, less, tree)
- `docker-compose.yml` - Docker Compose configuration for interactive development

**Note:** This is separate from the main `/tools/verify/Dockerfile` which is used by the Polly CLI for automated verification. Use this Dockerfile for interactive development and manual spec editing.

## Running Verification

### With Docker Compose (Interactive Development)
Start a container with TLA+ tools and development utilities:
```bash
cd tools/verify/specs
docker-compose up -d
docker-compose exec tla bash
# Inside container:
cd tla
tlc MessageRouter.tla -config MessageRouter.cfg
```

### With TLC Directly
```bash
cd tools/verify/specs/tla
tlc MessageRouter.tla -config MessageRouter.cfg
```

## See Also
- [Verify Package Documentation](../README.md)
- [TLA+ Specifications](./tla/README.md)
- [Examples](../../../examples/) - See todo-list and full-featured for verification in action
