# TLA+ Resources

A curated collection of TLA+ learning materials, tools, and community resources.

## Official Documentation

### TLA+ Language & Tools

- **[TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)** - Leslie Lamport's official TLA+ website
- **[TLA+ Wiki](https://docs.tlapl.us/)** - Community-maintained documentation
- **[TLC Model Checker Config Files](https://docs.tlapl.us/using:tlc:config_file)** - Configuration file syntax and options
- **[TLA+ Specification](https://lamport.azurewebsites.net/tla/book.html)** - The TLA+ specification book

### PlusCal

- **[PlusCal User's Manual (P-Syntax)](https://lamport.azurewebsites.net/tla/p-manual.pdf)** - Official PlusCal documentation

## Interactive Learning

### Beginner-Friendly Courses

- **[Learn TLA+](https://learntla.com/)** - Comprehensive interactive tutorial by Hillel Wayne
  - [Constants & Parameters](https://learntla.com/core/constants.html)
  - [Model Values](https://old.learntla.com/models/model-values/)
- **[TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)** - Leslie Lamport's video lectures

### Books

- **[Practical TLA+](https://www.apress.com/gp/book/9781484238288)** by Hillel Wayne - Hands-on guide to learning TLA+
- **[Specifying Systems](https://lamport.azurewebsites.net/tla/book.html)** by Leslie Lamport - The definitive TLA+ textbook

## Tools & IDE Support

### TLA+ Toolbox

- **[TLA+ Toolbox Download](https://github.com/tlaplus/tlaplus/releases)** - Official IDE for TLA+
- **[Toolbox Documentation](https://tla.msr-inria.inria.fr/tlatoolbox/doc/)** - Complete toolbox user guide
  - [Model Values and Symmetry](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/model-values.html)
  - [Model Overview Page](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/overview-page.html)
  - [Checking a Model](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/executing-tlc.html)

### VS Code Extension

- **[TLA+ for VS Code](https://github.com/tlaplus/vscode-tlaplus)** - Visual Studio Code extension for TLA+
  - [Issue #159: Better separate models and specs](https://github.com/tlaplus/vscode-tlaplus/issues/159)

### Command Line Tools

- **[TLA+ Command Line Tools](https://github.com/tlaplus/tlaplus)** - Run TLC from the command line
- **[Apalache](https://apalache.informal.systems/)** - Symbolic model checker for TLA+

## Community Resources

### Blogs & Articles

#### Advanced Topics

- **[An Introduction to Symmetry in TLA+](https://jack-vanlightly.com/blog/2024/12/5/an-introduction-to-symmetry-in-tla)** by Jack Vanlightly (Dec 2024)
  - Visual explanation of symmetry reduction
  - State space reduction examples
  - Practical tips for using symmetry

- **[Using TLA+ in the Real World to Understand a Glibc Bug](https://probablydance.com/2020/10/31/using-tla-in-the-real-world-to-understand-a-glibc-bug/)** by Malte Skarupke (Oct 2020)
  - Real-world debugging case study
  - Practical application of TLA+

#### Industry Case Studies

- **[Amazon's Use of TLA+](https://lamport.azurewebsites.net/tla/amazon.html)** - How Amazon uses TLA+ for critical systems
- **[Microsoft Azure's Use of TLA+](https://azure.microsoft.com/en-us/blog/azure-cosmos-db-pushing-the-frontier-of-globally-distributed-databases/)** - Cosmos DB verification

### Community Forums

- **[TLA+ Google Group](https://groups.google.com/g/tlaplus)** - Official discussion forum
  - [The effect of symmetry sets on TLC performance](https://groups.google.com/g/tlaplus/c/LlUYtAG8OyE)
  - [Syntax of cfg file](https://groups.google.com/g/tlaplus/c/PVa4CZMUQjE)

- **[TLA+ Discuss](https://discuss.tlapl.us/)** - Community discussion board
  - [Symmetry sets discussion](https://discuss.tlapl.us/msg02571.html)
  - [Re: Symmetry sets](https://discuss.tlapl.us/msg02575.html)

### GitHub Issues & Discussions

- **[TLA+ GitHub Repository](https://github.com/tlaplus/tlaplus)**
  - [Issue #404: Specifying symmetry set in cfg file manually](https://github.com/tlaplus/tlaplus/issues/404)
  - [Issue #705: Config file error messages](https://github.com/tlaplus/tlaplus/issues/705)
  - [Bug Reports](http://tla.msr-inria.inria.fr/bugzilla/)

## TLA+ Concepts

### Symmetry Reduction

Symmetry reduction is a powerful optimization technique that reduces the state space by treating equivalent states as identical.

**Key Resources:**
- [Model Values and Symmetry](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/model-values.html) - Official documentation
- [Jack Vanlightly's Symmetry Guide](https://jack-vanlightly.com/blog/2024/12/5/an-introduction-to-symmetry-in-tla) - Visual introduction
- [Google Group: Symmetry performance](https://groups.google.com/g/tlaplus/c/LlUYtAG8OyE) - Performance discussion

**Important Limitations:**
- Only ONE `SYMMETRY` declaration is allowed per config file (see [Issue #16](https://github.com/AlexJeffcott/polly/issues/16))
- Cannot check liveness properties when symmetry is used
- Large symmetry sets can be computationally expensive

### Model Checking

- **[TLC Model Checker Notes](https://courses.csail.mit.edu/6.897/spring01/LN/TLC_notes.pdf)** (MIT) - Technical overview of TLC
- **[Advanced TLA+ Examples](https://lamport.azurewebsites.net/tla/advanced-examples.html)** - Complex specifications and techniques

## Example Specifications

### Public Specifications

- **[TLA+ Examples Repository](https://github.com/tlaplus/Examples)** - Official collection of TLA+ specs
- **[Consensus Algorithms in TLA+](https://github.com/ongardie/raft.tla)** - Raft consensus algorithm
- **[Paxos in TLA+](https://github.com/tlaplus/tlaplus/tree/master/examples)** - Classic Paxos specification

### Tutorials & Workshops

- **[TLA+ Workshop Materials](https://github.com/tlaplus/DrTLAPlus)** - Workshop exercises and solutions
- **[PlusCal Examples](https://github.com/lemmy/PlusCal-Examples)** - Collection of PlusCal algorithms

## Troubleshooting & FAQs

### Common Issues

1. **Config File Errors**
   - [Specifying symmetry set manually](https://github.com/tlaplus/tlaplus/issues/404)
   - [Config file syntax errors](https://groups.google.com/g/tlaplus/c/PVa4CZMUQjE)

2. **Performance Optimization**
   - [Symmetry set performance](https://groups.google.com/g/tlaplus/c/LlUYtAG8OyE)
   - Use state constraints to limit exploration
   - Consider bounded model checking for large state spaces

3. **Debugging Specifications**
   - Use `CHOOSE` operator carefully
   - Enable TLC tracing with `-tool` flag
   - Check invariants incrementally

## Related Tools

### Formal Methods

- **[Alloy](https://alloytools.org/)** - Lightweight formal specification language
- **[Z3](https://github.com/Z3Prover/z3)** - SMT solver (used by Apalache)
- **[SPIN](http://spinroot.com/)** - Model checker for concurrent systems

### Visualization

- **[TLA+ State Graph Visualizer](https://github.com/will62794/tla-web)** - Web-based TLA+ visualization
- **[TLA+ Trace Explorer](https://github.com/tlaplus/tlaplus/tree/master/toolbox/org.lamport.tla.toolbox.tool.tlc.ui)** - Built into TLA+ Toolbox

## Contributing

### Get Involved

- **[TLA+ GitHub](https://github.com/tlaplus)** - Contribute to TLA+ tools
- **[TLA+ Community Wiki](https://github.com/tlaplus/tlaplus/wiki)** - Community documentation
- **[TLA+ Slack/Discord]** - Real-time community chat (check TLA+ Google Group for links)

## Polly-Specific Resources

### Verification in Polly

- [Polly Optimization Guide](./OPTIMIZATION.md) - Tier 1 & Tier 2 optimizations
- [Polly Architecture](./ARCHITECTURE.md) - How Polly generates TLA+ specs
- [Issue #16: Multiple Symmetry Groups](https://github.com/AlexJeffcott/polly/issues/16) - TLA+ limitation handling

---

## Quick Reference

### Essential Links for Getting Started

1. [Learn TLA+](https://learntla.com/) - Start here for interactive learning
2. [TLA+ Toolbox](https://github.com/tlaplus/tlaplus/releases) - Download the IDE
3. [TLA+ Google Group](https://groups.google.com/g/tlaplus) - Ask questions
4. [Jack Vanlightly's Blog](https://jack-vanlightly.com/blog/2024/12/5/an-introduction-to-symmetry-in-tla) - Symmetry guide

### Advanced Topics

1. [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html) - Deep dive
2. [Amazon's TLA+ Case Studies](https://lamport.azurewebsites.net/tla/amazon.html) - Real-world use
3. [Apalache](https://apalache.informal.systems/) - Symbolic model checking

---

**Last Updated**: January 2026

**Maintained By**: Polly Team

**Contributing**: Found a useful TLA+ resource? Please submit a PR to add it!
