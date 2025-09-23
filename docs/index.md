# CQOTL Documentation

This documentation collects the working knowledge for the Classical-Quantum Relational Hoare Logic project. The repository is split into two main components:

- `generator/`: an OCaml verification-condition generator and interactive prover.
- `lean-veri/`: the Lean 4 development that discharges the generated obligations.

Additional LaTeX material lives in `draft/`, and Markdown guides reside in this `docs/` directory.

## How to Use This Documentation

- Start with [development](development.md) for build, tooling, and platform notes.
- The [generator architecture](generator.md) guide explains the OCaml code base, command language, and reasoning pipeline.
- Review [lean integration](lean-integration.md) to understand how obligations are exported to Lean 4.
- Browse [examples](examples.md) for a tour of the included case studies and sample scripts.

## Repository Layout (summary)

```
├── generator/           OCaml project (dune workspace)
│   ├── bin/             CLI entry points (filewatcher)
│   ├── lib/             Core libraries: AST, parser, typing, reasoning, Lean export
│   └── examples/        Case studies and Lean example scripts
├── lean-veri/           Lean 4 project receiving generated obligations
├── draft/               Research notes and paper draft (LaTeX)
├── docs/                Project documentation (this directory)
└── README.md            Quick start and outstanding work items
```

## Status at a Glance

- The OCaml generator builds with Dune on macOS(via OCaml 4.12+).
- Interactive proofs are orchestrated through the `filewatcher` executable and a source/status file pair.
- Obligation export currently targets Lean 4; Coq support is scaffolded but unfinished.
- Several reasoning tactics (`r_seq`, `r_unitary`, `simpl_entail`, etc.) rely on sophisticated rewriting rules captured in `lib/reasoning.ml`.

Refer back to this index as new documents are added to `docs/`.
