# Development Guide

This guide collects the practical steps for setting up and extending the CQOTL generator on macOS.

## Prerequisites

- **OCaml 4.12 or later** (the code builds on the OCaml Unix module; 4.14+ is recommended).
- **opam** for dependency management.
- **dune 2.9+** to build the OCaml workspace.
- **menhir 3.0+** because the parser is generated from `lib/parser.mly`.
- **Lean 4** (optional) if you want to check generated obligations in `lean-veri/`.

### macOS notes

- Homebrew installations of OCaml (`brew install ocaml opam`) work out of the box.
- Menhir ships with opam (`opam install menhir`).

## Building the generator

```bash
cd generator
opam switch create . 4.14.1 --deps-only --locked   # optional, creates a local switch
opam install . --deps-only                          # pulls dune, menhir, etc.
dune build
```

The generated executable lives at `_build/default/bin/filewatcher.exe` (extension omitted on Unix).

## Running the prover loop

```bash
cd generator
dune exec filewatcher source status
```

- `source` is the file you edit with commands (definitions, proofs, tactics).
- `status` is rewritten by the watcher after every successful parse; it shows the environment, open goals, and any errors.
- Both files are created automatically by `filewatcher` if they do not already exist.

Edit `source` with your favourite editor; the watcher re-runs the command list whenever the file timestamp changes.

## Exporting Lean obligations

1. Populate `cqotl_path.config` (at the repo root) with the absolute or relative path to this repository.
2. Load the Lean generator module. Because it currently lives inside the `cqotl_vgc` library there is no standalone executable; either:
   - launch `dune utop` from `generator/` and evaluate `open Cqotl_vgc.Lean_generator;;`, or
   - build a tiny wrapper executable that calls `Cqotl_vgc.Lean_generator.process_example` on the desired obligations list.
3. The helper writes `.lean` files under `lean-veri/LeanVeri/Examples/`.

The OCaml transformer in `lib/transformer.ml` builds `lean_codegen/quantum_ast.ml` nodes, which are then rendered by `lean_codegen/lean_printer.ml`. Wiring an explicit command-line wrapper is a good future enhancement.

## Lean verification

```bash
cd lean-veri
lake build
```

`lean-veri/LeanVeri.lean` provides the top-level imports for the verification library. Generated obligations appear under `LeanVeri/GENERATED_OBLIGATIONS` or `LeanVeri/Examples`, depending on which pipeline you run.

## Recommended workflow

1. Develop or edit examples under `generator/source` or `generator/examples/case-studies/`.
2. Run `dune exec filewatcher source status` in a dedicated terminal.
3. Inspect `status` to see typing or proof errors.
4. Once the proof script compiles and all goals discharge, export obligations with the Lean generator and migrate to Lean for final proofs.

## Testing and linting

- The project does not yet ship automated tests. When adding features, craft regression examples under `generator/examples/` and exercise them through the watcher.
- OCamlformat/OCaml LSP is not enforced, but trimming unused imports and keeping the module graph tidy helps incremental building.

## Troubleshooting

- **Parser errors**: incremental parsing (`Parser_utils.parse_top_inc`) keeps the longest prefix that parses; syntax errors are appended to `status` with line/column info.
- **Typing failures**: the typing engine (`lib/typing.ml`) prints the offending term. Cross-check the expected constructors in the AST constants (`lib/ast.ml`).
- **Lean export errors**: when types cannot be translated, the transformer emits a `LeanTranslationError` message. Look for terminal output when running the Lean generator.

Reach out via issues when documenting new tactics or extending the Lean pipeline; keep this guide updated as the ecosystem grows.
