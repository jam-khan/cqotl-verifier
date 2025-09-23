# Lean Integration

The CQOTL tool chain produces proof obligations that can be discharged inside Lean 4. This document explains the translation path and the supporting Lean project.

## Translation pipeline (OCaml side)

1. **Frame extraction** (`lib/transformer.ml`)
   - `proof_frame_to_lean_frame` picks the leading goal from a `proof_frame` and trims the environment to the symbols used in the goal.
   - Quantum-specific utilities (e.g. `extract_symbols_from_goal`) keep only relevant assumptions.

2. **Intermediate AST** (`lib/lean_codegen/quantum_ast.ml`)
   - Defines `qType`, `expr`, and `quantumEnv` nodes that represent types, propositions, and environment entries in a Lean-friendly format.
   - Supports constructs such as labelled Dirac notation, Loewner order, and quantified propositions.

3. **Mapping to Lean syntax** (`lib/lean_codegen/mapper.ml`)
   - `transform_obligation_to_lean_file` converts `quantum_ast` nodes into `Lean_ast.lean_file` values, stitching together imports, notation declarations, and obligations.
   - The code uses helper functions from `lean_codegen/lean_commons.ml` to reuse standard definitions (kets, projectors, trace, etc.).

4. **Printing** (`lib/lean_codegen/lean_printer.ml`)
   - Renders `lean_file` records into plain `.lean` text, ready to be written to disk.

5. **Driver** (`lib/lean_codegen/lean_generator.ml`)
   - Binds everything together: reads `cqotl_path.config`, iterates over the `examples` list defined in `lean_examples.ml`, and writes each file into `lean-veri/LeanVeri/Examples/`.
   - Because it lives inside the `cqotl_vgc` library there is no standalone executable yet. Load it via `dune utop` (`open Cqotl_vgc.Lean_generator;;`) or build a small wrapper executable.

## Configuration

- `cqotl_path.config` must contain the absolute or relative repository path. The driver resolves the target directory (`lean-veri/LeanVeri/Examples/`) against it.
- Generated files are overwritten on each run; commit them intentionally if they represent stable obligations.

## Lean project layout

`lean-veri/` is a Lake-managed Lean workspace:

- `LeanVeri/` holds the main library with reusable lemmas, notation, and tactics for relational Hoare logic.
- `LeanVeri/Examples/` receives generated obligations.
- `LeanVeri/GENERATED_OBLIGATIONS/` stores legacy outputs from an earlier pipeline.
- `LeanVeri.lean` is the umbrella import file.

Run `lake build` (or `lake exe cache get` for dependencies) to compile the Lean project after generating obligations.

## Working with generated obligations

1. Export the obligations and inspect the emitted `.lean` files under `LeanVeri/Examples/`.
2. Open them in a Lean editor (VS Code, Emacs, Neovim) and fill in the proofs.
3. Keep an eye on the `QuantumAssumption` versus `QuantumDefinition` split: assumptions translate into Lean definitions with placeholder proofs (usually `sorry`), whereas definitions translate into full terms.
4. If Lean reports type mismatches, trace back to the OCaml types in `typing.ml` and the translation rules in `mapper.ml`.

## Future work

- Provide a first-class `dune exec` wrapper for the Lean generator to simplify CI usage.
- Expand the translator to cover remaining tactics (e.g. additional entanglement reasoning) and the Coq back-end (`lib/coqQ_ast.ml`).
- Synchronise the Lean imports with the evolving theory files in `lean-veri/LeanVeri/`.

Use this document when adjusting the Lean export path or onboarding new contributors to the Lean side of the project.
