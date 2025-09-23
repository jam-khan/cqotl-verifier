# Examples and Case Studies

The repository ships several scripted examples that exercise the prover and Lean exporter. Use them as regression tests or starting points for new developments.

## OCaml-side scripts (`generator/examples/`)

- `case-studies/` contains Rocq-style proof scripts. Files such as `example2` and `example4` demonstrate tactics like `r_seq`, `r_meas_meas`, and `cylinder_ext` on quantum programs.
- `lean-examples/` hosts Lean-specific snippets referenced by the exporter.

### Trying a case study

1. Copy an example into the watcher source:
   ```bash
   cd generator
   cp examples/case-studies/example2 source
   dune exec filewatcher source status
   ```
2. Inspect `status` to see the unfolding proof state. Tactics that are still marked `sorry` leave subgoals for Lean.

### Creating a new script

- Use `Def` and `Var` commands to set up operators and registers.
- Wrap the judgement you want to prove in a `Prove ... QED.` block.
- Combine classical tactics (`intro`, `rewrite`, `split`) with the quantum-specific rules (`r_unitary`, `r_meas`, `dirac`).
- Keep intermediate scripts under `examples/case-studies/` to document progress.

## Lean examples (`lean-veri/LeanVeri/Examples/`)

- After running the translator, generated `.lean` files appear alongside hand-written ones (e.g. `Obligation1-1.lean`).
- `LeanVeri/GENERATED_OBLIGATIONS/` stores legacy outputs—handy for spotting regression in the translator.

## Draft LaTeX (`draft/`)

The `draft/` directory contains the project manuscript (`main.tex`, `cqotl.tex`) and bibliography (`ref.bib`). Reference it when aligning documentation with the formal write-up.

## Suggested workflow

1. Iterate on proofs in `generator/source` with the watcher running.
2. Once the OCaml proof script closes, regenerate the Lean obligation.
3. Finish the proof inside Lean and commit both the OCaml script and the Lean proof for traceability.

Keep enriching the case-study folder—each new example doubles as documentation and as a test case for the typing, reasoning, and translation pipeline.
