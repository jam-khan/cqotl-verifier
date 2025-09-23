# (Maybe Complete) Classical-Quantum Relational Hoare Logics

CQOTL combines an OCaml verification-condition generator with a Lean 4 development for relational Hoare logic over classical-quantum programs.

GitHub repository: https://github.com/LucianoXu/cqotl.git

## Repository layout
- `generator/`: OCaml project that parses Rocq-style scripts, evaluates proof commands, and exports Lean obligations.
- `lean-veri/`: Lean 4 project that discharges the generated proof obligations.
- `docs/`: Markdown documentation (start with `docs/index.md`).
- `draft/`: LaTeX notes and paper drafts.
- `cqotl_path.config`: Path hint used by the Lean obligation exporter.

## Quick start (generator)

### Prerequisites
- **OCaml** 4.12 or later (4.14+ recommended).
- **opam** for dependency management.
- **dune** 2.9+.
- **menhir** 3.0+.

### Build steps

```bash
cd generator
opam install . --deps-only            # installs dune, menhir, etc.
dune build
```

For an isolated toolchain you can create a local switch first:

```bash
opam switch create . 4.14.1 --deps-only --locked
```

## Prover loop

Launch the interactive watcher from `generator/`:

```bash
dune exec filewatcher source status
```

- `source` collects the Rocq-style commands you edit.
- `status` is rewritten after every successful parse, showing the current environment, open goals, or syntax/typing errors.
- Both files are created automatically if they are missing.

Keep the watcher running in a terminal while you edit `source`; the process replays the script whenever the file timestamp changes.

## Lean integration

1. Ensure `cqotl_path.config` points at the repository root.
2. Use the Lean generator inside a Dune toplevel (`dune utop` → `open Cqotl_vgc.Lean_generator;;`) or wire a small wrapper executable.
3. Generated obligations are written under `lean-veri/LeanVeri/Examples/`.
4. Build the Lean project with:

   ```bash
   cd lean-veri
   lake build
   ```

Refer to `docs/lean-integration.md` for the full translation pipeline and future improvements.

## Documentation

- `docs/index.md` – entry point covering available guides.
- `docs/development.md` – macOS setup notes, build instructions, and troubleshooting.
- `docs/generator.md` – architecture overview of the OCaml codebase.
- `docs/examples.md` – catalogue of case studies shipped with the repository.
