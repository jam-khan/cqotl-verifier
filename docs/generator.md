# Generator Architecture

The `generator/` directory hosts the OCaml verification-condition generator. The tool parses Rocq-style scripts, evaluates them against an interactive proof state, and emits Lean-friendly proof obligations.

## High-level data flow

1. **Parsing** (`lib/parser.mly`, `lib/lexer.mll`, `lib/parser_utils.ml`)
   - `parser_utils.ml` wraps Menhir's incremental API. `parse_top_inc` keeps the longest prefix that parses and reports syntax errors with line/column info.
2. **Abstract syntax** (`lib/ast.ml`, `lib/ast_transform.ml`)
   - `ast.ml` defines command, tactic, and term constructors; it also encodes proof frames, environments, and helper types like `wf_ctx`.
3. **Typing** (`lib/typing.ml`)
   - The `calc_type` and `type_check` routines validate terms against a hierarchy of quantum/classical types (`Type`, `CVar`, `OType`, `DType`, etc.).
   - Helpers such as `get_qvlist` and `fresh_name_for_ctx` manage naming inside well-formed contexts.
4. **Reasoning** (`lib/reasoning.ml`)
   - Implements transformation passes and rewriting rules for boolean and quantum reasoning (e.g. `simpl`, `ciPi_merge`, `cq_entailment_destruct`).
   - Tactics like `simpl_entail`, `cylinder_ext`, and `entail_trans` delegate to these transformations.
5. **Evaluation and pretty-printing** (`lib/prover.ml`, `lib/pretty_printer.ml`)
   - `prover.ml` maintains a stack of frames (`NormalFrame` or `ProofFrame`) and interprets commands/tactics.
   - `eval_list` stops at the first failure. `get_status` renders the current frame using `pretty_printer.ml`.
6. **Lean export** (`lib/transformer.ml`, `lib/lean_codegen/*`)
   - `transformer.ml` converts proof frames into `lean_codegen/quantum_ast.ml` nodes.
   - `lean_codegen/` turns the intermediate AST into Lean syntax (`lean_printer.ml`) and stores sample obligations (`lean_examples.ml`).

The entire library is packaged as `cqotl_vgc` (see `lib/dune`) and consumed by the `filewatcher` executable.

## Command language

The syntax mirrors Rocq. Key commands are defined in `ast.ml`:

- `Def`, `Var`, `Check`, and `Show` manage the global environment.
- `Prove` starts a proof block; `QED` closes it.
- `Tactic` carries proof steps such as `intro`, `split`, `by_lean`, `r_meas`, and the specialised quantum rules.
- `Synthesize` triggers program synthesis (experimental).

See `generator/README.txt` for concrete examples, including while loops, unitary operations, and measurement commands.

## Proof frames and contexts

- `envItem` values (`Assumption` or `Definition`) capture named bindings.
- A `proof_frame` retains the global environment, proof goal, open subgoals, and obligations queued for Lean (`lean_goals`, `rocq_goals`).
- Tactics operate over the first open goal, rewriting or splitting it until the goal list is empty (`add_goal`, `discharge_first_goal`, etc.).

`typing.ml` supplies `wf_ctx` values that combine the proof environment and the local context of hypotheses to compute term types.

## Reasoning building blocks

`reasoning.ml` aggregates reusable transformations:

- Rewriting rules (`simpl_rules`) collapse propositional clutter and quantum Dirac notation.
- `ciPi_merge` merges identical preconditions within conjunctions.
- `cq_entailment_destruct` and `cylinder_ext` decompose entailments according to quantum variable scopes.
- Each transformation is wrapped by `apply_trans_all` and `repeat_transforms`, providing search-style tactics.

These utilities keep tactic code in `prover.ml` concise.

## File watcher entry point

`bin/filewatcher.ml` exposes the CLI:

- Watches two paths supplied at runtime (source file, status file).
- Re-parses the source file whenever its mtime increases.
- Writes the evaluation result to the status file, including the current environment and any errors.

Because the watcher uses `Unix.stat` and `Unix.sleepf`, it works on macOS, Linux, WSL, and native Windows builds that ship the OCaml Unix compatibility layer.

## Extending the generator

- Add new commands or tactics in `ast.ml`, then extend the evaluation logic in `prover.ml`.
- Supplement the parser (Menhir) by editing `parser.mly` and regenerating it with `dune build`.
- When introducing new types, update both `typing.ml` and the Lean translation path (`transformer.ml`, `quantum_ast.ml`).
- Remember to update documentation and add regression scripts under `generator/examples/`.

Refer back to this document for module entry points, and keep the architecture section current as new components (e.g. Coq exporters) land.
