## Quick orientation for AI coding agents

This repository is a Lean 4 formalization of many physics topics (PhysLean). The goal of these instructions is to give an AI agent the immediate, actionable knowledge needed to make small, correct changes and run the common developer workflows.

### Big picture
- Language and toolchain: Lean 4 (see `lean-toolchain`). The project was developed against Lean v4.23.0 (see `README.md`).
- Single central entrypoint: `PhysLean.lean` — this file imports almost all library modules. New modules must be referenced here to be included in builds and some meta tools expect that.
- Source layout: files under `PhysLean/` map directly to module names. Example:
  - File: `PhysLean/Particles/FlavorPhysics/CKMMatrix/StandardParameterization/Basic.lean`
  - Module: `PhysLean.Particles.FlavorPhysics.CKMMatrix.StandardParameterization.Basic`

### Essential commands (run from repository root)
Use the Lean `lake` tool installed with Lean. Example commands for PowerShell:

```powershell
# fetch cached executables/deps
lake exe cache get
# build the project
lake build
# update dependencies
lake update
```

Many helper scripts are packaged as lake executables (run with `lake exe <name>`). Examples below.

### Common developer scripts and checks
- `lake exe check_file_imports` — verifies that files are correctly imported into `PhysLean.lean`. Run this after adding new modules.
- `lake exe type_former_lint` — enforces that type/Prop-forming definitions begin with a capital letter (naming convention enforcement).
- `lake exe hepLean_style_lint` — repository-specific text-style checks (double-empty-lines, non-initial double spaces).
- `lake exe stats` — outputs repository statistics.
- `lake exe openAI_doc_check <module|random>` — runs an OpenAI-based docstring checker. Requires `Lean_llm_fork` and `OPENAI_API_KEY` environment variable.
- `./scripts/lint-all.sh` — runs the full lint pipeline.

### Automation and meta files to inspect before editing
- `PhysLean.lean` — central module list; add imports here for inclusion and CI expectations.
- `PhysLean/Meta/AllFilePaths.lean` — used by meta-programs; useful when adding or renaming modules.
- `scripts/check_file_imports.lean` — the linter/tool that checks imports match files.
- `scripts/type_former_lint.lean` and `scripts/lint-all.sh` — show lint expectations and integration points.

### Conventions and patterns (concrete, codebase-observed)
- Module path mirrors directory structure and dotted Lean module name must match file path under `PhysLean/`.
- Small PRs are preferred. The README and contributing guidelines request incremental changes for easier review.
- Documentation lives alongside code in Lean docstrings; `PhysLean/Meta/Notes` and `docs/CuratedNotes` contain examples of how informal notes and HTML exports are structured.
- Many proofs use local tactics from `PhysLean.Meta.TransverseTactics`. Inspect `PhysLean/Meta` for meta-programming and tactic helpers before changing proofs that rely on custom tactics.

### Integration points and external deps
- The project depends on external Lean packages resolved by `lake`. Use `lake update` to refresh.
- `scripts/openAI_doc_check` requires `https://github.com/jstoobysmith/Lean_llm_fork` and an environment variable `OPENAI_API_KEY` to be set. Example (PowerShell):

```powershell
$env:OPENAI_API_KEY = 'your_key_here'
lake exe openAI_doc_check PhysLean.SpaceAndTime.Space.Basic
```

### Minimal checklist for a change (use as a pre-PR checklist)
1. Add or edit Lean files under `PhysLean/...` following the module naming scheme.
2. If adding a new top-level module, add an `import` to `PhysLean.lean` (or the appropriate sub-import grouping).
3. Run `lake exe check_file_imports` and `lake build` locally.
4. Run `./scripts/lint-all.sh` or the specific linters (`type_former_lint`, `hepLean_style_lint`).
5. Keep PRs small and self-contained; link to related `PhysLean.Meta.*` helpers if you changed proofs or meta behavior.

### Examples to reference
- Proof-style and tactic usage: inspect `PhysLean/Meta/TransverseTactics.lean` and `PhysLean/Meta/Basic.lean`.
- Naming/type convention example: `PhysLean/Units/WithDim/Energy.lean` (types and units naming patterns).
- Physics examples and documentation style: `PhysLean/Electromagnetism/MaxwellEquations.lean` and `PhysLean/QuantumMechanics/OneDimension/HarmonicOscillator/Basic.lean`.

If anything above is unclear or you want additional examples (e.g., how imports are grouped inside `PhysLean.lean` or how a specific script is built), tell me which area and I'll expand or iterate.
