# Linting PhysLean

`Linting` is the process of checking changes to the project
for certain types of stylistic errors. This process is carried out
by automatic scripts called `linters`.

PhysLean has a number of linters which check for various different things.
They can all be run on your local version of the project, but some of them
are also automatically run on pull-requests to PhysLean. These latter linters
must be passed before the pull-request can be merged with the main branch of the
project.

Below we summarize the linters PhysLean has, in each bullet point the initial `code snippet`
is how the linter can be run locally.

- `lake exe lint_all` (**A PR must pass this linter**): This linter
- `./scripts/lint-style.sh` (**A PR must pass this linter**): This linter
