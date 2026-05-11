# PLAN 11 - Full Axiom Burndown

Status: DONE
Progress: [##########] 100%
Scope: Historical burndown of the older multi-axiom `molecule_h_*` frontier down
to the current single residual normalization axiom while keeping the zero-arg
top theorem.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` contains
no project-local `Molecule.molecule_h_*` entry other than the residual
`Molecule.molecule_h_norm`.
Dependencies: PLAN_18, PLAN_22, PLAN_23, PLAN_24
Stuck Rule: STUCK if PLAN_24 becomes STUCK.
Last Updated: 2026-04-30

## Work Log

- [x] Added plan.
- [x] Eliminated all top-level `molecule_h_*` dependencies except one.
- [x] Added localized-slice-data cutover theorem route.
- [x] Reduced the old frontier to the residual normalization dependency
  `Molecule.molecule_h_norm`.

## Current Outcome

- The older multi-axiom `molecule_h_*` frontier was collapsed.
- The current zero-argument theorem still lists the single residual project-local
  normalization axiom:
  - `Molecule.molecule_h_norm`
- Later plans (`PLAN_85` onward, with the active program in `PLAN_88` /
  `PLAN_90` / `PLAN_91`) own the remaining work.
