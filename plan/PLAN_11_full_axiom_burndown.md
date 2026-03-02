# PLAN 11 - Full Axiom Burndown

Status: ACTIVE
Progress: [#########-] 90%
Scope: Remove all remaining `molecule_h_*` axioms and keep zero-arg top theorem.
Acceptance: `check_axioms` output contains no `Molecule.molecule_h_*` entries.
Dependencies: PLAN_18, PLAN_22, PLAN_23, PLAN_24
Stuck Rule: STUCK if PLAN_24 becomes STUCK.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Eliminated all top-level `molecule_h_*` dependencies except one.
- [x] Added localized-slice-data cutover theorem route.
- [ ] Eliminate final root dependency `Molecule.molecule_h_norm`.
