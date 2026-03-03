# PLAN 25 - Core Assumption Decomposition

Status: DONE
Progress: [##########] 100%
Scope: Replace monolithic `molecule_core_assumptions` with decomposed, locally consumable theorem/axiom interfaces and reduce dependency surface on `molecule_conjecture_refined`.
Acceptance: `check_axioms` for `Molecule.molecule_conjecture_refined` no longer lists `Molecule.molecule_core_assumptions`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/Problem4_3.lean`, `Molecule/BoundsToHyperbolicity.lean`, `Molecule/GlobalAnalyticity.lean`
Stuck Rule: STUCK if every decomposition still requires re-introducing an equally strong monolithic root axiom.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [x] Split `MoleculeCoreAssumptions` into minimal independent contracts consumed at each theorem edge.
- [x] Rewire `molecule_hypothesis_pack` to consume decomposed contracts.
- [x] Re-run `check_axioms` and confirm the root symbol `molecule_core_assumptions` is gone.

## Initial Implementation Notes

- Current zero-arg route avoids `molecule_h_norm`, all `molecule_h_*` roots,
  and the monolithic `molecule_core_assumptions` symbol.
- Remaining work moved to iterative burndown of decomposed `molecule_core_*` axioms.
