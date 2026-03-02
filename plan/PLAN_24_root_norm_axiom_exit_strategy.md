# PLAN 24 - Root `h_norm` Axiom Exit Strategy

Status: ACTIVE
Progress: [#---------] 10%
Scope: Remove the final dependency on `Molecule.molecule_h_norm` by replacing remaining global-normalization theorem inputs with local fixed-point/spectral contracts.
Acceptance: `check_axioms` for `molecule_conjecture_refined` no longer lists `Molecule.molecule_h_norm`.
Dependencies: `Molecule/Conjecture.lean`, `Molecule/FeigenbaumFixedPoint.lean`, `Molecule/HyperbolicityTheorems.lean`, `Molecule/Problem4_3.lean`
Stuck Rule: STUCK if every route still requires deriving data from the contradictory global statement `∀ K, ...`.
Last Updated: 2026-03-02

## Work Log

- [x] Added plan.
- [ ] Isolate exact proof edges still forcing `h_norm` in the top theorem path.
- [ ] Introduce local-contract theorem variants for those edges.
- [ ] Switch top theorem chain to the local-contract variants.
- [ ] Re-run axiom audit and close PLAN_11.
