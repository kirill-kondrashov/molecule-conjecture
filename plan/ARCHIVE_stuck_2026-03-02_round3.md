# ARCHIVE - Stuck Plans (2026-03-02 Round 3)

Archived at: 2026-03-02

## Removed Stuck Plans

1. `PLAN_16_nonexplosive_top_theorem_path.md`
   - Reason: The zero-arg top theorem currently still requires contradiction-based witness filling via
     `molecule_h_norm_inconsistent`; no direct constructive witness path exists yet in current dependencies.
2. `PLAN_19_top_theorem_refactor_without_global_norm.md`
   - Reason: After cutover and axiom audits, remaining dependency is still `Molecule.molecule_h_norm`.
     No non-circular non-ex-falso route has been established in the current theorem chain.

## Replacement Plans

- `PLAN_22_hyperbolicity_local_fixedpoint_cutover.md`
- `PLAN_23_zero_arg_top_theorem_without_exfalso.md`
