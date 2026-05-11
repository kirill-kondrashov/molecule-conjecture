# PLAN 92 - Main Cardioid Boundary First Homology Seam

Status: PROPOSED
Progress: [#---------] 10%
Scope: reserve sidecar plan for a credible homology connection at the current
repository state. The active slice/BMol scaffold is still too discrete for
meaningful homology: current chart/operator packages only expose finite or
discrete sets, so at most `H_0`-type bookkeeping is honest there. The first
plausible nontrivial homology seam instead lies in the global geometry already
present in `Molecule/Mol.lean`, especially the main-cardioid boundary
parameterization and the compact/connected `MolSet` results.

Acceptance:
1. Do not count homology of finite chart images such as `{0}`, `{0, 1}`, or
   `{0, 1, 2}` as meaningful progress beyond discrete `H_0`.
2. Identify a concrete object already present or nearly present in
   `Molecule/Mol.lean` whose first homology could plausibly be nontrivial.
3. Prefer a first-homology seam (`H_1`) before any higher-homology claim.
4. Either expose a theorem-level loop/circle-type proxy strong enough to make
   an `H_1` statement plausible, or record the exact missing formalization
   debt.
5. Keep this plan reserve-only unless it yields either:
   - a real feedback point into the active scaffold/model redesign plans, or
   - a precise explanatory obstruction about why the current topology is too
     thin for nontrivial homology.

Dependencies: `Molecule/Mol.lean`,
`Molecule/BMol.lean`,
`Molecule/BanachSlice.lean`,
`Molecule/Conjecture.lean`,
`plan/PLAN_00_tracker.md`,
`plan/PLAN_90_separated_operator_action_redesign.md`,
`plan/PLAN_91_nonvacuous_scaffold_remaining_theorems.md`

Stuck Rule: STUCK if every candidate homology object is either:
- a finite/discrete chart image with only `H_0`,
- a set with no formal boundary/loop/circle-type theorem nearby, or
- disconnected from the active proof program with no model/topology
  consequence.

Last Updated: 2026-03-14

## Research Program

- [ ] Record the exact negative result for the current slice scaffold:
  only discrete `H_0`-level information is currently honest.
- [ ] Isolate the first plausible nontrivial homology target in
  `Molecule/Mol.lean`.
- [ ] Decide whether the right target is:
  - the main-cardioid boundary,
  - a quotient/circle-type proxy built from `MainCardioidParam`, or
  - a future non-discrete slice neighborhood after model/topology redesign.
- [ ] If the main-cardioid boundary is the best target, expose the minimal
  theorem package that makes `H_1` plausible:
  - a boundary set definition,
  - a loop or circle-type parameterization,
  - a non-contractibility or nontrivial-cycle proxy.
- [ ] Record whether the resulting homology seam is:
  - explanatory only, or
  - useful as a design signal for `PLAN_90` / `PLAN_91`.
- [ ] If no such seam survives, close the plan as explanatory-only and return
  to the active scaffold/model-topology route.

## Priority Order

1. Negative audit of current slice-side homology
2. Main-cardioid boundary / `MainCardioidParam` first-homology seam
3. Feedback into `PLAN_90` / `PLAN_91` model-topology redesign
4. Higher homology only after a credible `H_1` object exists

## Route Progress

| Route | Current State | Progress |
|---|---|---|
| Slice-side homology audit | Current slice/domain/chart/operator objects are finite or discrete, so the only honest invariant in sight is `H_0`. | [###-------] 30% |
| Global geometry candidate | `Mol.lean` already has a main-cardioid boundary parameterization together with compactness/connectedness results for `MolSet`, but no theorem yet identifies a circle-type boundary object or computes `H_1`. | [###-------] 30% |
| Proof-program relevance | This is a reserve explanatory/model-diagnostic sidecar, not part of the active elimination queue unless it feeds back into scaffold/model redesign. | [#---------] 10% |

## Notes

- Current negative evidence:
  - `BMol` still carries a discrete placeholder topology.
  - `slice_chart` is constant.
  - `slice_chart_refined` and `slice_chart_multivalued` only yield finite
    chart images in the current model.
  - So any current slice-scaffold homology beyond discrete `H_0` would be
    artificial.
- Plausible positive seam:
  - `Molecule/Mol.lean` defines `MainCardioid`.
  - `MainCardioidParam` already exposes a boundary-style parameterization.
  - `MolSet` is already proved compact and connected.
  - The first honest homology target is therefore likely an `H_1` statement
    for a formalized main-cardioid boundary or circle-type proxy, not a
    homology statement about the current slice scaffold.
- Relationship to active plans:
  - `PLAN_90` / `PLAN_91` remain primary.
  - This plan only becomes operationally important if it isolates a missing
    non-discrete/topological object that the active scaffold redesign really
    needs.
