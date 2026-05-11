# PLAN 93 - Dudko 2512 Virtual Molecule Roadmap

Status: PROPOSED
Progress: [#---------] 10%
Scope: Integrate Section 4 of `refs/2512.24171.pdf` into the repository's
planning layer without mislabeling it as the live operational frontier. This
plan records how Dudko's remaining unbounded satellite ql cases and the virtual
Molecule interpolation program should guide the residual `molecule_h_norm`
source-search effort.
Acceptance:
1. The repo has a stable plan document that distinguishes:
   - the current verified operational frontier,
   - the already-completed Problem 4.3 interface cutovers,
   - and Dudko's still-unformalized Section 4 research program.
2. The plan names the missing mathematical objects suggested by Section 4.5,
   rather than treating the existing Lean shell as already sufficient.
3. `plan/PLAN_00_tracker.md` references this file as a sidecar roadmap only,
   not as a replacement for `PLAN_88` / `PLAN_90` / `PLAN_91`.
Dependencies: `refs/2512.24171_section4_note.md`,
`Molecule/Problem4_3.lean`, `Molecule/PseudoSiegelDisk.lean`,
`Molecule/RenormalizationOrbit.lean`, `Molecule/Conjecture.lean`,
`plan/PLAN_00_tracker.md`, `plan/PLAN_20_problem43_local_norm_cutover.md`,
`plan/PLAN_88_dual_track_seed_or_non_singleton_localized_bridge.md`,
`plan/PLAN_91_nonvacuous_scaffold_remaining_theorems.md`
Stuck Rule: STUCK if this plan starts claiming that Dudko Section 4 has already
been formalized in the repo, or if it obscures the fact that the live frontier
is still the residual `Molecule.molecule_h_norm` program.
Last Updated: 2026-05-11

## Purpose

This plan exists to preserve an important distinction:

- the repo already has a Problem 4.3-shaped interface and several completed
  theorem-routing cutovers,
- but it does not yet formalize Dudko's remaining unbounded satellite ql cases
  or the virtual-Molecule interpolation regime.

So the value of `2512.24171` here is not an immediate Lean implementation
recipe. Its value is as a mathematically informed roadmap for the next
source-search abstraction beyond the current pseudo-Siegel / orbit shell.

## Current verified frontier

- `make check` for `Molecule.molecule_conjecture_refined` still reports the
  residual project-local axiom `Molecule.molecule_h_norm`.
- `PLAN_88` remains the governing route plan.
- `PLAN_90` / `PLAN_91` remain the day-to-day redesign theorem queue.

This plan does **not** replace any of the above.

## What is already done

### `PLAN_07`

`PLAN_07_dewrapper_ps_orbit.md` already de-wrapped pseudo-Siegel and orbit
assumptions into constructive interfaces.

### `PLAN_20`

`PLAN_20_problem43_local_norm_cutover.md` already localized the public
`Problem4_3` theorem route away from a global `h_norm` signature by routing
through:

- `FixedPointNormalizationData`
- `fixed_point_normalization_data_of_legacy`
- `problem_4_3_bounds_established_of_fixed_point_data`

This was a theorem-interface success, not a closure of Dudko Problem 4.3 in the
paper's full scope.

## What remains open from Dudko Section 4

### Track A - Remaining Problem 4.3 mathematics

The current code still lacks a source specific to the remaining **unbounded
satellite ql** cases. In repository terms, the gap is:

- not another wrapper decomposition pass,
- but a new producer/source that can justify pseudo-Siegel a priori bounds in
  the remaining satellite regime without bottoming out in
  `Molecule.molecule_h_norm`.

Primary current code touchpoints:

- `Molecule/Problem4_3.lean`
- `Molecule/PseudoSiegelDisk.lean`
- `Molecule/RenormalizationOrbit.lean`
- residual source seams in `Molecule/Conjecture.lean`

### Track B - Virtual Molecule regime

Section 4.5 points to a missing intermediate model between the current
pseudo-Siegel / orbit interfaces and a genuine non-axiomatic source. The repo
does not yet encode:

- satellite-copy chains `M(s)`,
- relative periods between consecutive copies,
- the split between virtual bounded-type satellite and virtual near-neutral,
- partially invariant virtual Julia sets,
- first-return control on the critical orbit through those virtual scales.

This is the main new planning content introduced by Dudko's note.

### Track C - Connection to the live frontier

The best current use of Dudko Section 4 in this repo is to guide the search for
a new upstream source class that could eventually feed the existing cutovers
already isolated by:

- `PLAN_88`
- `PLAN_90`
- `PLAN_91`
- sidecar carriers in `PLAN_80`, `PLAN_78`, and `PLAN_53`

That connection should be treated as mathematical guidance, not as a proof that
the correct source class has already been identified.

## Deliverables owned by this plan

- [x] Add `refs/2512.24171_section4_note.md`.
- [x] Record the mapping from Dudko Problem 4.3 to current modules.
- [ ] Keep a stable written roadmap for the virtual-Molecule program.
- [ ] Link the roadmap from `PLAN_00_tracker.md` as a reserve-only sidecar.
- [ ] When a concrete new producer class is named, hand off back to the active
      operational queue rather than growing this file into a theorem backlog.

## Non-goals

- This plan does not claim the repo already formalizes Dudko Problem 4.3.
- This plan does not replace `PLAN_88` as the governing frontier.
- This plan does not create a new theorem queue parallel to `PLAN_90` /
  `PLAN_91`.
- This plan does not count abstract speculation about virtual Molecule objects
  as progress unless it names a concrete producer class or exact model gap.

## Next handoff condition

The next meaningful activation step for this plan is:

1. identify a concrete producer class or model extension suggested by the
   virtual-Molecule picture, and
2. show how it can enter the existing source/cutover interfaces without
   collapsing back to the current blocked singleton/global route.
