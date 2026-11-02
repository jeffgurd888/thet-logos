# RES-2b LANDING DOSSIER — (a4) perturbation finiteness — 2026-11-02

**Item:** RES-2b (RES line optional, registered in the
resonance scoping as RES-2's stretch clause (a4), expressly
left untouched by RES-2). Fired under the 2026-11-01 unpark
steering (optionals as lanes allow).

## VERDICT: LANDED FULL — the RES line is now complete including its optional clause

**Artifact:** `lean/ThetLogos/SumResonancePerturbation.lean`
— strict 17, defs 5. Verified by the coordinator in the
main tree (build green); all five headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

Both faces of (a4) are frozen and proved finite:
`pertExcSet_finite` (the collCount-increase form) and
`newCollSet_finite` (the new-collision-through-j₀ form),
tied by `new_collision_form`: any perturbed collision not
already in `b` involves j₀ on exactly one side — "through
j₀" is forced by the perturbation's shape, not an extra
restriction. Both sets are trapped in the explicit finite
candidate finset.

**The degenerate-case finding (asked by the pack, answered
by proof, on the module's face):** the cross candidate
equations are `t = a i' + b j' − a i − b j₀` — coefficient
of t exactly 1, unique solution. The only t-independent
candidates are both-j₀ collisions, where t cancels (the
0 = 0 shape); `both_j0_t_independent` proves those hold
for the perturbation iff they hold for `b` — never new,
never count-raising. **The degenerate case is real but
inert; finiteness is unconditional, no extra hypothesis.**
Coincidences in this counting are destroyed by perturbing
one tone off a finite exceptional set — the scoping's
stability statement, now T1.

## Fences

NO CLAIM — abstract finite combinatorics; no measured
number derived or fitted; K-RES-1/K-RES-2 fences on the
module's face. No dial moves.

**Census after landing: 12,441 strict / 12,867 total / 430 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
