# RG-1 — The Blocked Measure Leaves the Wilson Line (Negative)

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/LatticeBlockingFlow.lean` (strict 55, defs
and instances 21, 887 lines, zero `sorry`, zero
`native_decide`; main-tree build green, 3,559 jobs,
parent-verified). **Parts of the Clay Yang–Mills statement
closed by this landing: 0.** This is a negative verdict,
reported at the same volume as a positive one: at the seat
below, the factor-2 blocked Gibbs measure is **not** a
coarse-lattice Gibbs measure at any coupling, for every
β > 0. The renormalization trajectory leaves the Wilson line
immediately; a running coupling β′(β) is a projection of the
flow, not the flow.*

## The headline

The corpus has owned the *blocking* since Pitch 4 Stage 2
(`LatticeBlocking.lean`): factor-2 decimation by path-ordered
link products, gauge covariance, Gibbs pushforward at every
β, effective-action existence. What it did not own was any
statement about the *flow* — and the module's own fenced
question, whether the blocked measure is again a Gibbs
measure on the coarse lattice at some β′, is now settled
negatively at a fully explicit seat:

> **`rg1_blocked_not_coarse_gibbs`** — seat: G₀ =
> `Multiplicative (ZMod 2)`, representation the sign
> character into `unitaryGroup (Fin 1) ℂ` (d = 1); fine
> lattice `Fin 2` with all shifts `Equiv.swap 0 1`; coarse
> lattice `Fin 1` with identity shifts; blocking
> `ι = fun _ => 0` (factor 2); Haar probability
> `(2:ℝ≥0∞)⁻¹ • count`. For every β > 0, there is **no** β′
> making the blocked measure a coarse Gibbs measure.

Axiom sets on the headline, both corollaries, and both
expectation theorems: exactly `[propext, Classical.choice,
Quot.sound]`.

## The mechanism

Fine plaquettes factor as group elements `w_μ·w_ν` in the
blocked links, so the fine action collapses to `S_β(U) =
2β·effAction(blockMap U)` with the explicit multi-link
coupling `effAction = Σ_{μ<ν}(1 − sgn w_μ sgn w_ν)`. Two
indicator observables separate the measures exactly: at
every β′ both coarse expectations equal **1/16** (the coarse
action vanishes identically at this seat — the degeneracy
is disclosed on the module's face, §6), while the blocked
expectations are `1/(16·Z_β)` and `exp(−12β)/(16·Z_β)`.
A single β′ matching both would force `exp(−12β) = 1`,
contradicting β > 0. Corollary `rg1_blocked_mass_ratio`:
the exact blocked mass ratio is `exp(−12β)`.

The abelian character of the seat was the registered risk —
the scoping warned the phenomenon might need a nonabelian
group. It does not: the separation survives head-on at the
abelian seat, and no fallback was needed.

## The fence

This is a **seat theorem**: one finite group, one
representation, one blocking, settled completely. It closes
the fenced `BlockedGibbsIsCoarseGibbs` question *negatively
at this seat*; it does not prove the blocked measure leaves
the Wilson line for every group or every blocking scheme,
and it constructs no flow — the multi-link coupling in the
effective action is exhibited at the seat, not developed
into a trajectory theory. RG-2 (the plaquette-matched
projection β′(β)) is untouched and remains priced. Mission
Step 4 now reads precisely: **blocking owned, flow zero,
and the one-coupling closure of the flow disproved at a
seat.** NO CLAIM; dials 0/4.

## Census effect

Strict 6,288 → **6,343**; attribute-inclusive 6,366 →
**6,421**; modules 213 → **214**; `sorry` placeholders
unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
