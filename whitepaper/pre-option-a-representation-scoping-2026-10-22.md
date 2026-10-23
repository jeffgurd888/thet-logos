# Pre-Option-A Representation — the hypercharge seat (scoping charter)

Commissioned by Jeff, 2026-10-22 22:06 EDT ("build all the bricks we
need… full standard model" → bounded to the one buildable gap →
"Build the pre-Option-A representation brick now"). This brick attacks
SM-Match Track 1's priced gap #1 (dossier
`whitepaper/sm-match-2026-10-11.md`, §Priced gaps; queue entry standing
since 2026-10-15).

## The gap, exactly as the ledger states it

SM-Match Track 1 (`SMGaugeAlgebra.lean`) is PARTIAL. The algebraic
side matches (U(AF) = U(1)×SU(2)×U(3), unimodular subgroup
U(1)×SU(2)×SU(3), T1). The represented side is the corpus's Option-A
π, whose kernel is exactly the pure-color elements (`pi_ker_iff`:
π(a) = 0 ↔ a.u1 = 0 ∧ a.q = 0): M₃(ℂ) survives only locked to
electroweak, and the represented U(1) acts only on H_R — trivially on
left-handed fermions (`pi_u1_eL_trivial`), while SM hypercharge has
Y(e_L) = −1. **The represented U(1) is not hypercharge; the seat is
empty in Option-A.**

## The build

Construct the **pre-Option-A representation** π₀ of
AF = ℂ ⊕ ℍ ⊕ M₃(ℂ) on the corpus's finite Hilbert space (per
`FiniteSpectralTriple.lean` and the sector structure of
`SMFermions.lean`): the natural action Option-A was chosen over —
ℍ on the left-handed doublets, ℂ on the right-handed singlets (with
the conjugate action on antiparticle sectors), M₃(ℂ) acting genuinely
on the color triplets. Build it in the landed modules' own vocabulary;
import them unmodified.

## Targets (pre-registered)

- **T1 — π₀ exists.** π₀ is an algebra representation of AF on H_F
  (homomorphism, respecting the sector decomposition and the
  corpus's grading/J structure where those apply — state exactly
  which compatibility conditions are proved and which are not
  attempted).
- **T2 — Faithfulness.** ker π₀ = 0 (contrast Option-A's
  `pi_ker_iff`): in particular pure color acts nontrivially now.
- **T3 — The seat is occupied.** The ℂ-summand's U(1) under π₀ acts
  NON-trivially on the e_L sector — the Option-A obstruction
  (`pi_u1_eL_trivial`) is gone in π₀.
- **T4 — The hypercharge pattern (the prize; PARTIAL allowed).**
  Under the unimodularity condition, the surviving U(1) generator's
  eigenvalues on the one-generation sectors are proportional to the
  SM hypercharges: the eigenvalue RATIOS equal the Y ratios, with
  one overall normalization free. Fences inside the target: if the
  sector decomposition has to import the Y table to state the
  target, say so on the face — the claim is then (representation +
  unimodularity) ⇒ ratios, normalization an input. Any deviation of
  the eigenvalue pattern from the Y ratios is reported exactly,
  never rounded into a match.
- **Kill criterion (pre-registered).** If π₀ cannot be made an
  algebra representation on H_F compatibly with the structure the
  corpus already carries (grading, J, first-order condition where
  applicable), or if unimodularity in π₀ forces the U(1) back to
  triviality on e_L, the brick reports KILLED/PARTIAL with the
  obstruction proved or pinpointed — at win speed, same as a stand.

## Fences

- **K-PA1.** Finite representation theory only. No continuum, no
  dynamics, no manifold factor (the other priced route to the same
  gap; untouched by this brick either way).
- **K-PA2.** Hypercharge VALUES remain T2-cited (textbook NCG) unless
  T4 closes in its stated form; masses, couplings, generations are
  inputs throughout, untouched. This brick does not derive the
  Standard Model; at best it fills the representation seat Track 1
  left empty.
- **K-PA3.** SM-Match's verdicts change only on landing, by the
  parent, on verified text: Track 1 PARTIAL is the number to beat,
  and a PARTIAL or KILL here leaves it exactly as it stands.

## Price

M — a new representation construction on the existing finite spaces,
sibling scale to `SMGaugeAlgebra.lean` (374 lines). Candidate only;
parent verifies and lands. Bench: the Ghys filler yields (Jeff's
build-now ruling); it resumes from cache after.
