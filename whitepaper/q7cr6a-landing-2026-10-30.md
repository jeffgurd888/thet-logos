# Q7CR-6a — the C₇ shift action, registered

**Date:** 2026-10-30 · **Brick:** Q7CR-6a (S–M) per
`scoping-q7cr-6-linker-2026-10-30.md` §2. New module:
`ThetLogos.Q7C4R4Linker`. **Verdict: LANDED FULL** (strict 27 /
defs 6, parent-verified from disk; full-tree build green;
headlines' axioms exactly [propext, Classical.choice,
Quot.sound]). The strict count exceeds the 12–22 estimate; the
overage is transport/splitting helper lemmas the proofs forced,
not extra claims.

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.** Face labels per the scoping: **the action was
supplied by BONES under Jeff's 2026-10-30 delegation** (his
word: "supply") — it is labeled as supplied, superseded by any
different name from Jeff; it is NOT presented as Jeff's coinage.
**"via C4" survives only as "graded by C4."** No proved
statement in this line makes the C⁴ factor mediate between the
Q⁷ action and any R⁴ action (K-Q7CR-6c, fired at scoping, stands
at full rank); Jeff's headline stands untouched as his T5
interpretation on Q7CR-0's face.

## What landed

The supplied action, vetted sound at scoping (already latent in
the corpus), realized by specialization of the corpus's own
FluxTwist machinery at n = 6 — cite, not rebuild:

- `q7Shift` S₇ = `uniformShift (n := 6) 0`, the unweighted
  cyclic permutation matrix wpMat cyc₇ 1 with
  cyc₇ = `FluxTwist.cyc` = `finRotate 7`; the row convention
  fixed on the face and as a theorem: `(S₇ *ᵥ v) i = v (cyc₇ i)`.
- `q7Shift_pow_seven : S₇ ^ 7 = 1`, and faithfulness
  `q7Shift_pow_ne_one` for 1 ≤ k < 7 — exact order 7.
- The representation package **`q7Rep : Multiplicative (ZMod 7)
  →* Matrix.unitaryGroup (Fin 7) ℂ`** — the additive C₇
  presented multiplicatively (a `→*` domain carries the group
  operation multiplicatively; stated on the face), group law
  proved from S₇⁷ = 1, injective (`q7Rep_injective`): a genuine
  unitary action, not merely a named matrix.
- Unitarity **by citation** (`uniformShift_unitary` at θ = 0).
- Fourier diagonalization by specialization of
  `uniformShift_mulVec_fourierVec` at θ = 0: spectrum
  {ζ₇^m : m ∈ ZMod 7}, each eigenvalue once (pinned formally:
  nonzero eigenvectors, pairwise-distinct eigenphases).
- The Pontryagin side cited from the pin's own
  `AddChar.zmodAddEquiv` at n = 7 — the standard Q⁷DFT
  identification at this seat, cited, not rebuilt.
- The realified action via Q7CR-1a's `realifyOp`: `q7ShiftR`
  with (S₇ᴿ)⁷ = 1 by transport, commuting with the complex
  structure, eigenphase conjugate-pairing proved; the block
  form stated exactly as **four real isotypic blocks
  1 ⊕ 2 ⊕ 2 ⊕ 2** (trivial + χ₁⊕χ₆, χ₂⊕χ₅, χ₃⊕χ₄) — the
  seven-real-sectors statement is false and is nowhere written.
  The block form is stated with its supporting formal facts
  proved, as the brick priced ("stated").

## The standing weakness, on the face (verbatim-tier)

This is the **regular representation** — every character of C₇
exactly once. Its Fourier completeness is a property of the
regular action, not of the composite: any C₇ action's
diagonalization is Fourier; what is special here is only that
nothing is missing. Rejected alternatives recorded on the face
(U(7): vacuous; full S₇: no Pontryagin shortcut); the
Weyl/Heisenberg enrichment is NOT built (priced only on
demonstrated need from Q7CR-6c).

**Pin quirk recorded:** this Mathlib pin has no `NatCast
(Fin n)` instance, so the power law is stated in
permutation-power form `(S₇ ^ k *ᵥ v) i = v ((cyc₇ ^ k) i)`
rather than `v (i + k)`; exact order comes from the cycle
machinery. Mathematically identical content.

Bounded-commutator caveat (standing for this line): in finite
dimension the criterion is vacuous; the testable content is
spectrum, grading behavior, and the D² identity.

**Census: 7,508 → 7,535 strict / 7,586 → 7,613
attribute-inclusive / 263 → 264 modules** (recounted from
disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
