# GATE-B2′ LANDING DOSSIER — 2026-11-02

**Item:** GATE-B2′ (SHELF-7b-disc chain, GATE-B) — the forward
inclusion of the disc spectral mapping theorem, in the live
interior form frozen by 7B-PIN-2.

## VERDICT: FULL — no PARTIAL seam triggered

**Artifact:** `lean/ThetLogos/HfcDiscForward.lean` —
strict 12, defs 0 (low end of the 12–25 band). Verified by
the coordinator in the main tree (build green, 2983 jobs);
headline and sharp-scale auxiliaries on exactly
`[propext, Classical.choice, Quot.sound]`.

**Headline:** `shelf7bB2ForwardInterior_proved : ∀ (a : A)
(f : ℂ → ℂ) (R : ℝ), Shelf7bB2ForwardInterior a f R` —
for `DiscHolomorphic f R` and `spectralRadius < R`, at
every interior radius `R₀` and every `lam ∈ spectrum ℂ a`:
`f lam ∈ spectrum ℂ (hfcDisc a (discCoeff f R₀))`. The
forward inclusion of the disc spectral mapping theorem
holds at the spectral scale, in the interior presentation
that GATE-B1's kill forced.

**Route (as built):** the norm-scale bound replaced by the
pin's own spectral radius (`spectralRadius_eq_of_unital`);
the scalar identity is GATE-B1's corrected B1c at
`‖lam‖ < R₀`; 8a §8's factorisation lemmas consumed as-is;
the sharp-scale work is the brick's own — B1d transported
to the interior radius by restriction of holomorphicity,
tail summability at an intermediate scale via B1d's Gelfand
ingredient (no Gelfand re-derived), and 8a's `hfcDisc_add` /
`hfcDisc_mul` re-proved at the sharp scale
(`hfcDisc_add_of_summable`, `hfcDisc_mul_discFactor_of_summable`),
yielding `scalarEval_mem_spectrum_sharp`. 8a's own forward
lemma does NOT match the hypothesis shape (it needs
`‖a‖ < R`) — steps 3–5 did not collapse, as the pack allowed.
The REFUTED frozen forms are neither consumed nor cited as
live.

**Consequence:** the registered trigger for GATE-B3′ (the
disc spectral mapping EQUALITY, `Shelf7bDiscInterior`) is
met — B3′ fires. Its reverse inclusion is the hard
direction; K-GELFAND-SUBALGEBRA binds its route (characters
of the polynomial closure see the filled spectrum — that
route cannot prove reverse inclusion).

## Fences

NO CLAIM; all dials 0/4. 7b-in-full remains pin-blocked
(FULL-1–FULL-4); the disc chain runs under its own name.

**Census after landing: 12,174 strict / 12,548 total / 415 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
