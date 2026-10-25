# Fuzzy Ball Gauntlet — the structural break of a sphere, recorded against a thermal matrix

**Date:** 2026-10-25. **Commission:** Jeff Gurd — "build it and run the
gauntlet… but build it into a fuzzy ball." Origin: the vision fragment
*the gravitational atomic spectral bridge* (`your_files/vision-fragment-
gravitational-atomic-spectral-bridge-2026-10-25.md`, T5): the structural
break geometry of a sphere, the break's "shadows" recorded against our
thermal matrix.

**Tier: EXHIBIT / computation.** Exact finite arithmetic (rational
spectra, float64 traces) on the declared finite model below. **This is
not a Lean theorem and no part of it enters the declaration census.**

**Artifacts:** `~/workspace/fuzzy-ball-gauntlet/fuzzy_ball_gauntlet.py`
(script), `results.json` + `shadows_data.json` (numbers), `shadows.png`
(plot of ΔΘ(t) vs t, log-x).

---

## 1. The construction (declared exactly)

**Fuzzy sphere (Madore).** At spin j the angular spectrum is
{l(l+1) with multiplicity (2l+1), l = 0..2j} — the exact round-sphere
spectrum, truncated. Total modes (2j+1)². Headline seat j = 8 (289
modes); cross-check j = 4 (81 modes). Heat trace
Θ(t) = Σ (2l+1) e^{−t·l(l+1)}; spectral gap 2 at both spins.

**Fuzzy ball.** K = 5 concentric shells, radii r_k = k/5
(k = 1..5: r = 1/5, 2/5, 3/5, 4/5, 1). Shell k carries angular modes
l = 0..L (L = 8) with eigenvalues l(l+1)/r_k² and multiplicities (2l+1)
— 81 modes per shell, **405 modes** total. Θ_B(t) = Σ over all shells
and modes of e^{−tλ}. Unbroken spectral gap: **2** (the l = 1 modes of
the outer shell).

> **Declared on its face:** the ball is an angular spectrum per shell
> with **no radial kinetic term** — a shell-stack (sediment) model, not
> a continuum ball. Shells do not talk to each other; the only radial
> structure is the 1/r_k² blue-shift of inner shells.

**Breaks** (each declared exactly, as a mode-removal operation; the
outer shell is k = 5, r = 1, eigenvalues l(l+1)):

- **A — LUNE BREAK (m > 0 half), outer shell.** Per l, remove l modes
  (the m = 1..l half), keep l+1.
- **B — MIRROR LUNE (m < 0 half), outer shell.** Per l, remove l modes
  (the m = −l..−1 half), keep l+1. A geometrically different break
  from A.
- **C — CAKE-RING BREAK.** Remove the outer shell entirely (the top
  stratum decapitated).
- **D — INTERIOR CRACK.** Remove the middle shell (k = 3, r = 3/5)
  entirely.
- **E — SAME-COUNT CONTROL.** Remove from the outer shell the same
  *number* of modes as A, taken as whole top-l shells filled from the
  highest l downward (l = 8 whole: 17; l = 7 whole: 15; 4 of l = 6,
  split by m from the top).

**The shadow.** For each break, ΔΘ(t) = Θ_unbroken(t) − Θ_broken(t)
= Σ over *removed* modes of e^{−tλ}, recorded on a log t-grid,
t ∈ [10⁻³, 10], 200 points. Also recorded per break: Δa₀ = removed mode
count; Δa₂ = first spectral moment of the removed set (Σ of removed
eigenvalues, exact rational); the broken ball's spectral gap; the
maximum relative shadow max_t ΔΘ(t)/Θ_unbroken(t).

---

## 2. Pre-registered claims (written before the results section)

- **C1.** Every break's shadow is strictly positive for all t > 0:
  removing modes strictly lowers the heat trace.
- **C2.** Breaks A and B cast **identical** shadows at every t — the
  same removed spectrum — despite being geometrically different
  breaks. The thermal matrix records the spectrum, not the geometry
  (finite non-uniqueness, exact).
- **C3.** Break E (same removed count as A) casts a **different**
  shadow from A at some t, while sharing Δa₀: the shadow sees the
  removed spectrum's *shape*, not just its size.
- **C4.** C and D are distinguishable by their shadows at large t.
  Both remove exactly one zero mode, so both shadows → 1 as t → ∞;
  the approach is governed by the smallest *positive* removed
  eigenvalue — 2 for C (mult 3), 2/r₃² = 50/9 for D (mult 3) — so the
  pre-registered ordering is **ΔΘ_C(t) > ΔΘ_D(t) at large t**, with
  ΔΘ_C − ΔΘ_D ~ 3e^{−2t}.
  *Correction logged in advance of the verdict:* the commissioning
  brief guessed "D removes smaller eigenvalues than C." Under the
  declared construction that is inverted — the crack shell's modes
  are blue-shifted by 1/r₃² = 25/9, so D removes *larger* nonzero
  eigenvalues than C. C4 is verdicted on the ordering stated here,
  derived from the construction, not on the brief's guess.
- **C5.** The lune break A preserves the ball's spectral gap: A keeps
  l+1 ≥ 2 modes at every outer l (in particular l = 1 keeps its m ≤ 0
  modes at λ = 2) and touches no inner shell, so the smallest positive
  eigenvalue of the broken spectrum equals the unbroken gap, 2.

---

## 3. Results

Fuzzy sphere seats: j = 4 → 81 modes, Θ(1) = 1.4184426386, gap 2;
j = 8 → 289 modes, gap 2 (at t = 1 the l ≥ 9 tail contributes below
float64 resolution, so Θ(1) prints identically — a float remark, not
an identity claim; the counts and spectra are exact rationals).

Fuzzy ball: 405 modes, Θ_B(1) = 5.5622868103, unbroken gap **2**.

| Break | Δa₀ (removed) | Δa₂ (Σ removed λ) | gap before → after | shadow max (grid) | shadow at t = 10 | max rel. shadow |
|---|---|---|---|---|---|---|
| A lune (m>0) | 36 | 1500 | 2 → 2 | 34.5395 | 2.061×10⁻⁹ | 0.1797 |
| B mirror lune (m<0) | 36 | 1500 | 2 → 2 | 34.5395 | 2.061×10⁻⁹ | 0.1797 |
| C cake-ring (outer shell) | 81 | 3240 | 2 → 25/8 | 77.8447 | 1.0000000062 | 0.4399 |
| D interior crack (shell 3) | 81 | 9000 | 2 → 2 | 72.6314 | 1.0 | 0.2325 |
| E same-count control | 36 | 2232 | 2 → 2 | 33.8376 | 1.579×10⁻¹⁸² | 0.1262 |

Claim-specific numbers:

- **C2:** the removed multisets of A and B are identical as sorted
  (eigenvalue, multiplicity) lists over exact rationals — verified
  symbolically, not by float closeness. Float shadow difference:
  exactly 0.0 at all 200 grid points.
- **C3:** Δa₀(A) = Δa₀(E) = 36, but Δa₂ differs (1500 vs 2232) and
  the shadows differ: max |ΔΘ_A − ΔΘ_E| = **6.9755**, attained at
  **t ≈ 0.02933** (ΔΘ_A above ΔΘ_E there — E's removed set is heavier
  at the top, so its shadow initially falls faster).
- **C4:** ΔΘ_C(t) − ΔΘ_D(t) > 0 on the *entire* grid, not only the
  tail; its minimum on the grid is 6.183×10⁻⁹ at t = 10, matching
  the pre-registered asymptotic 3e^{−2t} = 6.183×10⁻⁹. At t = 10:
  ΔΘ_C = 1.0000000062, ΔΘ_D = 1.0 (D's tail correction 3e^{−(50/9)·10}
  ≈ 2×10⁻²⁴ is below float64 resolution against 1).

---

## 4. Verdicts

- **C1 — STANDS.** Every break's shadow is strictly positive at all
  200 grid points. Grid minima: A/B 2.061×10⁻⁹, C 1.0 (attained at the
  tail, →1 from above), D 1.0, E 1.579×10⁻¹⁸² — all > 0. (Also forced
  analytically: each shadow is a nonempty finite sum of exponentials.)
- **C2 — STANDS.** A and B are geometrically different breaks with
  exactly the same removed spectrum and exactly the same shadow. The
  thermal matrix cannot tell a lune from its mirror. Finite, exact
  non-uniqueness — the drum moral, at 405 modes.
- **C3 — STANDS.** Same count, different shadow: Δa₀ alone does not
  determine the shadow; Δa₂ and the full removed spectrum do the
  seeing. Peak A–E separation 6.9755 at t ≈ 0.0293.
- **C4 — STANDS** (on the ordering pre-registered in §2; the brief's
  guessed direction was inverted and is corrected on the record in
  §2). Decapitation and interior crack are distinguishable at large
  t, and in fact at every t on the grid: the crack's shadow sits
  strictly below the decapitation's, both settling to the same
  zero-mode floor of 1.
- **C5 — STANDS.** Gap 2 → 2 under the lune break A, exactly as
  pre-registered. (The only break that moves the gap is C, 2 → 25/8:
  with the outer shell gone, the softest surviving mode is l = 1 on
  shell 4.)

**Gauntlet score: 5 STANDS, 0 KILLED.**

---

## 5. Fences

- **EXHIBIT / computation tier (T4-exact arithmetic on a declared
  finite model).** Not a Lean theorem; nothing here is T1, nothing is
  added to the corpus census, and no module was touched.
- **No gravity content.** "Quantum gravity shadow" is Jeff's name for
  the heat-trace difference ΔΘ(t) and nothing more is claimed.
  Conical defects and 2+1-dimensional gravity are literature framing
  around the lune picture (T4), not content of this computation; the
  corpus still holds **zero gravity objects**, dial #2 unmoved,
  NO CLAIM on any Millennium problem.
- **The model is a sediment stack, not a ball:** shells are
  kinematically independent (no radial kinetic term, no inter-shell
  coupling). A continuum ball, a coupled shell stack, or a
  noncommutative radial direction would each be a new entry, priced
  separately.
- **What the gauntlet actually shows** is narrower and, at its tier,
  solid: on a finite fuzzy geometry, a thermal record (the heat
  trace) sees exactly the removed spectrum — its size (C3), its
  softest mode (C4), its gap (C5) — and is blind to the geometry
  that produced it (C2). The shadow is real; the shadow is not the
  sphere.
