# ACMD Next-Phase Advancement — CORRECTED DRAFT (2026-10-06)

**Status:** DRAFT. Not pushed to any public repo. Corrects the unmarked
"Next-Phase Advancement" draft Jeff supplied 2026-10-06.
**Honesty tier of this document:** T2/T5 — a research program proposal, not results.

## Changelog — what was fixed and why

| # | Original claim | Fix | Reason |
|---|---|---|---|
| 1 | "1.8 meV neutrino floor" (lower bound on Majorana mass) | REMOVED | Yukawas in D_F are input parameters, not derived quantities. A mass floor cannot be extracted from free parameters. Killed per ledger rule; returns only as a new entry supported by proof. |
| 2 | Dark-energy drift w(z), w_a ≠ 0 as ACMD "prediction" | REMOVED → refiled as open question | No derivation from T1 objects exists. Presenting it as a ledger entry was a physical prediction wearing formal clothes. |
| 3 | Higgs mass shift Δm_H² ∝ Tr(Φ_act²) in the a₂ coefficient table | REMOVED → "uncomputed" | The trace was never computed against our D_F; the shift was asserted, not derived. |
| 4 | Connes distance "0.4065 GeV⁻¹ ⇒ Electroweak Scale Anchor" | REMOVED the anchor claim | A numerical distance value does not anchor a physical scale without a derivation bridging finite geometry to the electroweak scale. None exists. |
| 5 | Flux written Φ_act throughout | → φ_act | Standing notation doctrine (Jeff's corrected re-issue): Φ is the ontological glyph; φ (lowercase) is modular flux. The original broke it. |
| 6 | "PCK32.9 – PCK32.12" Lean sequence | → mapped to real files / marked PROPOSED | `grep` over the codebase: zero hits for "PCK32" in any .lean file. The numbering is foreign. Targets below reference actual modules. |
| 7 | "Gate L Empirical Signature Ledger" | → "Gate L" marked PROPOSED terminology | Zero hits for "Gate L" in the codebase. "Gate G" exists (closed by `exists_activeDriver` in `ModularFlux.lean`). Gate L is a proposal, not an established gate. |
| 8 | Spectral-action table presented as derived expansion | → tier-labeled | The standard column (Chamseddine–Connes) is real literature (T2). The ACMD column was speculation presented as computation. Now labeled. |

---

## I. Non-Equilibrium Operator Algebra (T2 proposal — hand-verified shape, not machine-checked)

Under the 32-state decomposition H_F = H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c = ℂ³²,
the internal Dirac operator D_F and an active modular generator K take block
matrix representations (standard; cf. `Scaffold32.lean`, `FiniteSpectralTriple.lean`).

Since [D_F², D_F] = 0, for K_β = βD² the flux vanishes — this is the
machine-checked `thermal_flux_vanishes` (T1, `ModularFlux.lean`). The
non-equilibrium exchange flux is therefore carried by the active driver G:

> φ_act := i[G, D_F]  (lowercase φ, per doctrine)

**Proposed structural constraints on G** (conjectures, NOT proved):

- *Commutant constraint (proposed):* G commutes with the gauge representation
  π(a) for all a ∈ A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ). This is the gauge-invariance condition
  a driver must satisfy; it is a well-formed formal statement and a candidate
  T1 target, not an established theorem.
- *Active non-triviality (proposed):* G acts off-diagonally across chiral
  sectors (G₁₂ ≠ 0), so φ_act ≠ 0. Existence of *some* non-commuting driver is
  T1 (`exists_activeDriver`, `ModularFlux.lean`); the inter-sectoral block
  shape is proposed.

**Interpretation (T5):** the thermal phase-time flow dτ = ℏ/(k_B·T(x))·ds is an
interpretive gloss on non-equilibrium modular flow, not a derived identity.
It may guide intuition; it proves nothing.

---

## II. Lean 4 Formalization Targets (proposed — mapped to real modules)

No new numbering scheme is introduced. Proposed targets, each to live in a
named file:

1. **Driver commutant characterization** → `ModularFlux.lean` (extension).
   *Statement shape:* for G satisfying the commutant constraint, φ_act = i[G, D_F]
   is gauge-covariant. Status: proposed.
2. **Inter-sectoral driver construction** → `ModularFlux.lean` (extension).
   *Statement shape:* exhibit G with G₁₂ ≠ 0 and φ_act ≠ 0. Status: proposed.
   (Note: `exists_activeDriver` already gives *a* driver; this strengthens the shape.)
3. **φ_act trace identities** → new file `ActiveFlux.lean` (proposed).
   *Statement shape:* Tr(φ_act²) in terms of block components of G and D_F.
   Pure linear algebra; the most formalizable target in this document.
4. **Spectral-action flux coupling (numerical)** → `SpectralAction.lean` (extension, Tier 4).
   *Statement shape:* numerical evaluation of Tr f((D_A² + φ_act²)/Λ²) heat-kernel
   coefficients for concrete G. Numerical exploration, NOT proof.

**Explicit non-targets:** no mass predictions, no continuum limit, no Yang–Mills
gap claim. Those remain quarantined per the Q4 amendment (`BlockedQuestions.lean`).

---

## III. Spectral Action with Active Flux (Tier 4 — numerical exploration, not derivation)

The product Dirac operator modified by gauge-invariant active flux,
D_{A,φ}² = D_A² + φ_act² (schematic), can be explored numerically via
Seeley–DeWitt heat-kernel coefficients. Honest status of each coefficient:

| Coefficient | Standard term (T2, literature) | ACMD flux term (honest status) |
|---|---|---|
| a₀ | Volume ∫ d⁴x √g (Chamseddine–Connes) | Uncomputed. Would require fixing G and Λ. |
| a₂ | Einstein–Hilbert R + Higgs | Uncomputed. No derived shift exists. |
| a₄ | Yang–Mills F² + Gauss–Bonnet + H⁴ | Uncomputed. Any "self-coupling" language is premature. |

The original draft's contribution column has been struck in full. Rebuilding it
requires: (i) a fixed G satisfying the commutant constraint (target II.1–2),
(ii) an explicit heat-kernel computation (target II.4), (iii) tier labeling of
every step. Until then the table is a wishlist, not a result.

---

## IV. Empirical Signatures (none established)

**There are no ACMD empirical predictions at this time.** The original "Gate L
Empirical Signature Ledger" (neutrino floor, distance anchor, w(z) drift) has
been removed in full — see changelog items 1–4.

What a future empirical program would require, in order:

1. A fixed, physically-motivated G (not a free matrix).
2. A derivation bridging finite-geometry quantities to physical scales
   (the continuum/QFT rungs — see `whitepaper/qft-rungs-map-2026-10-06.md`).
3. A prediction stated *before* measurement, with falsification conditions.
4. Independent reproduction.

Until (1)–(3) exist, "Gate L" remains proposed terminology for a gate with no
content. Naming it does not open it.

---

## Standing boundaries (unchanged)

- Φ is ontological; φ is modular flux. No exceptions.
- Killed claims return only as new, weaker entries supported by proof.
- No public thet-logos action without Jeff's explicit approval.
- This draft is not pushed, not published, not submitted anywhere.
