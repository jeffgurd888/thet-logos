# Bridge Span 4 — the twist-corrected reality prescription (dossier)

**Date:** 2026-10-07 · **Lead tier: T4** (numerical) + **T1** (Lean extension, machine-checked)
**Instrument:** `scripts/reality_span4_lab.py` (seeds 2026 / 202607)
**Results:** `scripts/reality-span-4-results.md`, `scripts/reality_span4_scatter.png`
**Predecessors:** `whitepaper/bridge-span-1-twist-2026-10-07.md` (flow twist: KILLED);
`whitepaper/bridge-span-2-involutive-twist-2026-10-07.md` (grading flip: STANDS);
`whitepaper/bridge-span-3-krein-2026-10-07.md` (Krein structure: primary STAND, single-H η KILLED)
**Lean:** `lean/ThetLogos/TwistedTriple.lean` §9 (extends §§1–8, builds green, zero sorrys)
**Git:** Lean §9 in local commit `3de9d9f`; numerical lab in local commit `75b9211` (NOT pushed)
**Status:** dossier drafted 2026-10-07.

## What this span is

Span 3 closed its own admission price with a precise algebraic character:
the twisted fluctuation preserves ρ-self-adjointness (`R D̃_ρᴴ R = D̃_ρ`)
exactly when the twisted 1-form is ρ-real (`R Ã_ρᴴ R = Ã_ρ`, needs
imaginary coefficients) — Span-3 §P.7, residuals 4.920 / 0.000. The
obstruction ledger had carried the **twist-corrected reality prescription**
since Span 1: self-adjointness of a twisted 1-form needs CM-regularity
plus a coefficient constraint (the T5 pin `AntilinearJCompat` in §8,
undischarged). This span implements and tests the DLM-correct version of
that prescription in ρ-language, both as Lean theorems and as a
definitive numerical iff.

**Verdict up front: STAND.** The twist-corrected reality prescription
closes both ways: the doubled fluctuation `F̃ = D̃ + Ã + ε₁ • Jterm` is
Krein-symmetric ⟺ the doubled 1-form `Ã = fromBlocks A 0 0 A′` is
ρ-real — i.e., exactly when `A′ = Aᴴ`. Lean proves the full conditional
iff (7 new theorems, zero sorrys, no new axioms); the numerical lab shows
a clean iff beyond sampling (kernel equality as real subspaces) plus a
perfectly monotone √2 boundary map. NO new T5 pin on either direction.

---

## (a) Exact setup and conventions **(T4 — numerical; definitions exact)**

Carried binding from Spans 1–3:

- Doubled Hilbert space `H⊕H = ℂ⁶⁴`, doubled Dirac `D̃ = block_diag(D_F, D_F)`.
- Fundamental symmetry `R = R_swap = [[0, I₃₂],[I₃₂, 0]]` (real symmetric,
  `R² = I`, `Rᴴ = R`) — Span 3's DLM transplant, standing.
- Doubled representation `π̃(a,a′) = block_diag(π(a), π(a′))`.
- Doubled real-structure action `J̃act(X) = Ũ conj(X) Ũᵀ`,
  `Ũ = block_diag(U_J, U_J)` (CONJUGATE-based, binding — the convention
  the whole bridge uses).
- The fluctuated Dirac under test: `D̃_f = D̃ + Ã + J̃act(Ã)` — the
  J̃-term is **always included** (Lean: packaged as
  `doubledFluctuation D A A' Jterm eps1 = D̃ + Ã + ε₁ • Jterm`).
- Residuals: `r1 = ‖R Ãᴴ R − Ã‖_F` (ρ-reality of the 1-form),
  `r2 = ‖R D̃_fᴴ R − D̃_f‖_F` (ρ-symmetry of the fluctuation).

**New T2 def (Lean §9, binding):** `IsRhoReal η A := η * Aᴴ * η = A` —
the Krein translation of the reality prescription. For block-diagonal
doublings the content is one equation: `R Ãᴴ R = Ã`.

Finite dimension: boundedness automatic, stated not tested. No
Lorentzian-physics claims; no thermal-phase-transition language.

---

## (b) The prescription, with derivation

### The claim (T2 → T1)

> **Twist-corrected reality prescription (Span 4, Krein form):** the
> doubled fluctuated Dirac `F̃` is Krein-symmetric
> (`KreinSymm R F̃`, i.e. `R F̃ᴴ R = F̃`) **iff** the doubled twisted
> 1-form `Ã = fromBlocks A 0 0 A′` is ρ-real (`IsRhoReal R Ã`,
> i.e. `R Ãᴴ R = Ã`) — under `Dᴴ = D`, the packaged J-term hypothesis
> `hJ : IsRhoReal R Jterm`, and `ε₁` real (`star eps1 = eps1`).

The prescription **halves** rather than adds. ρ-reality of the
block-diagonal `Ã` is equivalent to `A′ = Aᴴ`
(`rhoReal_blockDiag_iff`, proved T1): the second copy is forced to be
the adjoint of the first — the same pairing content as DLM's
component form `X_l = X_r†` (Lemma 4.2 of arXiv:1411.1320, up to sign
convention). So the prescription says: the fluctuation preserves the
Krein structure exactly when the two copies carry conjugate data.

### Derivation (what the proofs actually do)

- **Forward (⟹):** `KreinSymm` is a *linear* condition over the real
  scalars (`kreinSymm_add`, `kreinSymm_sub`, `kreinSymm_real_smul`,
  all T1). The Dirac block is ρ-symmetric by
  `kreinSymm_blockDiag_of_selfAdjoint` (Span 3, T1), the J-term is
  ρ-symmetric by hypothesis `hJ` scaled by the real `ε₁`, so Krein
  symmetry of `F̃` subtracts back down to Krein symmetry — i.e.
  ρ-reality — of `Ã`.
- **Converse (⟸):** `rhoReal_blockDiag_iff` turns `IsRhoReal R Ã` into
  `A′ = Aᴴ`, and `kreinSymm_fluctuation_of_rhoReal` re-assembles the
  fluctuation from ρ-symmetric parts.
- **Numerical mechanism (S2, S5, S6):** on block-diagonal
  `Ã = block_diag(A1, A2)` the residuals factor through
  `E = A1 − A2ᴴ` as `r1 = √2‖E‖` (max rel. deviation 5.3e-16) and
  `r2 = √2‖E + Jact32(E)‖` (max rel. deviation 6.3e-16). The
  (⟹) direction goes through because `Jact32` preserves Hermitian
  conjugation exactly (`‖Jact32(Xᴴ) − Jact32(X)ᴴ‖/‖X‖ = 0.000e+00`,
  S2). The (⟸) direction is the real-linear question "does
  `E + Jact32(E) = 0` imply `E = 0` on the twisted-1-form image
  space E(V)?" — answered by `s_min(L|E(V)) = 1.414214` for
  `L(E) = E + Jact32(E)` (S6).

### Honest bookkeeping (binding)

- The J-term's ρ-reality is a **hypothesis** (`hJ`), never derived from
  the antilinear J — the existing pinned obstruction
  `AntilinearJCompat` (§8) is **untouched**. Both Lean directions close
  conditionally; the unconditional fluctuated-D result still pins on
  exactly this.
- The Lean proofs could not literally invoke
  `kreinSymm_twistedFluctuation_iff` (that iff is about equal-block
  doublings `fromBlocks D D`; Span 4 lives on the doubled 1-form
  `fromBlocks A 0 0 A′` itself) — the module docstrings state this.
  Nothing was smuggled through that name.
- NO new T5 pins. The §9 ledger entry is: both directions close in the
  linear model; no pin on either side.

---

## (c) The iff verdict

### T1 — Lean (`TwistedTriple.lean` §9, machine-checked 2026-10-07)

`lake build ThetLogos.TwistedTriple` → **completed successfully**,
zero sorrys, `#print axioms = [propext, Classical.choice, Quot.sound]`
for all 7 new theorems (lines 1303–1484, local commit `3de9d9f`, NOT
pushed). No new axioms.

| # | Theorem | Statement | Status |
|---|---|---|---|
| T2 | `IsRhoReal η A` | `η * Aᴴ * η = A` — ρ-reality (new T2 def) | DEF |
| T2 | `doubledFluctuation D A A' Jterm eps1` | `F̃ = D̃ + Ã + ε₁ • Jterm` (new T2 def) | DEF |
| T1 | `kreinSymm_add`, `kreinSymm_sub`, `kreinSymm_real_smul` | `KreinSymm` linear over real scalars (helpers) | PROVED |
| T1-27 | `rhoReal_blockDiag_iff` | `IsRhoReal R (fromBlocks A 0 0 A') ↔ A' = Aᴴ` | PROVED |
| T1-28 | `kreinSymm_fluctuation_of_rhoReal` | `Dᴴ=D`, `A'=Aᴴ`, `hJ`, `ε₁` real ⟹ `KreinSymm R F̃` (conditional) | PROVED |
| T1-29 | `rhoReal_of_kreinSymm_fluctuation` | `Dᴴ=D`, `hJ`, `ε₁` real, `KreinSymm R F̃` ⟹ `IsRhoReal R Ã` (conditional; the anticipated obstruction does not materialize) | PROVED |
| T1-30 | `kreinSymm_fluctuation_iff_rhoReal` | full conditional iff: `KreinSymm R F̃ ↔ IsRhoReal R Ã` | PROVED |

### T4 — numerical (`reality_span4_lab.py`, seeds 2026 / 202607, commit `75b9211`)

**S1 sanity gate: REPRODUCED** — Span-3 P.7 exactly: structured real
coefficients → ρ-symmetry residual **4.920e+00**; purely-imaginary
(ρ-real) coefficients → **0.000e+00**. Gate passed; lab proceeded.

**Forward (⟹) — STAND.** Max residual **0.000e+00** over **250 trials**:
200 constructed `Ã = block_diag(A, Aᴴ)` (100 diagonal-type `x=y`,
100 general `x≠y`) plus 50 genuine ρ-real twisted 1-forms (imaginary
coefficients, Hermitian pairs).

**Converse (⟸) — CLEAN IFF, not mere sampling.** 500 general random
trials with no ρ-reality imposed: **ZERO counterexamples** (no trial
with `r2 < 1e-9` and `r1 > 1e-6`). Beyond sampling: kernel equality as
*real* subspaces of the twisted-1-form space `V` (`dim_ℂ V = 6`,
36 spanning twisted commutators):
`dim_ℝ ker(Ψ|V) = 6 = dim_ℝ ker(Δ|V)` (12 real params);
`ker(Ψ) ⊆ ker(Δ)` at max 3.8e-15; `ker(Δ) ⊆ ker(Ψ)` at max 2.5e-14.

**Boundary map (S7) — perfectly monotone.** Over all 500 trials,
`r2/r1 ∈ [1.4142, 1.4142]` — the scatter collapses to the exact line
`r2 = √2·r1`. Mechanism (S6): `Re⟨E, Jact32(E)⟩ ≡ 0` on `E(V)`, so
`r2/r1 = ‖L(E)‖/‖E‖ = √2` **exactly**, and `r2 = 0 ⟺ r1 = 0` — no
points on the `r1`-axis away from the origin, no cancellation
counterexample can exist.

### Reading the verdicts

- The Lean iff is conditional in exactly the honest way: the Dirac is
  self-adjoint (true of `D_F`), `ε₁` is real (true by convention), and
  the J-term is ρ-real by hypothesis (the pinned antilinearity
  obstruction). The machine proves the *logic* of the prescription,
  not its premises.
- The numerical iff is the strong form: ρ-symmetry of the fluctuation
  **is** ρ-reality of the 1-form, both directions, kernel-equal, with
  a monotone √2 boundary map. Nothing in the twisted-1-form space can
  slip through — cancellation between `Ã` and `J̃act(Ã)` is ruled out
  structurally, not just sampled out.
- The prescription STANDS in the form the bridge needs: a
  **reduction**, not an addition — it *removes* half the doubled
  degrees of freedom.

---

## (d) Comparison with the literature — what DLM actually proves

This span was written to the exact statements, because the literature
does NOT contain what a careless reader would expect it to contain.

| Question | DLM literature | Our position | Match |
|---|---|---|---|
| `D_{A_ρ}` ρ-self-adjoint ⟺ `R A_ρᴴ R = A_ρ` (iff) | **NO clean theorem exists** — searched 2026-10-07 | `kreinSymm_fluctuation_iff_rhoReal` is ours, not a quote | **we are ahead in formal precision** |
| one direction: 1-form self-adjoint ⟹ `D_{A_ρ}` self-adjoint (sufficient, NOT necessary) | Devastato–Martinetti arXiv:1411.1320 §4 ("We do not require A to be selfadjoint, we only ask that D_A is selfadjoint"); Filaci–Martinetti PRD 104:025011 §3.3, §4.2; Brzeziński–Ciccoli–Dąbrowski–Sitarz arXiv:1601.07404 Prop 2.3 setup | our ⟸ direction is the Krein analog of this sufficient direction | partial (Krein vs Euclidean) |
| exact iff for ORDINARY self-adjointness | Devastato–Martinetti 1411.1320 Lemma 4.2 eq (4.21): `D_X` self-adjoint ⟺ `ρ(X_μ) = −X_μ†` (component form `X_l = X_r†` — same pairing content as our `A′ = Aᴴ`, up to sign convention); Prop 4.4: `D_σ` self-adjoint ⟺ `φ = φ̄` (scalar fluctuation real) | `rhoReal_blockDiag_iff` (`A′ = Aᴴ`) is the same pairing content in Krein form | **content match** (sign convention differs) |
| ρ-adjointness (Krein) as an iff | **no iff theorem** — only conditional remarks: Devastato–Filaci–Martinetti–Singh arXiv:2002.11700 Def 3.1 (§3.2: twisted gauge transformation *preserves* ρ-adjointness, one direction); Martinetti survey arXiv:2301.08346v2 §5.1 fn 11 (conditional "if one were starting with…"); Martinetti–Nieuviarts–Zeitoun arXiv:2401.07848 §4.4 | present `R Ãᴴ R = Ã` as **our Krein translation**, NOT as a quoted DLM theorem | **we state it as ours** |

**Bottom line:** the literature has the ordinary-adjointness iff's and
one sufficient Krein direction; the full Krein iff — `F̃`
ρ-symmetric ⟺ `Ã` ρ-real — is ours, proved T1 (conditional) and
characterized T4 (kernel-equal). Our Lean `kreinSymm_twistedFluctuation_iff`
(Span 3) and `kreinSymm_fluctuation_iff_rhoReal` (this span) are ahead
of the published record in formal precision on the Krein point. We do
not quote DLM for what DLM does not say.

---

## (e) Field-content reading — with the tier boundary

### What the algebra says (exact)

`R Ãᴴ R = Ã ⟺ A′ = Aᴴ`. On the diagonal `(a,a)` — the physical field,
per Span 2 T1-13 (the twisted commutator at `(a,a)` reduces to the
ordinary one) — in the lab's anti-Hermitian `(h,h)` basis the reading
is: **imaginary coefficients are KEPT, real coefficients are
PROJECTED OUT**. Basis-independent reading: the prescription keeps
the Hermitian (operator) part and kills the anti-Hermitian part. That
is the algebra's entire content. It ends there.

### What the algebra does NOT say (T5 overlay — do not cross)

- **The gauge/Higgs split does not exist as physics in our finite
  model.** There is no manifold part, no `∂̸⊗I_F` term to fluctuate.
  The algebra only has Γ-even vs Γ-odd blocks, and ρ-reality treats
  both identically — no separation, both survive-or-die together.
  Any sentence of the form "this is the gauge boson, that is the
  Higgs" is T5 overlay on T1 algebra.
- **FLAG (recorded):** `InnerFluctuations.lean`'s "SU(3)×SU(2)×U(1)
  gauge connections" docstring language is T5. Reconcile that
  docstring with Span-3's representation caveat (18/24 generators map
  to 0 under the lab's π; M₃(ℂ) killed) before any "gauge boson"
  claim ships.
- **Doubling ≠ field creation.** ρ-reality doesn't add fields; it
  halves the doubled DOF — the `A′ = Aᴴ` pairing is the constraint.
  (Same content as DLM Lemma 4.2's `X_l = X_r†`.)
- **The explicit boundary:** algebra ends at
  "A′ = Aᴴ; imaginary kept, real killed." Everything beyond —
  "gauge bosons", "Higgs", "physical field" — is T5 overlay, and this
  dossier marks it as such.

---

## (f) Remaining canyon (named, with admission prices — unchanged from Span 3)

| Gap | Status after Span 4 | Admission price |
|---|---|---|
| **Twist-corrected reality prescription** | **CLOSED (STAND)** — full conditional iff, T1 + T4 | the J-term ρ-reality premise (`AntilinearJCompat`, still pinned T5 — the unconditional fluctuated-D result still hangs on it) |
| **Causality** | untouched | a cone/order on states respected by the flip — unbuilt |
| **Continuum** | untouched | a limit procedure — unbuilt; the thermal-phase-transition ban stands |
| **BW analog** | still quarantined (Span 1 §(c)) | a localization structure — does not exist |
| **Lorentzian signature** | **not effected** — Krein structure built and verified (Span 3); signature hinge (R as a Dirac matrix) absent; no finite analog of the fermionic-action argument | a Clifford action — does not exist |

---

## (g) T1 / T4 / T5 ledger for Span 4

### T1 — machine-checked (extends Span 3's T1-15–T1-26)

`lean/ThetLogos/TwistedTriple.lean` §9 (lines 1303–1484) — build
green, zero sorrys, axioms `[propext, Classical.choice, Quot.sound]`,
local commit `3de9d9f`.

T1-27 (`rhoReal_blockDiag_iff`: ρ-reality ⟺ `A′ = Aᴴ`),
T1-28 (`kreinSymm_fluctuation_of_rhoReal`, conditional ⟸),
T1-29 (`rhoReal_of_kreinSymm_fluctuation`, conditional ⟹),
T1-30 (`kreinSymm_fluctuation_iff_rhoReal`, full conditional iff);
helpers `kreinSymm_add/sub/real_smul`.
Both directions conditional on `Dᴴ = D`, `hJ : IsRhoReal R Jterm`,
`ε₁` real. **NO new T5 pins.**

### T4 — numerical (this dossier's lead tier for the verdicts)

T4-26 (sanity gate: Span-3 P.7 reproduced, 4.920e+00 / 0.000e+00),
T4-27 (J-identity `‖Jact32(Xᴴ) − Jact32(X)ᴴ‖/‖X‖ = 0.000e+00`),
T4-28 (forward: max r2 **0.000e+00** over 250 trials),
T4-29 (converse: 500 trials, **zero** counterexamples),
T4-30 (kernel equality: `dim_ℝ ker(Ψ|V) = 6 = dim_ℝ ker(Δ|V)`,
inclusions at 3.8e-15 / 2.5e-14),
T4-31 (residual factorization `r1 = √2‖E‖`, `r2 = √2‖E+Jact32(E)‖`,
deviations ≤ 6.3e-16),
T4-32 (boundary map: `r2/r1 ∈ [1.4142, 1.4142]` exactly — monotone,
`r2 = 0 ⟺ r1 = 0`).

### T5 — pinned / vision

- `AntilinearJCompat` (§8, **untouched**): the true J is antilinear;
  the J-term's ρ-reality stays a hypothesis, never derived.
- Unconditional `KreinSymm` for the fluctuated Dirac: still pins on the
  J-term premise — same obstruction as Spans 1–3, now with both
  directions of the conditional proven.
- Lorentzian signature change: open — Krein structure built, signature
  hinge absent; no finite analog of the fermionic-action argument.
  No Lorentzian-physics claims.
- BW analog: still quarantined. No thermal-phase-transition language.
- Physical reading beyond "A′ = Aᴴ; imaginary kept, real killed":
  all T5 overlay (gauge bosons, Higgs, "physical field") — marked,
  not shipped.
- `InnerFluctuations.lean` gauge-language docstring: FLAG for
  reconciliation with the representation caveat.

### T2 / T3

T2: `IsRhoReal`, `doubledFluctuation`. T3: none.

---

## Span verdict

**STAND:** the twist-corrected reality prescription — the doubled
fluctuated Dirac `F̃` is Krein-symmetric ⟺ the doubled 1-form `Ã` is
ρ-real (`A′ = Aᴴ`) — closes both ways: Lean proves the full
conditional iff (T1-27–T1-30, build green, zero sorrys, no new pins)
and the numerical lab shows a clean beyond-sampling iff
(kernel-equal real subspaces, perfectly monotone √2 boundary map).
The bridge now has three standing pylons (viable twist, Krein
structure, reality prescription); the remaining canyon is named in
§(f). Killed claims stay killed: single-H η, the flow twist, naive
`ρ(a) = ΓaΓ`, the lab's wrong commutant-obstruction argument, and
the thermomagnetic "7-state torsion / cloaking" language — none of
them appear in this span.
