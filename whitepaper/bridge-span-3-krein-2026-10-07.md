# Bridge Span 3 — the Krein structure (dossier)

**Date:** 2026-10-07 · **Lead tier: T4** (numerical) + **T1** (Lean extension, machine-checked)
**Instrument:** `scripts/krein_span3_lab.py` (seed 2026)
**Results:** `scripts/bridge-span-3-results.md`
**Predecessors:** `whitepaper/bridge-span-1-twist-2026-10-07.md` (flow twist: KILLED);
`whitepaper/bridge-span-2-involutive-twist-2026-10-07.md` (grading flip: STANDS)
**Lean:** `lean/ThetLogos/TwistedTriple.lean` §8 (extends §§1–7, builds green, zero sorrys)
**Status:** dossier drafted 2026-10-07.

## What this span is

Span 2 left a standing pylon — the DLM grading flip, a living Connes–Moscovici
twisted triple with twisted order-one intact over 331,776 pairs — and one
named admission price: the **Krein / ρ-product structure**, the indefinite
inner product the DLM Lorentzian-signature argument actually needs. Span 2's
§D probe refuted the naive candidate (the Γ-product: D_F is Γ-skew,
`‖ΓDΓ − Dᴴ‖ = 2‖D‖`). This span builds the real one.

**Verdict up front: STAND (primary), KILL (secondary).** The DLM transplant
— the swap fundamental symmetry `R = [[0,I₃₂],[I₃₂,0]]` on the doubled
Hilbert space `H⊕H = ℂ⁶⁴` — satisfies all four kill/stand criteria exactly:
`R² = I`, `Rᴴ = R`, D ρ-symmetric (`R D̃ᴴ R = D̃`), and the flip implemented
innerly with J-compatibility at sign +1. The ambitious alternative — a
fundamental symmetry η on the single `ℂ³²` — is KILLED by a proved
obstruction: the Hermitian joint-constraint space has a 4-dimensional
common kernel, so every admissible η is singular and `η² = I` is impossible.
The kill is structural, not a failed search.

---

## (a) Exact setup and conventions **(T4 — numerical; definitions exact)**

### Literature (verified 2026-10-07 via web search)

arXiv:1710.04965, "Lorentz signature and twisted spectral triples"
(Devastato–Lizzi–Martinetti), §3.1–§3.2:

- **ρ-product (3.1):** `⟨Ψ,Φ⟩_ρ := ⟨Ψ, RΦ⟩`, R the unitary implementing
  `ρ(a) = R a R⁻¹` (3.11).
- **Fundamental symmetry:** R self-adjoint, `R ≠ 1` ⟹ eigenvalues ±1,
  `H = H₊ ⊕ H₋`, ρ-product positive on H₊ / negative on H₋ — a **Krein
  space**; `⟨·, R·⟩_ρ` is the original (positive) Hilbert product.
- **Krein-adjoint:** `A⁺ := R Aᴴ R`; D ρ-symmetric ⟺ `R Dᴴ R = D`.
- **Compatibility (3.12):** `JR = ±RJ`.
- **DLM SM case:** `R = [[0,1₂],[1₂,0]] = γ_E^0`; the ρ-product is the
  Lorentzian Krein product `∫ Ψ†γ⁰Φ`.
- Twisted first-order condition `[[D,a]_ρ,b°]_{ρ°} = 0` with
  `ρ°(a°) := (ρ⁻¹(a))°` (arXiv:2010.15367 §2.2) — reproduced for reference;
  not re-tested here (Span 2 §B stands).

### The DLM transplant (primary candidate)

On `H⊕H = ℂ⁶⁴`:
- Doubled representation: `π̃(a,a′) = block_diag(π(a), π(a′))`.
- Fundamental symmetry: `R_swap = [[0, I₃₂],[I₃₂, 0]]` (real symmetric).
- Doubled Dirac: `D̃ = block_diag(D_F, D_F)`.
- Doubled real structure: `J̃act(X) = Ũ conj(X) Ũᵀ`, `Ũ = block_diag(U_J, U_J)`
  (CONJUGATE-based, binding — same convention as Spans 1–2).
- `‖D_F‖ = 228.78 GeV` (operator norm), `‖D_F‖_F = 792.796`.

### Representation caveat (binding, from the lab)

18/24 generators map to **0** under π (this representation kills the M₃(ℂ)
factor); the 6 nonzero π(g) have ℂ-rank 6. Pair grids run over all 24 gens
as specified but are effectively 6×6. The single-H linear-constraint section
uses the 6-matrix ℂ-basis — exactly equivalent (`[X,·] = 0` is ℂ-linear,
`[X,0] = 0` vacuous).

### Convention table (carried, binding)

`piOp` TRANSPOSE-based; J-action CONJUGATE-based; agree on Hermitian,
differ otherwise. Finite dimension: boundedness automatic, stated not
tested. No Lorentzian-physics claims; no thermal-phase-transition language.

---

## (b) Preserve / break verdicts

### T1 — Lean (`TwistedTriple.lean` §8, machine-checked 2026-10-07)

`lake build ThetLogos.TwistedTriple` → **completed successfully (3244 jobs)**,
zero sorrys, zero `sorryAx` anywhere in the file (grep-verified),
`#print axioms = [propext, Classical.choice, Quot.sound]` on all 33
`#print axioms` lines (16 new + 17 pre-existing). No new axioms.

| # | Theorem | Statement | Status |
|---|---|---|---|
| T1-15 | `kreinAdjoint_involutive` | `(A⁺)⁺ = A` for `A⁺ = ηAᴴη`, from `η²=1`, `ηᴴ=η` | PROVED |
| T1-16 | `swapR_sq`, `swapR_hermitian`, `swapR_fundamental` | `R²=1`, `Rᴴ=R`, `IsFundamentalSymm R` | PROVED |
| T1-17 | `swapR_conj_blockDiag` | `R·fromBlocks A 0 0 B·R = fromBlocks B 0 0 A` (workhorse) | PROVED |
| T1-18 | `kreinSymm_blockDiag_of_selfAdjoint` | `R·D̃ᴴ·R = D̃` for `D̃ = fromBlocks D 0 0 D` given `Dᴴ=D` | PROVED |
| T1-19 | `kreinSymm_blockDiag_iff_selfAdjoint` | `KreinSymm R (fromBlocks Df 0 0 Df) ↔ Dfᴴ = Df` | PROVED |
| T1-20 | `kreinSymm_twistedFluctuation_iff` | same iff for `D̃_{Aρ}` (conditional T1) | PROVED (conditional) |
| T1-21 | `swapR_implements_flip` | `R·π̃(a,a')·R = π̃(a',a)` for block-diagonal doubled reps | PROVED |
| T1-22 | `trace_swapR` | `Matrix.trace R = 0` — the (n,n) signature data (proved via diagonal sum; Mathlib has no `trace_fromBlocks`) | PROVED |
| T1-23 | `kreinSymm_swapR_transport_of_comm` / `_of_anticomm` | `JR = ±RJ ⟹ (KreinSymm R D → KreinSymm R (J·D·Jᴴ))` — linear stand-ins with explicit antilinearity caveats | PROVED |
| T1-24 | `kreinProd_one`, `kreinProd_fundSymm_self` | ρ-product at `η=1` is the dot product; `⟨x,Rx⟩_ρ = ⟨x,x⟩` | PROVED |
| T1-25 | `swapR_ne_diagGrading` | **`R ≠ Γ`** — the swap is a NEW off-diagonal object, not the grading (proved, not merely asserted) | PROVED |
| T1-26 | `swapR_kreinUnitary_self` | the swap is Krein-unitary for its own product | PROVED |

**T2 defs:** `IsFundamentalSymm`, `kreinAdjoint`, `kreinProd`
(`star x ⬝ᵥ (η *ᵥ y)`), `KreinSymm`, `ImplementsFlip`, `swapR`,
`IsKreinUnitary`.

**T5 pinned (exact obstructions):**
- `AntilinearJCompat` — DLM (3.12) for the *true* J. Obstruction: J is
  antilinear, inexpressible with linear `Matrix` maps (consistent with the
  §6 pin). T1 shadows: the two transport lemmas.
- `KreinUnitaryTwist` — twist by a two-sided Krein-unitary in full DLM
  generality. Obstruction: the Krein-unitary group and its intertwining
  with the flip are unbuilt. T1 shadow: `swapR_kreinUnitary_self`.

**Fluctuated Dirac — closes conditionally, pins unconditionally:**
`kreinSymm_twistedFluctuation_iff` proves
`KreinSymm R D̃_{Aρ} ↔ D_{Aρ}ᴴ = D_{Aρ}` as T1. The unconditional
`KreinSymm` for the fluctuated Dirac therefore **pins T5**, with the exact
obstruction being the twist-corrected reality prescription for twisted
1-forms — the same obstruction as Span 2 §B C (self-adjointness residuals
9.97e3/2.087, not automatic). **No new obstruction introduced.**

### T4 — numerical (`krein_span3_lab.py`, seed 2026)

**PRIMARY — R_swap on ℂ⁶⁴: STAND.** All eight residuals:

| # | Test | Result | Verdict |
|---|---|---|---|
| P.1 | `‖R²−I‖_F`, `‖R−Rᴴ‖_F` | **0.000e+00**, **0.000e+00** (`‖R−I‖`=11.31, nontrivial ✓) | PASS — self-adjoint unitary ≠ 1 |
| P.2 | flip implementation, 576 pairs | max **0.000e+00** | PASS — `ρ` inner via R, exactly |
| P.3 | D ρ-symmetry `‖R D̃ᴴ R − D̃‖` | **0.000e+00** | PASS |
| P.4 | J-compatibility `‖Ũ_J R − sRŨ_J‖` | s=+1: **0.000e+00**; s=−1: 1.600e+01 | PASS — DLM (3.12) with **+ sign** |
| P.5 | spectrum of R | **32×(+1), 32×(−1)**; tr R = 0 | Krein signature **(32,32)** |
| P.6 | twisted order-one, doubled picture, 331,776 pairs | max **0.000e+00** | reproduces Span 2 |
| P.7 | fluctuated D̃ ρ-symmetry | **4.920e+00** (structured, real coeffs); **0.000e+00** with purely-imaginary (ρ-real) coefficients | **the DLM point, in Krein language:** fluctuation preserves ρ-self-adjointness ⟺ the twisted 1-form is ρ-real (`RÃ_ρᴴR = Ã_ρ` needs imaginary coefficients) |
| P.8 | — | (see §S) | — |

**P.7 notes:** the literal Span-2 off-diagonal `(h₀,h₁)/(h₁,h₀)`
fluctuation vanishes identically here (`Dh₀ = h₁D` exactly), so the test
uses the diagonal-pair version `(h₀,h₀),(h₁,h₁)` — nontrivial
(`‖Ã_ρ‖ = 2.03`). For block-diagonal `D̃_f`, the ρ-symmetry residual equals
the ordinary self-adjointness residual. Same admission price as Spans 1–2
§C, now stated as a Krein condition rather than a Euclidean one.

**SECONDARY — single-H η on ℂ³²: KILL (obstruction proved).**
- The lab's original "Γ-even commutant" obstruction argument was **wrong**
  for this representation (commutant is 787-dim, far larger than the
  opposite-image span) — caught and corrected in-lab; the wrong argument
  is recorded as killed, per the relabeling rule.
- The linear constraints do NOT obstruct η: constraint nullities are
  (L1 [commutant]) = 787, (L1+L2 [sector swap]) = 392,
  (L1+L2+L3 [D-symmetry]) = **75** — clean SVD gaps, smallest nonzero
  singular value 1.41.
- The obstruction is **unitarity**, proved structurally: the 75-real-dim
  Hermitian joint-nullspace has a **4-dimensional COMMON kernel** — every
  admissible Hermitian H annihilates the same 4-dim subspace
  (verified `max_k ‖B_k v‖ = 1.6e-14`; random H have rank 28/32,
  min|eig| ~1e-15, none invertible in 500 trials). Since `η² = I`
  requires η invertible, **no single-H η exists**.
- **Pareto frontier:** {`η²=I`, `η†=η`} feasible; +{`ηΓ=−Γη`} feasible
  (explicit η₀ swap, all residuals 0); all linear-only subsets feasible
  (787/392/75-dim); full set + unitarity **infeasible** (common-kernel
  proof). Unitarity inside intermediate subspaces not determined — moot
  for the verdict.

### Reading the verdicts

- **P.1–P.4:** the DLM transplant lands exactly. The swap is a genuine
  fundamental symmetry, implements the flip innerly, keeps D̃ ρ-symmetric,
  and meets J with the + sign — every compatibility the literature asks
  for, at numerical zero.
- **P.5:** the (32,32) signature is algebraic data, not spacetime — see §(c).
- **P.6:** the Krein picture doesn't disturb the Span-2 order-one result;
  the twisted calculus is intact in the doubled picture.
- **P.7:** the fluctuation story is now sharp: ρ-self-adjointness is the
  property the twisted fluctuation preserves, and it holds exactly when
  the 1-form is ρ-real. This reframes Spans 1–2's §C flag (Euclidean
  self-adjointness residuals 9.97e3/2.087) as the *wrong* self-adjointness
  to demand — the DLM-correct one is the ρ-version, and it has a precise
  algebraic character (imaginary coefficients).
- **§S kill:** the single-H η is dead by proof, not by failed search.
  The common-kernel obstruction is structural: any η satisfying the linear
  constraints is singular. This is consistent with DLM's own picture — R
  lives on B(H) implementing the flip, and in the SM case H = L²(M,S)
  already carries the chiral doubling; our finite H = ℂ³² has no such
  room, so the doubling must be explicit (H⊕H).

---

## (c) The signature question — precise verdict

The finite triple now carries **algebraic signature data (32,32)**: the
flip's implementing fundamental symmetry `R_swap` has vanishing trace
and ±1 spectrum with equal multiplicities (T1: `trace_swapR`; T4: 32/32
eigenvalues), making `(H⊕H, ⟨·,·⟩_ρ)` a genuine Krein space in which `D̃`
is ρ-symmetric, the flip is implemented innerly, and J-compatibility
holds at sign +1. This is the exact finite-dimensional transplant of
DLM's construction — every compatibility the literature requires is
satisfied, several at the T1 level.

What it does **not** carry is **Lorentzian spacetime signature**. There
is no manifold, no Clifford action, and no γ^μ from which to read
(+,−,−,−): in DLM's continuum argument the signature emerges because
`R = γ_E^0` is simultaneously the flip implementer *and* the temporal
Dirac matrix, so the fermionic action `⟨Ψ, DΨ⟩_ρ` becomes the Lorentzian
Dirac Lagrangian. Our `R_swap` implements the flip but is not a Dirac
matrix — it carries no Clifford relations, no light cone, no causality.
The (32,32) is a property of the doubled representation (two copies of
everything), not of a metric. The honest ledger entry: **Krein structure:
built and verified; signature change: not effected.** The DLM continuum
step — fluctuation preserving the Lorentzian product in the fermionic
action — has no finite analog here, because there is no fermionic action
to preserve it in.

---

## (d) Comparison with the continuum DLM construction

| Axis | DLM continuum (arXiv:1710.04965) | This span (finite) | Match |
|---|---|---|---|
| ρ-product `⟨·,·⟩_ρ = ⟨·,R·⟩` | §3.1, R = γ⁰_E | built (T2), swap instance | exact transplant |
| R self-adjoint unitary ≠ 1 | §3.2 ⟹ Krein space | T1 (`swapR_fundamental`) + T4 (P.1) | exact |
| `ρ(a) = RaR⁻¹` inner | (3.11) | T1 (`swapR_implements_flip`) + T4 (P.2, 0.000e+00) | exact |
| D ρ-symmetric | assumed/proved per model | T1 (`kreinSymm_blockDiag_of_selfAdjoint`) + T4 (P.3) | exact |
| `JR = ±RJ` | (3.12) | T4: + sign at 0.000e+00; T1: linear-shadow transport lemmas; full antilinear form pinned T5 | partial (antilinearity) |
| R = γ⁰ (temporal Dirac) | the signature hinge | **absent** — R_swap is not a Dirac matrix | **the gap** |
| Fermionic action → Lorentzian | §4–5 | no finite analog | canyon |
| Twisted fluctuation preserves ρ-product | survey §4.2 remark | P.7: exactly when 1-form is ρ-real | algebraic analog |

**Bottom line:** the finite transplant reproduces every *algebraic*
compatibility of DLM's Krein construction and fails at exactly the point
where the continuum uses *geometry* (γ⁰ as a Clifford generator). The map
is honest about which side of that line we're on.

---

## (e) Remaining canyon (named, with admission prices)

| Gap | Status after Span 3 | Admission price |
|---|---|---|
| **Twist-corrected reality prescription** | reframed, not closed — now a Krein condition (ρ-real 1-forms, P.7) instead of a Euclidean one | the DLM follow-up construction, implemented and tested in ρ-language |
| **Causality** | untouched | a cone/order on states respected by the flip — unbuilt |
| **Continuum** | untouched | a limit procedure — unbuilt; the thermal-phase-transition ban stands |
| **BW analog** | still quarantined (Span 1 §(c)) | a localization structure — does not exist |
| **Single-H fundamental symmetry** | **KILLED** (common-kernel proof) — returns only as a new construction on a different representation, per the relabeling rule | n/a (dead) |

---

## (f) T1 / T4 / T5 ledger for Span 3

### T1 — machine-checked (extends Span 2's T1-8–T1-14)

`lean/ThetLogos/TwistedTriple.lean` §8 — build green (3244 jobs), zero
sorrys, axioms `[propext, Classical.choice, Quot.sound]`.

T1-15 (Krein-adjoint involution), T1-16 (swap fundamental symmetry),
T1-17 (block-conjugation workhorse), T1-18/19/20 (ρ-symmetry for
block-diagonal D, iff-characterizations incl. the conditional fluctuated
case), T1-21 (flip implementation), T1-22 (`trace_swapR = 0`),
T1-23 (J-compatibility transport, linear shadows), T1-24 (ρ-product
basics), T1-25 (`swapR_ne_diagGrading` — R ≠ Γ, proved), T1-26
(swap Krein-unitary for its own product).

### T4 — numerical (this dossier's lead tier for the verdicts)

T4-18 (R self-adjoint unitary ≠ 1, exact), T4-19 (flip implementation,
576 pairs, exact), T4-20 (D ρ-symmetry, exact), T4-21 (J-compatibility
+ sign, exact), T4-22 (spectrum 32/32, tr R = 0), T4-23 (twisted
order-one, 331,776 pairs, reproduces Span 2), T4-24 (fluctuated-D
ρ-symmetry: 4.920 structured / 0.000 ρ-real — the DLM point),
T4-25 (single-H η KILLED: 4-dim common kernel ⇒ all admissible η
singular ⇒ η²=I impossible; Pareto 787/392/75).

### T5 — pinned / vision

- `AntilinearJCompat`: exact obstruction = J's antilinearity.
- `KreinUnitaryTwist`: exact obstruction = unbuilt Krein-unitary group.
- Fluctuated-D unconditional ρ-symmetry: exact obstruction = the
  twist-corrected reality prescription (same as Spans 1–2, reframed).
- Lorentzian signature change: open — Krein structure built, signature
  hinge (R as Dirac matrix) absent; no finite analog of the fermionic
  action argument.
- BW analog: still quarantined. No Lorentzian-physics claims; no
  thermal-phase-transition language; killed claims (flow twist, naive
  Γ-conjugation, single-H η, the lab's own wrong commutant argument)
  stay killed.

### T2 / T3

T2: `IsFundamentalSymm`, `kreinAdjoint`, `kreinProd`, `KreinSymm`,
`ImplementsFlip`, `swapR`, `IsKreinUnitary`. T3: none.

---

## Span verdict

**STAND (primary):** the DLM Krein transplant — `R_swap` on `H⊕H` is a
fundamental symmetry implementing the flip, with D ρ-symmetric,
J-compatible at sign +1, spectrum (32,32), and twisted order-one intact —
verified T1 (12 new theorem groups, build green) and T4 (all residuals
exact). **KILL (secondary):** the single-ℂ³² η, by a proved common-kernel
obstruction — the doubling is not optional, which is exactly what DLM's
picture says. The bridge now has two standing pylons (viable twist,
Krein structure) and the map marks the next span precisely: the
twist-corrected reality prescription in ρ-language, then causality. The
far shore — Lorentzian physics — is still canyon, and the dossier says
exactly why: we have the Krein space, but not the γ⁰.
