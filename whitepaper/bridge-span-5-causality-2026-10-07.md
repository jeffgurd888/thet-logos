# Bridge Span 5 — causality (dossier)

**Date:** 2026-10-07 · **Lead tier: T1** (proved obstruction) + **T4** (numerical no-go) + **T5** (literature survey)
**Instruments:** `scripts/causality_span5_lab.py` (seeds 2026 / 202607); `lean/ThetLogos/TwistedTriple.lean` §10
**Results:** `scripts/bridge-span-5-results.md`; `whitepaper/bridge-span-5-causality-literature.md`
**Predecessors:** `whitepaper/bridge-span-4-reality-2026-10-07.md` (reality prescription: STANDS);
`whitepaper/bridge-span-3-krein-2026-10-07.md` (Krein structure: primary STAND, single-H η KILLED);
`whitepaper/bridge-span-2-involutive-twist-2026-10-07.md` (grading flip: STANDS);
`whitepaper/bridge-span-1-twist-2026-10-07.md` (flow twist: KILLED)
**Lean:** `lean/ThetLogos/TwistedTriple.lean` §10 (extends §§1–9, builds green, zero sorrys)
**Git:** Lean §10 in local commit `841fad4`; numerical lab in local commit `c3b721a`; literature ledger untracked (NOT pushed)
**Status:** dossier drafted 2026-10-07.

## What this span is

Spans 2–4 built the algebraic Lorentzian apparatus: a viable twist (the
DLM grading flip), a Krein structure (R_swap on ℂ⁶⁴), and the
twist-corrected reality prescription (iff closed both ways). But
Lorentzian geometry is not just indefinite signature — it is **causal
order** (p ≤ q). DLM's twisted triples encode signature via the Krein
structure; causality is a further structure: a distinguished convex cone
of "causal functions" in the self-adjoint algebra. The finite triple has
no spacetime points — so the question this span answers is sharp: **can
A_F carry a causal cone at all, or is causality irreducibly
manifold-level?**

**Verdict up front: KILL.** Three independent confirmations — proved
(Lean), numerical (T4), and literature (Besnard's egalitarian theorem) —
converge: no Franco-style causal cone exists on the finite triple. The
obstruction is structural, not a failed search. This is the clean,
valuable kill the span was designed to allow, and it names the exact
admission price the manifold factor must pay.

---

## (a) Exact setup and conventions **(binding, carried from Spans 1–4)**

- Doubled Hilbert space `H⊕H = ℂ⁶⁴`, doubled Dirac `D̃ = block_diag(D_F, D_F)`.
- Fundamental symmetry `R = R_swap = [[0, I₃₂],[I₃₂, 0]]` (real symmetric,
  `R² = I`, `Rᴴ = R`) — Span 3's DLM transplant, standing.
- Doubled representation `π̃(a,a′) = block_diag(π(a), π(a′))`.
- Conjugate-based real-structure action `Jact(X) = U X.conj() Uᵀ`.
- **Represented algebra caveat (binding):** all numerical statements are
  about the *represented* algebra — 18/24 generators map to 0 under the
  lab's π, M₃(ℂ) killed; `A_rep ≅ M₂(ℂ)⊕ℂ⊕ℂ`, with represented unit `e`,
  `[D_F, e] = 0` verified. `I₃₂` is NOT represented (fit residual 5.29);
  (F4) was read against `e`.
- Franco's axioms (from the literature ledger,
  `whitepaper/bridge-span-5-causality-literature.md`):
  (F1) Hermitian; (F2) sum-stable; (F3) positive homogeneity;
  (F4) all real constants `x·1 ∈ C`; (F5) norm-closure of complex span
  = Ã; (F6) `⟨φ, J[D,a]φ⟩ ≤ 0` for all `φ ∈ H`. Plus (F7) the induced
  order `ω ≼ η` on states and (F8) the recovery theorem (complete
  globally hyperbolic M ⇒ ≼ on physical pure states recovers the
  causal relation).

---

## (b) Confirmation 1 — the proved obstruction (T1, Lean §10)

`lake build` fully green — **3324 jobs**, zero errors, zero sorrys in
§10 (~560 lines, local commit `841fad4`). All `#print axioms` for new
theorems show exactly `[propext, Classical.choice, Quot.sound]`.

| # | Entry | Statement | Status |
|---|---|---|---|
| T2 | `IsPosSemidef` | positive semidefiniteness | DEF |
| T2 | `IsCausalConeStatic` | Franco (F1)–(F5) | DEF |
| T2 | `IsDynamicallyCompatible` | `i[D,f]`-PSD (dynamical variant) | DEF |
| T2 | `IsLorentzCompatible` | Krein J-form (stated; **no verdict**) | DEF |
| T2 | `CausalLE` | induced order on states | DEF |
| T1 | `causalCone_obstruction` | **no set satisfies (F1)–(F5) jointly with `i[D,f]`-PSD when D is self-adjoint and non-central** | PROVED |
| T1 | `causalCone_forces_central` | dynamical compatibility forces `f` into D's commutant | PROVED |
| T1 | `dyn_comm_eq_zero`, `posSemidef_trace_eq_zero`, `trace_comm_eq_zero` | trace-collapse engine: `Tr[D,f] ≡ 0` | PROVED |
| T1 | `psdCone_static`, `selfAdjointSet_static`, `psd_spanning` | static axioms alone ARE satisfiable (even by the positive cone) | PROVED |
| T1 | `causalLE_refl`, `causalLE_trans` | induced order is a preorder | PROVED |

**Mechanism (the proof's content):** trace-class collapse of the
commutator. `Tr[D,f] ≡ 0` for self-adjoint D forces any PSD `i[D,f]`
to vanish, collapsing the dynamical cone to D's self-adjoint
commutant — which cannot span `A_sa`. The static axioms (F1)–(F5)
alone are satisfiable (the ordinary positive cone passes them), so
the *dynamical* axiom is exactly what fails. 23 theorems total, all
proved, no new axioms.

**Honesty boundary (binding):** `IsDynamicallyCompatible` (`i[D,f]`-PSD)
is **not** Franco's (F6) (the Krein form `J[D,a] ≤ 0`). The proved
obstruction kills the `i[D,f]`-variant; the J-form verdict in Lean is
explicitly open (`IsLorentzCompatible`, no verdict claimed). The (F4)
formalization uses `1 ∈ C` (weaker than Franco's all-real-multiples),
so the obstruction applies a fortiori to true Franco cones.

---

## (c) Confirmation 2 — the numerical no-go (T4)

`scripts/causality_span5_lab.py` (commit `c3b721a`, seeds 2026/202607),
graded against Franco's real (F1)–(F6) verbatim (the literature file
existed in time — this mattered: (F4) requires *all* real multiples of
the unit, including negative).

| Candidate | Verdict | Mechanism |
|---|---|---|
| **(a) Krein-positive cone** (ρ-positivity w.r.t. R_swap) | **KILL, degenerate** | `R π̃(a,a) = [[0,A],[A,0]]` has spectrum `±eig(A)` (residual 6.3e-16 over 2000 samples) ⇒ ρ-positivity forces `A = 0` exactly: **cone = {0}**. Fails (F4) and (F5). |
| **(b) Grading cone** (Γ-even positives) | **KILL, trivial** | `[Γ, π] = 0` (residual 0.000e+00) makes the Γ-even condition vacuous ⇒ this **IS the ordinary positive cone** — order structure, not causal structure. Fails (F4) (`−e` has eigenvalue −1) and (F6) not even statable generically. |

**Twist compatibility — PASS (not the blocker):** flip preserved
exactly, `‖R π̃(a,a′) R − π̃(a′,a)‖_F` max = **0.000e+00** over 576
generator pairs and 200 random doubled-cone pairs.

**Krein compatibility — CLASH:** 400/400 nonzero grading-cone samples
are R-indefinite on the diagonal (worst min-eig −5.04); only {0} is
both operator-positive and ρ-positive.

**The general no-go (stronger than the candidates):** the (F6) form
`M(a) = R[D̃,π̃(a,a)]` has **identically vanishing Hermitian part**
(max `‖M+M†‖` = **0.000e+00**) — the operator inequality is statable
**iff `[D_F, A] = 0`** (500/500 agreement). Maximal statable complex
span = commutant: **dim 3 < 6** diagonal, **6 < 12** doubled (200/200).
Hence **(F5) spanning and (F6) are jointly unsatisfiable** — no
Franco-style causal cone exists on the represented finite triple with
the DLM Krein structure, not just these two candidates. (In the
commutative Lorentzian case `J[D,f]` *is* self-adjoint via Clifford
relations — Besnard §7; the finite transplant lacks that relation.)

---

## (d) Confirmation 3 — the literature (T5 survey)

From `whitepaper/bridge-span-5-causality-literature.md`:

- **Franco's six axioms** (arXiv:1212.5171 v2/v3) are all **(a)
  formally statable** over a finite *-algebra (convex/functional-calculus
  constraints; (F6) is a concrete LMI on ℂ⁶⁴ with our R_swap). The
  induced order on states is also (a). Everything giving the cone
  *meaning* — recovery theorem (F8), toposet duality, distance-formula
  proof, causal functions separating points, global hyperbolicity —
  is **(b) manifold-level**.
- **Besnard's egalitarian theorem** (arXiv:1508.01917 review):
  **Mₙ(ℂ) admits only the trivial isocone for all n ≠ 2.** Our M₃(ℂ)
  summand ⇒ trivial order; the SM finite algebra has no M₂(ℂ). (The ℍ
  summand is unexamined — flagged, not proven.)
- **Finite/twisted verdict:** no causal cone constructed for any
  purely finite triple, anywhere; **no causal-cone results at all for
  twisted triples** (arXiv:1710.04965 supplies only the Krein J;
  arXiv:2512.15450 stops at a local compact result). The one
  finite-involving result (Franco–Eckstein arXiv:1310.8225 on
  S(ℝ^{1,1})⊗M₂(ℂ)) keeps the manifold factor.
- Neither Franco nor Besnard axiomatizes the strict chronological
  relation ≪ — both cones define the reflexive causal order; proper
  time appears only in the distance formula.

---

## (e) The three confirmations agree — and where they differ

| Axis | Lean (T1) | Numerical (T4) | Literature (T5) |
|---|---|---|---|
| Static axioms (F1)–(F5) | satisfiable (positive cone) | grading cone passes (F1)–(F3) | portable to finite algebras |
| Dynamical content | **killed**: `i[D,f]`-PSD + (F1)–(F5) impossible for non-central D | **killed**: (F5) × (F6) jointly unsatisfiable; M+M† ≡ 0 | Besnard: M₃(ℂ) egalitarian (trivial order) |
| Krein (F6) form | open in Lean (stated, no verdict) | **killed numerically**: statable ⟺ commutant | no twisted-triple results exist |
| Semantics (F8, duality, distance) | — | — | manifold-level, un-crossed |

The Lean kill and the numerical kill are *independent mechanisms*
(trace-collapse vs Hermitian-part vanishing) converging on the same
conclusion — this is not one argument repeated three ways.

---

## (f) Manifold admission price (exact)

Causality is the first bridge span whose admission price is **entirely
manifold-side**. For a causal cone to exist, the manifold factor must
supply:

1. **Points** — pure states to order (F7), and enough of them for the
   order to be non-trivial (the finite state space gives only the
   trivial order on the M₃(ℂ) summand, by Besnard).
2. **A Lorentzian metric with Clifford relations** — what makes
   `J[D,f]` self-adjoint (Besnard §7); the finite transplant lacks
   this relation, which is why (F6) collapses to the commutant.
3. **Global hyperbolicity** — for the recovery theorem (F8) that turns
   the algebraic order into spacetime causal order.
4. **Non-compactness** — no compact causal spacetimes; the finite
   setting's compactness is part of the obstruction's environment.

None of these is purchasable inside the finite triple. The bridge's
algebraic pylons (twist, Krein, reality prescription) stand; the
causal span cannot be built from this side.

---

## (g) T1 / T4 / T5 ledger for Span 5

### T1 — machine-checked

`lean/ThetLogos/TwistedTriple.lean` §10 (~560 lines, commit `841fad4`)
— build green (3324 jobs), zero sorrys, axioms
`[propext, Classical.choice, Quot.sound]`. 23 theorems including
`causalCone_obstruction` (the kill), `causalCone_forces_central`,
`dyn_comm_eq_zero`, `posSemidef_trace_eq_zero`, `trace_comm_eq_zero`,
`psdCone_static` (+ `psd_spanning` Jordan decomposition),
`causalLE_refl`/`causalLE_trans`. T2: `IsPosSemidef`,
`IsCausalConeStatic`, `IsDynamicallyCompatible`, `IsLorentzCompatible`
(no verdict), `CausalLE`.

### T4 — numerical

`scripts/causality_span5_lab.py` (commit `c3b721a`, seeds 2026/202607):
Krein-positive cone = {0} (spectrum ±eig(A), 6.3e-16); grading cone =
ordinary positive cone (trivial); flip preservation 0.000e+00;
Krein clash (400/400 R-indefinite); `‖M+M†‖` = 0.000e+00 identically;
statability ⟺ commutant (500/500); commutant dims 3<6 / 6<12.

### T5 — pinned / survey

- Literature ledger: Franco (F1)–(F6) portable-but-semantics-manifold;
  Besnard egalitarian (M₃(ℂ) trivial); no finite-alone or twisted
  causal results anywhere.
- J-form (F6) in Lean: stated, no verdict (numerical kill covers it).
- ℍ summand vs Besnard's theorem: unexamined, flagged.
- Remaining canyon: **continuum** (the limit procedure — unbuilt; the
  thermal-phase-transition ban stands), **BW analog** (still
  quarantined — localization does not exist).
- Lorentzian signature: still not effected (Span 3 ledger entry
  unchanged).

### T2 / T3

T2: the five §10 defs above. T3: none.

---

## Span verdict

**KILL — clean, triple-confirmed, valuable.** No Franco-style causal
cone exists on the finite triple: Lean proves the `i[D,f]`-dynamical
variant impossible for non-central D (trace-collapse); numerics show
the Krein (F6)-form statable only on the commutant, making spanning
and the operator inequality jointly unsatisfiable; the literature has
never built one and Besnard's egalitarian theorem independently
trivializes the M₃(ℂ) summand. The twist is preserved exactly and the
Krein structure stands — causality fails for its own reasons, not
theirs.

**The bridge so far:** twist ✓ (Span 2), Krein structure ✓ (Span 3),
reality prescription ✓ (Span 4), causality ✗ (Span 5 — killed).
Remaining canyon: **continuum**, quarantined **BW analog**. The
manifold admission price for causality is named exactly in §(f).

Killed claims stay killed: flow twist, naive `ρ(a) = ΓaΓ`, single-H η,
the lab's wrong commutant-obstruction argument, thermomagnetic
cloaking language, and now the finite causal cone — none appear as
live entries. Per the relabeling rule, a causal cone returns only as
a NEW entry: on the manifold factor, with points, Clifford relations,
and global hyperbolicity in hand.
