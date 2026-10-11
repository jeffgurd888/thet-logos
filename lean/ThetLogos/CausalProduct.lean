import ThetLogos.TwistedTriple

namespace ThetLogos

/-!
# ThetLogos.CausalProduct — causality re-entry on the almost-commutative product

**Bridge Span 5 re-entry (Rung 2), 2026-10-08.** Span 5 killed the causal
cone on the finite triple three ways (Lean obstruction + numerical no-go +
Besnard): `causalCone_obstruction` (TwistedTriple.lean §10) proves no set
satisfies (F1)–(F5) jointly with `i[D,f]`-PSD when `D` is self-adjoint and
non-central. This module asks the re-entry question: **does the obstruction
carry over to the almost-commutative product `C^∞(M) ⊗ A_F`?**

**Verdict (T1 + sharp T2): the obstruction does NOT carry over.**
The failing hypothesis is the proof's *engine*, not any of the four stated
hypotheses:

- On the finite triple, `dyn_comm_eq_zero` factors through
  `trace_comm_eq_zero : Matrix.trace (D*f - f*D) = 0` (finite cyclicity)
  and `posSemidef_trace_eq_zero` (PSD + trace 0 ⟹ zero) — both typed over
  `Matrix n n ℂ` with `[Fintype n]`.
- On the product, `[D_prod, f]` is **not trace-class**: the trace over the
  manifold factor `L²(M,S)` diverges (D_prod is unbounded; `i[D_M, f]` is a
  bounded nonzero multiplication-type operator with infinite trace-class
  norm — see `scripts/causality_product_trace_lab.py`, T4). So the collapse
  `PSD ⟹ = 0` cannot be invoked.

The failure is exhibited as a proved theorem: no "trace-collapse
functional" `τ` (the two properties the finite engine needs) exists on the
product (`trace_collapse_hypothesis_fails`, T1), given the sharp T2
manifold admission-price axiom `prod_nonzero_causal_commutator` — a cone
function with `i[D_prod, f]` PSD but `[D_prod, f] ≠ 0`. On the finite
triple this combination was *proved impossible* (`dyn_comm_eq_zero`); on
the product it is the manifold fact that rescues spanning.

**Carried pylons (no Lorentzian claims without them).** The Krein structure
(Span 3, `swapR`) and reality prescription (Span 4) stand on the finite
factor; the product adds the manifold Krein factor `ηprod` and the
Clifford relation `prod_clifford_hermitian` — the exact relation the
finite transplant lacked (Span-5 numerics: `‖M + M†‖ ≡ 0` identically, so
the J-form was not even statable there). Here the J-form
(`IsProdLorentzCompatible`) IS statable; its joint
spanning+inequality satisfiability is NOT proved (PIN).

**Remaining admission price (PIN).** Global hyperbolicity
(`GloballyHyperbolicM`, T2 axiom): the recovery theorem (F8) — that the
algebraic order recovers spacetime causal order — is not proved here.

Tier ledger for this module:
- T2 defs: `IsOpPSD`, `IsProdCausalConeStatic`,
  `IsProdDynamicallyCompatible`, `IsProdLorentzCompatible`, `ProdCausalLE`,
  `HasFiniteTraceCollapse`.
- T2/T5 axioms: `Hprod`, `M`, `ProdOp` (+ ring/scaling interface),
  `prodForm`, `prodSmul` (+ comp/one/zero laws), `Dprod` (+ self-adjoint,
  non-central), `ηprod` (+ fundamental symmetry), `Cprod`,
  `prod_coord_in_cone`, `prod_clifford_hermitian`,
  `prod_nonzero_causal_commutator`, `GloballyHyperbolicM` (PIN).
- T1 theorems: `trace_collapse_hypothesis_fails` (the verdict),
  `product_not_forced_central` (the finite conclusion falsified).
-/

/-! ## §1. Product data (T2 defs, T5 axioms) -/

/-- T5: the Lorentzian spin manifold `M` (axiomatized). For a genuine causal
    order this must be globally hyperbolic (hence non-compact) — see
    `GloballyHyperbolicM` (PIN). The finite triple's "compactness" is part
    of what the manifold factor leaves behind. -/
axiom M : Type

/-- T5: the product Hilbert space `H_prod = L²(M,S) ⊗ ℂ³²` (axiomatized).
    Infinite-dimensional — this is the whole point: no finite trace. -/
axiom Hprod : Type

/-- T2: the product operator algebra (bounded operators on `Hprod`),
    axiomatized minimally as a ring. -/
axiom ProdOp : Type
axiom prodOpRing : Ring ProdOp
attribute [instance] prodOpRing

/-- T2: the ∗-structure on product operators (axiomatized). -/
axiom prodStar : ProdOp → ProdOp

/-- T2: the sesquilinear form `⟨ψ, A ψ⟩` on `Hprod` (axiomatized). -/
axiom prodForm : Hprod → ProdOp → Hprod → ℂ

/-- T2: ℂ-scaling of product operators (axiomatized scalar action). -/
axiom prodSmul : ℂ → ProdOp → ProdOp

/-- T2: scaling composes by multiplication. -/
axiom prodSmul_comp : ∀ (a b : ℂ) (X : ProdOp),
    prodSmul a (prodSmul b X) = prodSmul (a * b) X

/-- T2: scaling by 1 is the identity. -/
axiom prodSmul_one : ∀ X : ProdOp, prodSmul 1 X = X

/-- T2: scaling the zero operator gives zero. -/
axiom prodSmul_zero_op : ∀ c : ℂ, prodSmul c 0 = 0

/-- T2: PSD for product operators (form-based, mirroring `IsPosSemidef`
    of §10): self-adjoint with nonnegative real form on all vectors. -/
def IsOpPSD (A : ProdOp) : Prop :=
  prodStar A = A ∧ ∀ ψ : Hprod, 0 ≤ (prodForm ψ A ψ).re

/-- T5: the product Dirac `D_prod = D_M ⊗ 1 + γ₅ ⊗ D_F` (axiomatized). -/
axiom Dprod : ProdOp

/-- T2: `D_prod` is self-adjoint (manifold + finite parts both are). -/
axiom dprod_selfadj : prodStar Dprod = Dprod

/-- T2: `D_prod` is non-central on self-adjoints (inherited from both
    factors: `D_M` does not commute with multiplication operators, `D_F`
    has Yukawa structure). -/
axiom dprod_noncentral :
    ∃ a : ProdOp, prodStar a = a ∧ Dprod * a - a * Dprod ≠ 0

/-- T2: the product fundamental symmetry (Krein structure carried over:
    Span 3's `swapR` on the finite factor tensored with the manifold
    Krein factor). `η² = 1`, `ηᴴ = η`. -/
axiom ηprod : ProdOp
axiom ηprod_sq : ηprod * ηprod = 1
axiom ηprod_selfadj : prodStar ηprod = ηprod

/-- T5: the causal cone on the product (axiomatized membership): the
    `i[D_prod, f]`-positive cone for `f ∈ C^∞(M)` — manifold coordinate
    functions now exist, which is exactly what the finite triple lacked. -/
axiom Cprod : Set ProdOp

/-- **Manifold admission price, part 1 (T2 axiom).** Manifold coordinate
    functions exist in the cone and are self-adjoint. The finite triple had
    no spacetime points; the product has functions to order. -/
axiom prod_coord_in_cone :
    ∃ f : ProdOp, f ∈ Cprod ∧ prodStar f = f

/-- **Manifold admission price, part 2 (T2 axiom).** The Clifford relation:
    for cone functions, `η[D_prod, f]` IS Hermitian. This is the exact
    relation the finite transplant lacked — Span-5 numerics showed
    `‖M + M†‖ ≡ 0` identically for `M(a) = R[D̃, π̃(a,a)]`, so the Krein
    J-form was not even statable there (Besnard §7: Clifford relations are
    what make `J[D,f]` self-adjoint). On the product the J-form
    (`IsProdLorentzCompatible`) is statable. -/
axiom prod_clifford_hermitian : ∀ f : ProdOp, f ∈ Cprod → prodStar f = f →
    prodStar (ηprod * (Dprod * f - f * Dprod))
      = ηprod * (Dprod * f - f * Dprod)

/-- **Manifold admission price, part 3 (T2 axiom) — the trace-rescue
    exhibit.** There is a cone function `f` with `i[D_prod, f]`
    positive semidefinite but `[D_prod, f] ≠ 0`. On the finite triple this
    combination was PROVED impossible (`dyn_comm_eq_zero`: PSD +
    `Tr(i[D,f]) = 0` forces `[D,f] = 0`). On the product it holds because
    the commutator is not trace-class — the trace over the manifold factor
    `L²(M,S)` diverges, so the finite proof's engine cannot run. T4
    support: `scripts/causality_product_trace_lab.py` (trace-class norm
    `‖[D_N, f_N]‖₁ ~ c·N → ∞` while `Tr_N([D_N,f_N]) ≡ 0` at every finite
    truncation). -/
axiom prod_nonzero_causal_commutator :
    ∃ f : ProdOp, f ∈ Cprod ∧ prodStar f = f ∧
      IsOpPSD (prodSmul Complex.I (Dprod * f - f * Dprod)) ∧
      (Dprod * f - f * Dprod) ≠ 0

/-! ## §2. Causal cone axioms on the product (T2 defs) -/

/-- The static Franco axioms on the product (T2 — definition): mirror of
    `IsCausalConeStatic` (§10) with `prodStar`/`prodSmul` in place of
    `ᴴ`/`•`. (F1) Hermitian, (F2) sum-stable, (F3) positive homogeneity,
    (F5) spanning (`C - C = A_sa`), (F4) weakened to `1 ∈ C` as in §10. -/
def IsProdCausalConeStatic (C : Set ProdOp) : Prop :=
  (∀ a ∈ C, prodStar a = a)
    ∧ 0 ∈ C
    ∧ (∀ a ∈ C, ∀ b ∈ C, a + b ∈ C)
    ∧ (∀ a ∈ C, ∀ r : ℝ, 0 ≤ r → prodSmul (r : ℂ) a ∈ C)
    ∧ (∀ a : ProdOp, prodStar a = a →
        ∃ f g : ProdOp, f ∈ C ∧ g ∈ C ∧ a = f - g)
    ∧ 1 ∈ C

/-- Dynamical compatibility on the product (T2 — definition): mirror of
    `IsDynamicallyCompatible` (§10) — every `f ∈ C` has `i[D_prod, f]` PSD.
    This is the §10-native `i[D,f]`-variant, NOT Franco's Krein (F6). -/
def IsProdDynamicallyCompatible (D : ProdOp) (C : Set ProdOp) : Prop :=
  ∀ f ∈ C, IsOpPSD (prodSmul Complex.I (D * f - f * D))

/-- The Lorentzian dynamical axiom on the product (T2 — definition, NO
    verdict on joint satisfiability): mirror of `IsLorentzCompatible`
    (§10) — the form version of Franco's (F6) `⟨φ, J[D,a]φ⟩ ≤ 0` with the
    carried-over fundamental symmetry `ηprod`. Unlike §10, this IS
    statable here: `prod_clifford_hermitian` makes the form's operator
    Hermitian for cone functions. -/
def IsProdLorentzCompatible (η D : ProdOp) (C : Set ProdOp) : Prop :=
  ∀ a ∈ C, ∀ ψ : Hprod, (prodForm ψ (η * (D * a - a * D)) ψ).re ≤ 0

/-- The causal order on the product (T2 — definition): mirror of
    `CausalLE` (§10), `f ≤[C] g` iff `g - f ∈ C`. -/
def ProdCausalLE (C : Set ProdOp) (f g : ProdOp) : Prop :=
  g - f ∈ C

/-! ## §3. Which hypothesis of `causalCone_obstruction` fails (T1 verdict) -/

/-- A "trace-collapse functional" (T2 — definition): the two properties
    the finite proof's engine actually uses —
    `trace_comm_eq_zero` (`Tr(i[D,f]) = 0`, finite cyclicity) and
    `posSemidef_trace_eq_zero` (PSD + trace 0 ⟹ zero). `dyn_comm_eq_zero`
    is exactly "every trace-collapse functional forces `[D,f] = 0`". -/
def HasFiniteTraceCollapse (τ : ProdOp → ℂ) : Prop :=
  (∀ f : ProdOp, τ (prodSmul Complex.I (Dprod * f - f * Dprod)) = 0) ∧
  (∀ A : ProdOp, IsOpPSD A → τ A = 0 → A = 0)

/-- **The verdict (T1 — proved): the trace-collapse hypothesis fails on
    the product.** No trace-collapse functional exists: the manifold
    admission price (`prod_nonzero_causal_commutator`) supplies a cone
    function `f` with `i[D_prod, f]` PSD but `[D_prod, f] ≠ 0`, and any
    collapse functional would force `i[D_prod, f] = 0`, hence
    `[D_prod, f] = 0` — contradiction. This is the exact hypothesis of
    `causalCone_obstruction` that the product defeats: the finite proof's
    engine (`trace_comm_eq_zero` + `posSemidef_trace_eq_zero`, typed over
    `Matrix n n ℂ` with `[Fintype n]`) cannot run where the trace over the
    manifold factor is infinite. None of the four *stated* hypotheses
    (self-adjoint `D`, non-central `D`, static cone, `i[D,f]`-PSD) fails —
    all four can hold on the product; it is the *unstated ambient*
    hypothesis (finite matrices ⇒ finite trace) that fails. -/
theorem trace_collapse_hypothesis_fails :
    ¬ ∃ τ : ProdOp → ℂ, HasFiniteTraceCollapse τ := by
  rintro ⟨τ, hvanish, hcollapse⟩
  obtain ⟨f, hfC, hfsa, hpsd, hne⟩ := prod_nonzero_causal_commutator
  have h0 : prodSmul Complex.I (Dprod * f - f * Dprod) = 0 :=
    hcollapse _ hpsd (hvanish f)
  have key : Dprod * f - f * Dprod = 0 := by
    have e : prodSmul (-Complex.I) (prodSmul Complex.I (Dprod * f - f * Dprod))
        = Dprod * f - f * Dprod := by
      rw [prodSmul_comp]
      have hII : (-Complex.I) * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      rw [hII, prodSmul_one]
    rw [h0, prodSmul_zero_op] at e
    exact e.symm
  exact hne key

/-- **The finite conclusion is falsified on the product (T1 — proved).**
    `causalCone_forces_central` concludes `∀ a` self-adjoint,
    `[D, a] = 0` on the finite triple; on the product this conclusion is
    false — the manifold factor keeps `D_prod` non-central even on the
    cone. Hence `causalCone_obstruction` does not carry over. -/
theorem product_not_forced_central :
    ¬ ∀ a : ProdOp, prodStar a = a → Dprod * a - a * Dprod = 0 := by
  intro h
  obtain ⟨f, hfC, hfsa, hpsd, hne⟩ := prod_nonzero_causal_commutator
  exact hne (h f hfsa)

/-! ## §4. Global hyperbolicity — the remaining admission price (PIN) -/

/-- T2 axiom (PIN): the manifold factor is globally hyperbolic. This is
    the remaining admission price for a *genuine* causal order: Franco's
    recovery theorem (F8) — that the algebraic order `ProdCausalLE` on
    pure states recovers the spacetime causal relation — needs global
    hyperbolicity (hence non-compactness; no compact causal spacetimes).
    NOT discharged here: no recovery theorem is claimed. Status: PIN. -/
axiom GloballyHyperbolicM : Prop

#print axioms trace_collapse_hypothesis_fails
#print axioms product_not_forced_central

end ThetLogos
