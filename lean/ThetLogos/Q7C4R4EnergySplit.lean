import Mathlib.Tactic
import ThetLogos.Q7C4R4Trifecta
import ThetLogos.Q7C4R4Dynamics

namespace ThetLogos

open TensorProduct

/-!
# ThetLogos.Q7C4R4EnergySplit — T-Q7-2: the First-leg energy test

**Status: TEST EXECUTED — the registered splitting DISCHARGES at
its registered (interaction-free) seat. K-T-Q7-2 does NOT fire.
NO CLAIM. Dials 0/4. No measured number.**

Governing pack: `routeb-general-scratch/pack-t-q7-2.md`;
governing memo: `routeb-general-scratch/
scoping-q7c4r4-trifecta-2026-10-30.md`; registration:
`ThetLogos.Q7C4R4Trifecta` (Q7CR-T0). Gate named in the memo's
§4 table for this brick: Q7CR-1b (`ThetLogos.Q7C4R4Assembly`,
landed). The instantiated seat additionally consumes Q7CR-2's
factor packages (`ThetLogos.Q7C4R4Spectrum`: `factorQ7`,
`factorC4`, `factorR`) and Q7CR-5's dynamics
(`ThetLogos.Q7C4R4Dynamics`: `dynGen`, `dynGibbs`,
`dynGibbsState`). Module name chosen here:
`Q7C4R4EnergySplit` — beside `Q7C4R4FirstLeg` (T-Q7-1's home),
the registration module untouched.

## The registered target, quoted verbatim (memo location)

Memo §2.1, item (ii), brick T-Q7-2:

> **(ii) FINITE-TESTABLE — energy additivity (brick T-Q7-2).**
> The First Law's actual content is energy bookkeeping, and its
> finite core is statable: for the Q7CR-1 factor operator
> packages assembled without interaction terms, the composite
> Hamiltonian's expectation on product states splits as the sum
> of factor expectations. Falsifiable in form: the moment a
> later instantiation adds an interaction term, the splitting
> fails on entangled states and the leg survives only in the
> non-interacting form, recorded as such.

Memo §4, priced-path row:

> | **T-Q7-2** | First-Law bookkeeping: product-state
> energy-expectation splitting for the interaction-free
> assembly | **S–M** | Q7CR-1b |

Memo §4, the armed kill K-T-Q7-2:

> **K-T-Q7-2** an interaction-bearing instantiation breaking
> the splitting on product states ⇒ leg survives
> non-interacting-only, labeled.

This is NOT the capacity form: the capacity identification was
T-Q7-1's target and K-T-Q7-1 already fired on it
(`Q7C4R4FirstLeg.legFirstCapacity_realified_false`); that kill
stands untouched beside this brick. This is also NOT the
unregistered pair-total candidate reported by T-Q7-1: no
entropy functional is consumed here at all, because the
registered T-Q7-2 target is energy bookkeeping, not entropy —
the pack's entropy instruction applies "where the test needs"
it, and this registered test needs none.

## How the registered words are instantiated, in owned vocabulary

- "Composite Hamiltonian": the corpus's own Hamiltonian-shaped
  object of the assembly is the square of the product Dirac —
  Q7CR-5 registers exactly this choice (`dynGen := diracInst^2`,
  "CHOSEN generator"). At general packages (Q7CR-1b) it is
  `(diracQ7C4R4 F₇ F₄ F_R)^2`, and Q7CR-1b's landed D² identity
  says it IS the interaction-free Kronecker sum
  `D₇² ⊗ 1 ⊗ 1 + 1 ⊗ D₄² ⊗ 1 + 1 ⊗ 1 ⊗ D_R²`
  (`diracQ7C4R4_sq`). §1 defines that sum as `hamAssembly` and
  proves the identification.
- "Expectation": the form expectation for the registered
  composite pairing, `compositePair (H ψ) ψ` (Q7CR-1b's lifted
  pairing), and factorwise `factorPair n (Hᵢ x) x` /
  `minkowskiInner (H_R z) z`, with factor Hamiltonians
  `Hᵢ := Dᵢ²` — the summands the D² identity actually carries.
- "Product states": pure tensors `(x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z`.
- "Splits as the sum of factor expectations": §2 first proves
  the exact weighted form with NO hypotheses (each factor term
  carries the other two factors' self-pairings as weights —
  the honest general identity), then the registered splitting
  in its plain form under the product state's normalization
  (each factor self-pairing `= 1`).

## The deciding computation

`compositePair` evaluates on pure tensors factorwise
(`compositePair_tmul`), and each Kronecker summand acts on a
pure tensor factorwise (`opTensorQ_tmul`); the three summands
therefore contribute exactly the three weighted factor terms,
and no cross term exists — there is no interaction term in
the assembly to produce one. §4 makes the scope boundary
exact: adjoining ANY operator `W` as an interaction term adds
exactly `compositePair (W ψ) ψ` to the expectation, so the
plain splitting for an interaction-bearing assembly holds iff
that extra term vanishes — K-T-Q7-2's trigger, stated as a
term, at this seat. At the registered interaction-free seat
the extra term is absent and the splitting discharges.

## Verdict

**T-Q7-2 DISCHARGES AS REGISTERED at the interaction-free
assembly: on normalized product states the composite
Hamiltonian's expectation is exactly the sum of the three
factor expectations, for arbitrary Q7CR-1 factor packages
(§2), at Q7CR-2's instantiated packages (§3, with a concrete
basis computation), and at Q7CR-5's Gibbs seat the composite
Gibbs expectation of the Hamiltonian's eigenvalue splits as
the sum of its three factor-observable expectations (§3).
K-T-Q7-2 does NOT fire; it remains armed against any later
interaction-bearing instantiation (§4).**

**Leg status line (First leg): capacity DEAD (K-T-Q7-1);
energy additivity DISCHARGED at the interaction-free assembly
(T-Q7-2, this brick) — the leg stands on definition +
additivity only, the capacity identification not revived.**

The trifecta assignment itself is Jeff's registered DATA;
this brick tests one leg's stated consequence only and
promotes nothing.
-/

/-! ## §1. The interaction-free Hamiltonian assembly -/

/-- **Factor energy expectation** (complex factors): the form
expectation of the factor Hamiltonian `F.D ^ 2` — the factor
square the D² identity carries — for the registered factor
pairing. Tier T1 (definition). -/
noncomputable def factorEnergyC {n : ℕ} (F : FactorOp n) (x : Fin n → ℂ) : ℝ :=
  factorPair n ((F.D ^ 2) x) x

/-- **Factor energy expectation** (R⁴ factor): the form
expectation of `F.D ^ 2` for the Minkowski pairing.
Tier T1 (definition). -/
def factorEnergyR (F : FactorOpR) (z : Minkowski) : ℝ :=
  minkowskiInner ((F.D ^ 2) z) z

/-- **The interaction-free composite Hamiltonian assembly**:
the Kronecker sum of the factor squares,
`D₇² ⊗ 1 ⊗ 1 + 1 ⊗ D₄² ⊗ 1 + 1 ⊗ 1 ⊗ D_R²`. By construction
it has NO interaction term: every summand acts on one factor
and as the identity on the other two. Tier T1 (definition). -/
noncomputable def hamAssembly (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) : Module.End ℝ q7c4r4Composite :=
  opTensorQ (F₇.D ^ 2) 1 1 + opTensorQ 1 (F₄.D ^ 2) 1
    + opTensorQ 1 1 (F_R.D ^ 2)

/-- **The assembly IS the composite Hamiltonian**: the
Kronecker sum is the square of Q7CR-1b's product Dirac — the
general form of Q7CR-5's CHOSEN generator `dynGen`. This is
Q7CR-1b's landed D² identity, read in the direction this
brick consumes. Tier T1. -/
theorem hamAssembly_eq_dirac_sq (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR) :
    hamAssembly F₇ F₄ F_R = (diracQ7C4R4 F₇ F₄ F_R) ^ 2 :=
  (diracQ7C4R4_sq F₇ F₄ F_R).symm

/-- **Composite energy expectation**: the form expectation of
the composite Hamiltonian for the registered composite
pairing. Tier T1 (definition). -/
noncomputable def compEnergy (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) (ψ : q7c4r4Composite) : ℝ :=
  compositePair (hamAssembly F₇ F₄ F_R ψ) ψ

/-- A **product state** of the three factors, in the
registered association. Tier T1 (definition). -/
noncomputable def prodState (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski) :
    q7c4r4Composite :=
  (x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z

/-! ## §2. The splitting: exact weighted form, then the
registered form under normalization -/

/-- **The exact weighted splitting, no hypotheses.** On a
product state, the composite expectation is the sum of the
three factor expectations, each weighted by the other two
factors' self-pairings. The computation is factorwise
evaluation of the registered pairing on pure tensors; there
is no cross term, because the assembly has no interaction
term. Tier T1. -/
theorem compEnergy_prod_weighted (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski) :
    compEnergy F₇ F₄ F_R (prodState x y z)
      = factorEnergyC F₇ x * factorPair 4 y y * minkowskiInner z z
        + factorPair 7 x x * factorEnergyC F₄ y * minkowskiInner z z
        + factorPair 7 x x * factorPair 4 y y * factorEnergyR F_R z := by
  unfold compEnergy prodState hamAssembly factorEnergyC factorEnergyR
  rw [LinearMap.add_apply, LinearMap.add_apply, opTensorQ_tmul,
    opTensorQ_tmul, opTensorQ_tmul]
  simp only [Module.End.one_apply, map_add, LinearMap.add_apply,
    compositePair_tmul]

/-- **T-Q7-2, DISCHARGED AS REGISTERED.** For the Q7CR-1
factor operator packages assembled without interaction
terms, the composite Hamiltonian's expectation on a
normalized product state (each factor self-pairing `= 1`)
splits as the sum of the factor expectations — for
arbitrary packages, at the gate the memo names (Q7CR-1b).
Tier T1. -/
theorem compEnergy_prod_split (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski)
    (hx : factorPair 7 x x = 1) (hy : factorPair 4 y y = 1)
    (hz : minkowskiInner z z = 1) :
    compEnergy F₇ F₄ F_R (prodState x y z)
      = factorEnergyC F₇ x + factorEnergyC F₄ y
        + factorEnergyR F_R z := by
  rw [compEnergy_prod_weighted, hx, hy, hz]
  ring

/-! ## §3. The instantiated seats: Q7CR-2's packages and
Q7CR-5's Gibbs dynamics -/

/-- The splitting at Q7CR-2's instantiated factor packages
(`factorQ7`, `factorC4`, `factorR`), on normalized product
states. Tier T1. -/
theorem compEnergy_prod_split_inst (x : Fin 7 → ℂ)
    (y : Fin 4 → ℂ) (z : Minkowski)
    (hx : factorPair 7 x x = 1) (hy : factorPair 4 y y = 1)
    (hz : minkowskiInner z z = 1) :
    compEnergy factorQ7 factorC4 factorR (prodState x y z)
      = factorEnergyC factorQ7 x + factorEnergyC factorC4 y
        + factorEnergyR factorR z :=
  compEnergy_prod_split factorQ7 factorC4 factorR x y z hx hy hz

/-- Q⁷ factor energy of a real site basis vector: its site
square `a₇ k ^ 2` (the eigen lemma `factorQ7_basisC_eigen`,
paired against the orthonormal basis). Tier T1. -/
theorem factorEnergyC_factorQ7_basis (k : Fin 7) (b : Fin 2) :
    factorEnergyC factorQ7 (basisC 7 (k, b)) = a₇ k ^ 2 := by
  unfold factorEnergyC
  rw [factorQ7_basisC_eigen, factorPair_smul_left,
    factorPair_basisC]
  simp

/-- C⁴ factor energy of a real site basis vector: its site
square `d₄ k ^ 2`. Tier T1. -/
theorem factorEnergyC_factorC4_basis (k : Fin 4) (b : Fin 2) :
    factorEnergyC factorC4 (basisC 4 (k, b)) = d₄ k ^ 2 := by
  unfold factorEnergyC
  rw [factorC4_basisC_eigen, factorPair_smul_left,
    factorPair_basisC]
  simp

/-- Left homogeneity of the Minkowski pairing. Tier T1. -/
theorem minkowskiInner_smul_left (a : ℝ) (z w : Minkowski) :
    minkowskiInner (a • z) w = a * minkowskiInner z w := by
  unfold minkowskiInner
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- R⁴ factor energy of a site basis vector: its site square
times the site's η-sign (the pairing's diagonal value).
Tier T1. -/
theorem factorEnergyR_factorR_basis (m : Fin 4) :
    factorEnergyR factorR ((Pi.basisFun ℝ (Fin 4)) m)
      = (r_R m ^ 2) * minkSign m := by
  unfold factorEnergyR
  rw [factorR_basis_eigen, minkowskiInner_smul_left,
    minkowskiInner_basisFun]
  simp

/-- **The deciding computation at the instantiated seat.**
On the product of real site basis vectors at the time site
`0` of R⁴ (self-pairings: `1`, `1`, and `minkSign 0 = 1`),
the composite expectation is exactly the sum of the factor
site squares — and that sum is Q7CR-2's composite eigenvalue
`eigComp` at the same index. Tier T1. -/
theorem compEnergy_basis_product (k₇ : Fin 7) (b₇ : Fin 2)
    (k₄ : Fin 4) (b₄ : Fin 2) :
    compEnergy factorQ7 factorC4 factorR
        (prodState (basisC 7 (k₇, b₇)) (basisC 4 (k₄, b₄))
          ((Pi.basisFun ℝ (Fin 4)) 0))
      = eigComp (((k₇, b₇), (k₄, b₄)), 0) := by
  have h₇ : factorPair 7 (basisC 7 (k₇, b₇)) (basisC 7 (k₇, b₇))
      = 1 := by rw [factorPair_basisC]; simp
  have h₄ : factorPair 4 (basisC 4 (k₄, b₄)) (basisC 4 (k₄, b₄))
      = 1 := by rw [factorPair_basisC]; simp
  have hR : minkowskiInner ((Pi.basisFun ℝ (Fin 4)) 0)
      ((Pi.basisFun ℝ (Fin 4)) 0) = 1 := by
    rw [minkowskiInner_basisFun]; simp [minkSign]
  rw [compEnergy_prod_split_inst _ _ _ h₇ h₄ hR,
    factorEnergyC_factorQ7_basis, factorEnergyC_factorC4_basis,
    factorEnergyR_factorR_basis, eigComp_eq]
  simp [minkSign, r_R]

/-- **The Gibbs seat (Q7CR-5).** The composite Gibbs
expectation of the CHOSEN generator's eigenvalue function
splits as the sum of the three factor-observable
expectations under the same composite Gibbs weights:
energy additivity at the thermal seat, in the exact form
the landed `dynGibbsState` / `eigComp` vocabulary carries.
Tier T1. -/
theorem dynGibbsState_eigComp_split (β : ℝ) :
    dynGibbsState β eigComp
      = dynGibbsState β (fun t => s₇c t.1.1)
        + dynGibbsState β (fun t => s₄c t.1.2)
        + dynGibbsState β (fun t => s_R t.2) := by
  unfold dynGibbsState eigComp
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-! ## §4. The scope boundary: what an interaction term adds
(K-T-Q7-2's trigger, stated as a term) -/

/-- **Interaction boundary, exact.** Adjoining ANY operator
`W` to the interaction-free Hamiltonian changes the product
state expectation by exactly the interaction term's own
expectation `compositePair (W ψ) ψ` — no more, no less.
Hence a plain sum-splitting for an interaction-bearing
assembly at a product state holds if and only if that extra
term vanishes there: that vanishing's failure is precisely
K-T-Q7-2's registered trigger, and it is ABSENT at the
registered seat of §2, where no `W` is adjoined. This
theorem bounds the §2 verdict to the non-interacting form,
exactly as the memo's kill registers the leg's survival
mode. Tier T1. -/
theorem compEnergy_add_interaction (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (W : Module.End ℝ q7c4r4Composite)
    (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski) :
    compositePair ((hamAssembly F₇ F₄ F_R + W)
        (prodState x y z)) (prodState x y z)
      = compEnergy F₇ F₄ F_R (prodState x y z)
        + compositePair (W (prodState x y z))
            (prodState x y z) := by
  unfold compEnergy
  rw [LinearMap.add_apply, map_add, LinearMap.add_apply]

end ThetLogos
