/-
# LeibnizGibbsBridgePin — the Leibniz–Gibbs bridge, in finite form

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials 0/4
under every outcome.**

Commissioned: Zero, 2026-11-19 11:32 EST — "we need a leibniz gibbs
bridge" — inside his thermodynamics seeing-sequence of the same
morning. Scope of record:
`leibniz-gibbs-bridge-scope-2026-11-19.md` (T5 scope; its §0
strike-check repriced this pin to its genuine delta before any brick
fired).

## The seat

Leibniz's dyadic arithmetic and Gibbs's statistical mechanics meet
at one precise finite point: the configuration space of a two-state
seat *is* the set of binary strings. A configuration of `n` binary
links is a function `Fin n → Bool` — which is, definitionally, the
row type of the corpus's own `LeibnizPin` (`dotRow (k) (n) :
Fin k → Bool`) — and there are `2 ^ n` of them, Boltzmann's `W` for
the binary seat. This module puts a Gibbs state on that seat and
proves the finite bridge statements: the partition function of a
sum-over-links energy factorizes over the links (LG-2, heterogeneous
links allowed), the Gibbs state of the sum energy *is* the product
of the per-link Gibbs states (LG-2 — the joint between the census
partition line, `ModularVariance`, and the census entropy line,
`FiniteEntropy` / `SiteEntropyMap`), and at uniformity the entropy
of the dyadic seat is `n * log 2`, Planck-scaled `k * n * log 2`
(LG-3, by citation of census additivity and census saturation —
no additivity is re-proved here).

## Fences (armed in the scope, carried on this module's face)

- **K-LG-DUPLICATE** (headline): every brick was strike-checked
  against the census shelf before drafting. Census already owns
  product-weight additivity (`entropyW_siteProdWeight`, stronger
  and general), the uniform-saturation iff
  (`entropyW_eq_log_card_iff`), and the row encoding's exactness
  (`dotRow`); the dyadic factorization instance is owned at lane
  grade by `StringResponsePin` at `k = 1`. What is proved here is
  only what that shelf does not own: the heterogeneous per-site
  factorization and the `gibbsProb`/`siteProdWeight` weight
  identity, plus named corollaries that cite the shelf.
- **K-LG-COSTUME**: this module proves finite identities about a
  Gibbs state on the dyadic seat. It does not show that Leibniz
  held, anticipated, or "had" statistical mechanics. Leibniz's
  binary arithmetic (1703) predates Gibbs (1902) by two centuries
  and contains no temperature, no ensemble, no entropy; the
  correspondence is between their *objects* (the string type and
  the state on it), registered as structural in the MCC registry.
- **K-LG-CALENDAR**: the calendar's binary rows are NOT
  configurations of this seat. `seatRow` and `dayRow` are encodings
  *of numbers* read on a clock face; a configuration here is a
  *state of `n` links*. The two share the type `Fin n → Bool` and
  nothing else: no theorem in this module cites a seat, a day, or
  the Boundary Day, and no calendar claim is upgraded or lent a
  tier by anything here.
- **K-LG-CORRELATE**: entropy additivity is stated ONLY for the
  Gibbs state of a sum-over-links energy, which is a product state
  by LG-2. The unrestricted form is FALSE on this very seat (the
  2-link weight `w(0,0) = w(1,1) = 1/2` has entropy `log 2` against
  site entropies summing to `2 log 2` — census witness,
  `SiteEntropyMap`'s K-TCS-ENT guard).
- **K-LG-LANDAUER**: the `k * n * log 2` corollary is a counting
  identity at uniformity whose *shape* is Landauer's. Nothing here
  erases anything, couples to a bath, or prices a process; the
  principle is not claimed as proved.

## Dependencies

Census modules only: `FiniteEntropy`, `SiteEntropyMap`,
`ModularVariance`, `LeibnizPin`. No dependency on the
Boltzmann–Shannon lane — this module is stated in census vocabulary
(`entropyW`, `partSum`, `gibbsProb`, `siteProdWeight`); restating
the lane's definitions would be a weld, and importing the lane
would chain integration for zero content.
-/

import Mathlib.Tactic
import ThetLogos.FiniteEntropy
import ThetLogos.SiteEntropyMap
import ThetLogos.ModularVariance
import ThetLogos.LeibnizPin

namespace ThetLogos

-- ============================================================================
-- LG-1. The dyadic seat and its count
-- ============================================================================

/-- **Sum-over-links energy on the dyadic seat** (definition): for
per-link energies `ε : Fin n → Bool → ℝ` — link `i` in state `s`
costs `ε i s` — the energy of a configuration `c : Fin n → Bool`
(the Leibniz row type: `false` the hollow dot, `true` the filled
dot) is the sum of its links' costs. The sum-over-links form is the
whole content of the bridge: it is the hypothesis on the face of
every factorization statement below. -/
def linkEnergy {n : ℕ} (ε : Fin n → Bool → ℝ) : (Fin n → Bool) → ℝ :=
  fun c => ∑ i, ε i (c i)

/-- The sum-over-links energy, unfolded by name (so later bricks
rewrite by name rather than by delta). -/
theorem linkEnergy_apply {n : ℕ} (ε : Fin n → Bool → ℝ) (c : Fin n → Bool) :
    linkEnergy ε c = ∑ i, ε i (c i) :=
  rfl

/-- **Boltzmann's `W` for the binary seat** (proved): there are
`2 ^ n` dyadic configurations of `n` links — the cardinality of
Leibniz's row type `Fin n → Bool`, as a named count. -/
theorem dyadic_card (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

-- ============================================================================
-- LG-2. Factorization: the pin's genuine proof
-- ============================================================================

/-- **Factorization of the partition function over links** (proved —
the pin's genuine delta): the partition function of a sum-over-links
energy is the product of the per-link partition functions,
heterogeneous links allowed — link `i` may carry its own energy
`ε i`. Route: `Real.exp_sum` turns each Boltzmann factor of a sum
into a product over links; `Finset.prod_univ_sum` turns the
configuration sum of a product into the product of the link sums.
No statement of this heterogeneous form exists on the census shelf
(strike-check, scope §0): the shelf owns the identical-link string
instance at lane grade (`StringResponsePin`), not this. -/
theorem partSum_linkEnergy {n : ℕ} (ε : Fin n → Bool → ℝ) (β : ℝ) :
    ModularVariance.partSum (linkEnergy ε) β
      = ∏ i, ModularVariance.partSum (ε i) β := by
  have hexp : ∀ c : Fin n → Bool,
      Real.exp (-(β * linkEnergy ε c))
        = ∏ i, Real.exp (-(β * ε i (c i))) := by
    intro c
    rw [linkEnergy_apply]
    have hsum : -(β * ∑ i, ε i (c i)) = ∑ i, -(β * ε i (c i)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hsum, Real.exp_sum]
  unfold ModularVariance.partSum
  rw [Finset.sum_congr rfl (fun c _ => hexp c)]
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i s => Real.exp (-(β * ε i s)))
  rw [Fintype.piFinset_univ] at h
  exact h.symm

/-- **Identical links: `Z = z ^ n`** (proved, corollary): when every
link carries the same energy `ε`, the factorized partition function
is the single-link partition function to the `n`. This is the
brief's `Z_total = z^n`, obtained here as the constant case of the
heterogeneous factorization — not by the string seat's induction. -/
theorem partSum_linkEnergy_identical {n : ℕ} (ε : Bool → ℝ) (β : ℝ) :
    ModularVariance.partSum (linkEnergy (fun _ : Fin n => ε)) β
      = (ModularVariance.partSum ε β) ^ n := by
  rw [partSum_linkEnergy, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The Gibbs state of a sum energy is the product state** (proved
— the pin's second genuine delta): the Gibbs state of the
sum-over-links energy `linkEnergy ε` *is* the product of the
per-link Gibbs states, as a `siteProdWeight`. This is the joint
between the partition side (`ModularVariance`) and the entropy side
(`SiteEntropyMap`): it is the only route by which census entropy
additivity attaches to a Gibbs state rather than to an abstract
product weight, and no statement of it exists on the shelf
(strike-check, scope §0). Numerator by `Real.exp_sum`, denominator
by `partSum_linkEnergy`, quotient by `Finset.prod_div_distrib`. -/
theorem gibbsProb_linkEnergy {n : ℕ} (ε : Fin n → Bool → ℝ) (β : ℝ) :
    ModularVariance.gibbsProb (linkEnergy ε) β
      = siteProdWeight (fun i => ModularVariance.gibbsProb (ε i) β) := by
  have hexp : ∀ c : Fin n → Bool,
      Real.exp (-(β * linkEnergy ε c))
        = ∏ i, Real.exp (-(β * ε i (c i))) := by
    intro c
    rw [linkEnergy_apply]
    have hsum : -(β * ∑ i, ε i (c i)) = ∑ i, -(β * ε i (c i)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hsum, Real.exp_sum]
  funext c
  rw [siteProdWeight_apply]
  unfold ModularVariance.gibbsProb
  rw [partSum_linkEnergy, Finset.prod_div_distrib, hexp c]

/-- **The single binary link's partition function** (proved, a
two-term evaluation): for the dyadic link energy — hollow dot `0`,
filled dot `1` — `z = 1 + e^{−β}`. DISCLOSED OVERLAP, on its face:
the same value is owned at lane grade by `StringResponsePin`'s
`siteSum_eq` at `k = 1`, on the string seat (`Fin 2`-valued links,
proved by chain induction). This is the `Bool` link of *this* seat,
evaluated directly from the definition in two terms; the string
argument is not re-run (a draft that re-ran it would die by
K-LG-DUPLICATE). -/
theorem dyadic_z (β : ℝ) :
    ModularVariance.partSum (fun s : Bool => if s then (1 : ℝ) else 0) β
      = 1 + Real.exp (-β) := by
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by
    ext b
    cases b <;> simp
  unfold ModularVariance.partSum
  rw [huniv, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp

-- LG-3. Entropy: the additivity corollary and the uniform count
-- (by citation — this brick proves no additivity and no saturation;
--  it attaches the census theorems to the dyadic Gibbs state)
-- ============================================================================

/-- **Glue:** every Gibbs state is a probability weight in the
census entropy vocabulary (packaged from census `gibbsProb_pos` +
`sum_gibbsProb`; the packaging itself was not on the shelf —
strike-check, scope §2). -/
theorem isProbWeight_gibbsProb {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) :
    IsProbWeight (ModularVariance.gibbsProb E β) :=
  ⟨fun i => (ModularVariance.gibbsProb_pos E β i).le,
   ModularVariance.sum_gibbsProb E β⟩

/-- **Additivity for the dyadic Gibbs state** (proved BY CITATION):
the entropy of the Gibbs state of a sum-over-links energy is the
sum of the per-link Gibbs entropies. The proof is two citations and
nothing else: LG-2's `gibbsProb_linkEnergy` rewrites the state as a
`siteProdWeight`, and census `entropyW_siteProdWeight` closes it.
Stated ONLY for the Gibbs state of a sum-over-links energy — which
is a product state by LG-2 — because the unrestricted form is FALSE
on this seat (K-LG-CORRELATE; census witness in `SiteEntropyMap`'s
header). This brick proves no additivity; it attaches the census
additivity to the Gibbs state. -/
theorem entropyW_gibbs_linkEnergy {n : ℕ} (ε : Fin n → Bool → ℝ) (β : ℝ) :
    entropyW (ModularVariance.gibbsProb (linkEnergy ε) β)
      = ∑ i, entropyW (ModularVariance.gibbsProb (ε i) β) := by
  rw [gibbsProb_linkEnergy]
  exact entropyW_siteProdWeight _
    (fun i => isProbWeight_gibbsProb (ε i) β)

/-- **Additivity, identical links** (proved, corollary): with every
link carrying the same energy, the total entropy is `n` times the
single-link Gibbs entropy. -/
theorem entropyW_gibbs_linkEnergy_identical {n : ℕ} (ε : Bool → ℝ)
    (β : ℝ) :
    entropyW (ModularVariance.gibbsProb (linkEnergy (fun _ : Fin n => ε)) β)
      = (n : ℝ) * entropyW (ModularVariance.gibbsProb ε β) := by
  calc entropyW (ModularVariance.gibbsProb (linkEnergy (fun _ : Fin n => ε)) β)
      = ∑ _i : Fin n, entropyW (ModularVariance.gibbsProb ε β) :=
        entropyW_gibbs_linkEnergy (fun _ : Fin n => ε) β
    _ = (n : ℝ) * entropyW (ModularVariance.gibbsProb ε β) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- **The dyadic count at uniformity** (proved by assembly): the
entropy of the uniform weight on the dyadic seat is `n * log 2`.
Assembly, stated as such: the constant weight is uniform, so census
`entropyW_eq_log_card_iff` (⇐) applies at `ι = (Fin n → Bool)`;
LG-1's `dyadic_card` and `Real.log_pow` finish. The counting is
Boltzmann's, the saturation is `FiniteEntropy`'s; this statement
contributes the seat and the name. -/
theorem entropyW_dyadic_uniform (n : ℕ) :
    entropyW (fun _ : Fin n → Bool => ((2 : ℝ) ^ n)⁻¹)
      = (n : ℝ) * Real.log 2 := by
  have hprob : IsProbWeight (fun _ : Fin n → Bool => ((2 : ℝ) ^ n)⁻¹) := by
    refine ⟨fun _ => by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, dyadic_card, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    exact mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))
  have hunif : ∀ c : Fin n → Bool,
      ((2 : ℝ) ^ n)⁻¹ = 1 / (Fintype.card (Fin n → Bool) : ℝ) := by
    intro c
    rw [dyadic_card, Nat.cast_pow, Nat.cast_ofNat, one_div]
  rw [(entropyW_eq_log_card_iff hprob).mpr hunif, dyadic_card,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- **The dyadic Gibbs state at `β = 0` is uniform, and its entropy
is the count** (proved): at `β = 0` every Boltzmann factor is `1`,
the partition sum is the configuration count `2 ^ n`, so the Gibbs
state of any sum-over-links energy is the uniform weight on the
dyadic seat — and the previous statement closes it. The dyadic
count at uniformity, stated about the Gibbs state itself. -/
theorem entropyW_gibbs_linkEnergy_zero {n : ℕ} (ε : Fin n → Bool → ℝ) :
    entropyW (ModularVariance.gibbsProb (linkEnergy ε) 0)
      = (n : ℝ) * Real.log 2 := by
  have hunif : ModularVariance.gibbsProb (linkEnergy ε) 0
      = fun _ : Fin n → Bool => ((2 : ℝ) ^ n)⁻¹ := by
    funext c
    unfold ModularVariance.gibbsProb ModularVariance.partSum
    simp only [zero_mul, neg_zero, Real.exp_zero, Finset.sum_const,
      Finset.card_univ, dyadic_card, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat, mul_one, one_div]
  rw [hunif, entropyW_dyadic_uniform]

/-- **The Landauer-shaped identity, named as shape only**
(K-LG-LANDAUER): at uniformity, `k` times the entropy of an
`n`-digit dyadic string is `k * n * log 2` — one binary digit
carries `k * log 2`. A counting identity at uniformity whose shape
is Landauer's: nothing here erases anything, couples to a bath, or
prices a process, and Landauer's principle is not claimed. -/
theorem planck_dyadic_uniform (n : ℕ) (k : ℝ) :
    k * entropyW (fun _ : Fin n → Bool => ((2 : ℝ) ^ n)⁻¹)
      = k * (n : ℝ) * Real.log 2 := by
  rw [entropyW_dyadic_uniform]
  ring

end ThetLogos
