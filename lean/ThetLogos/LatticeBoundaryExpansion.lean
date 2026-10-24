import ThetLogos.LatticeBoundaryOp
import ThetLogos.LatticeGramSeries

/-!
# ThetLogos.LatticeBoundaryExpansion — dynamic-boundary
charter, brick DB2: expansion stability, REDUCED FORM ONLY

The dynamic-boundary scoping charter
(`whitepaper/dynamic-boundary-scoping-2026-10-24.md`, §2.2)
asked the one finite statement in the generative direction
of Jeff's fragment that is honestly statable: insert a layer
pair, `N → N + 2`, and ask whether the boundary the
expansion creates is the same boundary. The charter scoped
DB2 in **reduced form**, two levels:

- **(b0) the β = 0 control** (§2 and §3b of this module): the
  boundary weight at zero coupling is the trivial kernel at
  every size (DB1's `bdry_zero`), and the inserted layers
  carry product Haar, which marginalizes to product Haar —
  the boundary the expansion creates at zero coupling is
  the same trivial boundary operator, transported.
- **(bβ) general β: locality transport** (§§1, 3): the
  crossing action `S₀` sees only its own stratum — it is a
  function of the configuration's seam-neighbourhood links
  alone (§1) — and under the layer-pair insertion its
  summands over the *transported* stratum are identical to
  the old seam factor's summands, so the transported part
  of the new seam factor *is* the old seam factor (§3).

**What the reduced form does NOT contain, stated on the
face (charter kill K-DB2(a), fired on the total-identity
reading):** the unrestricted identity `S₀^{N+2}(insert U) =
S₀^N(U)` is **false in this corpus**, and §3 proves the
exact decomposition instead: the inserted configuration's
crossing action is the old crossing action plus
`β` times an exhibited **extra-stratum sum** — the seam
plaquettes over the enlarged spatial torus at the seam
times. The corpus's size parameter is isotropic (one `N`
for all four directions), so growing `N` grows the seam's
spatial extent along with its time extent; there is no
time-only growth type in the corpus for the charter's
setup to land on. The differing factor is therefore new
*seam*, not inserted bulk: §3 also proves that **no
plaquette based at an inserted time lies in the crossing
stratum at all** (inserted-time plaquettes are in the
positive/negative classes — they contribute their own
half-action factors), and that `S₀` is invariant under
arbitrary changes at the inserted times. Locality — the
content (bβ) was scoped to express — holds; the kill's
stated trigger (an inserted-layer plaquette inside
`wilsonActionZero`, breaking locality) is refuted by
proof, and the kill fires only on the naive total
identity, with its differing factor exhibited in §3 at
machine-checked rank.

**Charter fence (kill K-DB2(c)), on the face:** no
statement in this module iterates the insertion, and
nothing here is a statement about a limit, an attractor,
or convergence of any kind. The attractor / repeated-
expansion reading was killed at scoping (charter §2.2,
§4: FRONTIER) and is not revived here, in any wording.
**Charter fence (kill K-DB1(c), persisting):** no
positivity assertion about `Bdry` — in particular no
positive-definiteness — appears anywhere in this module.

NO CLAIM. Parts of the official Clay Yang–Mills statement
closed by this module: 0. Stage 1b-B label unchanged
(positivity T1 for U(1) at all `β ≥ 0`; general `(G, ρ)`
OPEN).

- Status: brick DB2 — built 2026-10-24 under the
  dynamic-boundary charter; parent-verified 2026-10-24
  (targeted build exit 0, strict recount, axiom check);
  verdict PARTIAL (K-DB2(a) fired on the total-identity
  reading only). Dossier:
  `whitepaper/dynamic-boundary-db2-partial-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Locality

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. Locality: the crossing action sees only its
own stratum

`S₀` is a sum of plaquette densities over the crossing
stratum (landed classification `isZeroPlaq_iff`: temporal
plaquettes based at times `N/2 − 1` and `N − 1`). A
plaquette is a product of four links, and the four links
of a crossing plaquette have base times in
`{N/2 − 1, N/2, N − 1, 0}` — the two seam base times, the
successor of the lower seam time, and the wrap-around
successor of the upper one. Hence `S₀` — and with it the
boundary weight — is a function of the configuration's
values on those links alone: the seam factor does not see
the bulk. -/

/-- Two configurations agreeing on the seam-neighbourhood
links (base times `N/2 − 1`, `N/2`, `N − 1`, `0`) have the
same plaquette at every crossing plaquette. -/
theorem plaquette_congr_seam {U U' : Config (Fin 4 → ZMod N) G}
    (hN : Even N)
    (h : ∀ ℓ : Link (Fin 4 → ZMod N),
      (ℓ.1 0).val = N / 2 - 1 ∨ (ℓ.1 0).val = N / 2
        ∨ (ℓ.1 0).val = N - 1 ∨ (ℓ.1 0).val = 0 → U ℓ = U' ℓ)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hpI : p ∈ plaqIndex)
    (hp0 : IsZeroPlaq p) :
    plaquette (torusShift N) U p.1 p.2.1 p.2.2
      = plaquette (torusShift N) U' p.1 p.2.1 p.2.2 := by
  obtain ⟨hμ, ht⟩ := (isZeroPlaq_iff hN p hpI).mp hp0
  -- The four links of the plaquette, and their base times.
  have hν : p.2.2 ≠ 0 := by
    have hlt : p.2.1 < p.2.2 := mem_plaqIndex hpI
    rw [hμ] at hlt
    exact ne_of_gt hlt
  have htime : ∀ y : Fin 4 → ZMod N,
      (y = p.1 ∨ y = torusShift N p.2.1 p.1
        ∨ y = torusShift N p.2.2 p.1) →
      ((y 0).val = N / 2 - 1 ∨ (y 0).val = N / 2
        ∨ (y 0).val = N - 1 ∨ (y 0).val = 0) := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · rcases ht with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
    · -- the `μ = p.2.1 = 0` shift: base time increases by one
      have h0 : (torusShift N p.2.1 p.1) 0 = p.1 0 + 1 := by
        rw [torusShift_apply_coord, hμ, Pi.single_eq_same, add_comm]
      rw [h0, ZMod.val_add]
      have h1val : (1 : ZMod N).val = 1 % N := by
        conv_lhs => rw [← Nat.cast_one]
        exact ZMod.val_natCast N 1
      rw [h1val]
      obtain ⟨r, hr⟩ := hN
      have hr1 : 1 ≤ r := by
        by_contra hc
        have hr0 : r = 0 := by omega
        exact (NeZero.ne N) (by omega)
      have hN2 : N / 2 = r := by rw [hr]; omega
      have hmod1 : 1 % N = 1 := Nat.mod_eq_of_lt (by rw [hr]; omega)
      rw [hmod1]
      rcases ht with h1 | h1
      · rw [h1, hN2]
        have e1 : (r - 1) + 1 = r := by omega
        rw [e1, Nat.mod_eq_of_lt (by rw [hr]; omega : r < N)]
        exact Or.inr (Or.inl rfl)
      · rw [h1]
        have e1 : (N - 1) + 1 = N := by
          have hN1 : 1 ≤ N := Nat.pos_of_ne_zero (NeZero.ne N)
          omega
        rw [e1, Nat.mod_self]
        exact Or.inr (Or.inr (Or.inr rfl))
    · -- the `ν = p.2.2 ≠ 0` shift: base time unchanged
      rw [torusShift_apply_zero_of_ne hν]
      rcases ht with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h1))
  have e1 : U (p.1, p.2.1) = U' (p.1, p.2.1) :=
    h (p.1, p.2.1) (htime p.1 (Or.inl rfl))
  have e2 : U (torusShift N p.2.1 p.1, p.2.2)
      = U' (torusShift N p.2.1 p.1, p.2.2) :=
    h (torusShift N p.2.1 p.1, p.2.2)
      (htime (torusShift N p.2.1 p.1) (Or.inr (Or.inl rfl)))
  have e3 : U (torusShift N p.2.2 p.1, p.2.1)
      = U' (torusShift N p.2.2 p.1, p.2.1) :=
    h (torusShift N p.2.2 p.1, p.2.1)
      (htime (torusShift N p.2.2 p.1) (Or.inr (Or.inr rfl)))
  have e4 : U (p.1, p.2.2) = U' (p.1, p.2.2) :=
    h (p.1, p.2.2) (htime p.1 (Or.inl rfl))
  unfold plaquette
  rw [e1, e2, e3, e4]

/-- **Locality of the crossing action.** `S₀` depends on
the configuration only through its seam-neighbourhood
links: configurations agreeing there have the same
crossing action, at every real `β`, general `(G, ρ)`,
even `N`. This is the engine of DB2: whatever happens in
the bulk — in particular, whatever layers an expansion
inserts away from the seam — the seam factor does not see
it. -/
theorem wilsonActionZero_congr_seam {U U' : Config (Fin 4 → ZMod N) G}
    (hN : Even N)
    (h : ∀ ℓ : Link (Fin 4 → ZMod N),
      (ℓ.1 0).val = N / 2 - 1 ∨ (ℓ.1 0).val = N / 2
        ∨ (ℓ.1 0).val = N - 1 ∨ (ℓ.1 0).val = 0 → U ℓ = U' ℓ)
    (β : ℝ) :
    wilsonActionZero ρ β U = wilsonActionZero ρ β U' := by
  unfold wilsonActionZero
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpI : p ∈ plaqIndex := (Finset.mem_filter.mp hp).1
  have hp0 : IsZeroPlaq p := (Finset.mem_filter.mp hp).2
  have hplaq := plaquette_congr_seam hN h p hpI hp0
  unfold plaquetteDensity
  rw [hplaq]

/-- **Locality of the boundary weight.** The boundary
operator reads the unsplit configuration only through its
seam-neighbourhood links: split configurations whose
unsplit readings agree there have the same boundary
weight, at every real `β`. -/
theorem bdry_congr_seam
    {p p' : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)}
    (hN : Even N)
    (h : ∀ ℓ : Link (Fin 4 → ZMod N),
      (ℓ.1 0).val = N / 2 - 1 ∨ (ℓ.1 0).val = N / 2
        ∨ (ℓ.1 0).val = N - 1 ∨ (ℓ.1 0).val = 0 →
      ((splitEquiv (halfLinks (N := N))).symm p) ℓ
        = ((splitEquiv (halfLinks (N := N))).symm p') ℓ)
    (β : ℝ) :
    Bdry ρ β p = Bdry ρ β p' := by
  apply Subtype.ext
  show (Bdry ρ β p : ℝ) = (Bdry ρ β p' : ℝ)
  rw [bdry_apply, bdry_apply, wilsonActionZero_congr_seam ρ hN h β]

end Locality

section Control

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §2. The β = 0 control (charter (b0))

At zero coupling the boundary weight is the constant `1`
at every size (DB1's `bdry_zero`), so it is invariant
under Haar marginalization over either half: integrating
a constant against a probability measure returns the
constant. The measure-level statement — the inserted
layers carry product Haar, which marginalizes to product
Haar — is §3's `configMeasure_map_insLink`, proved with
Q1's rectangle machinery once the insertion's link
transport is on the table. -/

/-- **(b0), marginal form.** Haar-integrating the β = 0
boundary weight over the negative half returns the
weight: at zero coupling the boundary the expansion
creates is the same trivial boundary, and marginalizing
the inserted Haar layers changes nothing. -/
theorem bdry_zero_marginal (y : ↥(halfLinks (N := N)) → G) :
    ∫ u, (Bdry ρ 0 (y, u) : ℝ)
        ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG) = 1 := by
  have hval : ∀ u : ↥(negLinks (N := N)) → G,
      (Bdry ρ 0 (y, u) : ℝ) = 1 := by
    intro u
    rw [show Bdry ρ 0 (y, u) = 1 from bdry_zero ρ (y, u)]
    exact NNReal.coe_one
  rw [integral_congr_ae (ae_of_all _ fun u => hval u)]
  simp

end Control

section Transport

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-! ## §3. The insertion N → N + 2: transport data

Old size `N = r + r` (`r ≥ 2`), new size `N + 2`. The
insertion adds two consecutive time layers in the
interior of each closed half, away from the seam: on
representatives, time `0` stays, times `1..r` shift by
`1`, times `≥ r + 1` shift by `2`, so the two inserted
new times are `1` and `r + 2`. The old seam times land on
the new seam times (`r − 1 ↦ r = (N+2)/2 − 1`,
`r + r − 1 ↦ 2r + 1 = (N+2) − 1`) and the old reflection
axis `r` lands on the new axis `r + 1`. The fold reverses
the insertion on its image. (Sizes and `r` are explicit
arguments throughout this section: the corpus's size
parameter is isotropic, and the transport arithmetic is
stated with nothing left implicit.) -/

/-- The time shift of the insertion, on representatives. -/
def insShift (N r : ℕ) (a : ZMod N) : ℕ :=
  if a.val = 0 then 0 else if a.val ≤ r then 1 else 2

/-- The inserted time of an old time. -/
def insTime (N r : ℕ) (a : ZMod N) : ZMod (N + 2) :=
  ((a.val + insShift N r a : ℕ) : ZMod (N + 2))

/-- The fold shift: inverse of `insShift` on its image. -/
def foldShift (N r : ℕ) (b : ZMod (N + 2)) : ℕ :=
  if b.val = 0 then 0 else if b.val ≤ r + 1 then 1 else 2

/-- The folded time of a new time. -/
def foldTime (N r : ℕ) (b : ZMod (N + 2)) : ZMod N :=
  ((b.val - foldShift N r b : ℕ) : ZMod N)

/-- Value-preserving lift of a spatial coordinate. -/
def liftCoord (N : ℕ) (a : ZMod N) : ZMod (N + 2) := (a.val : ZMod (N + 2))

/-- Value fold of a spatial coordinate. -/
def foldCoord (N : ℕ) (b : ZMod (N + 2)) : ZMod N := (b.val : ZMod N)

/-- The inserted site: transport the time coordinate,
lift the spatial ones by value. -/
def insSite (N r : ℕ) (x : Fin 4 → ZMod N) : Fin 4 → ZMod (N + 2) :=
  fun i => if i = 0 then insTime N r (x 0) else liftCoord N (x i)

/-- The folded site: fold the time coordinate, fold the
spatial ones by value. -/
def foldSite (N r : ℕ) (y : Fin 4 → ZMod (N + 2)) : Fin 4 → ZMod N :=
  fun i => if i = 0 then foldTime N r (y 0) else foldCoord N (y i)

/-- The inserted plaquette index. -/
def insPlaq (N r : ℕ) (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    (Fin 4 → ZMod (N + 2)) × Fin 4 × Fin 4 :=
  (insSite N r p.1, p.2.1, p.2.2)

/-- The inserted configuration: the old configuration
read through the fold. What the seam factor sees of it is
computed in §3b: on the transported seam stratum the
fold is the exact inverse of the insertion. -/
def insConfig (N r : ℕ) (U : Config (Fin 4 → ZMod N) G) :
    Config (Fin 4 → ZMod (N + 2)) G :=
  fun ℓ' => U (foldSite N r ℓ'.1, ℓ'.2)

/-- The new size is even. -/
theorem even_succ_two (N r : ℕ) (hrN : N = r + r) : Even (N + 2) :=
  ⟨r + 1, by omega⟩

/-- `1` has representative `1` at the new size. -/
theorem val_one_two (N : ℕ) : (1 : ZMod (N + 2)).val = 1 := by
  conv_lhs => rw [← Nat.cast_one]
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

/-- The shift of the zero time is zero. -/
theorem insShift_zero (N r : ℕ) {a : ZMod N} (h : a.val = 0) :
    insShift N r a = 0 := by
  unfold insShift
  rw [if_pos h]

/-- The shift of a positive time up to `r` is one. -/
theorem insShift_of_pos_le (N r : ℕ) {a : ZMod N} (h0 : a.val ≠ 0)
    (h1 : a.val ≤ r) : insShift N r a = 1 := by
  unfold insShift
  rw [if_neg h0, if_pos h1]

/-- The shift of a time past `r` is two. -/
theorem insShift_of_gt (N r : ℕ) {a : ZMod N} (h0 : a.val ≠ 0)
    (h1 : r < a.val) : insShift N r a = 2 := by
  unfold insShift
  rw [if_neg h0, if_neg (not_le.mpr h1)]

/-- The fold shift of the zero time is zero. -/
theorem foldShift_zero (N r : ℕ) {b : ZMod (N + 2)} (h : b.val = 0) :
    foldShift N r b = 0 := by
  unfold foldShift
  rw [if_pos h]

/-- The fold shift of a positive time up to `r + 1` is
one. -/
theorem foldShift_of_pos_le (N r : ℕ) {b : ZMod (N + 2)}
    (h0 : b.val ≠ 0) (h1 : b.val ≤ r + 1) : foldShift N r b = 1 := by
  unfold foldShift
  rw [if_neg h0, if_pos h1]

/-- The fold shift of a time past `r + 1` is two. -/
theorem foldShift_of_gt (N r : ℕ) {b : ZMod (N + 2)} (h0 : b.val ≠ 0)
    (h1 : r + 1 < b.val) : foldShift N r b = 2 := by
  unfold foldShift
  rw [if_neg h0, if_neg (not_le.mpr h1)]

/-- The representative of an inserted time: no wraparound
occurs, since inserted values stay below `N + 2`. -/
theorem insTime_val (N r : ℕ) (hrN : N = r + r) [NeZero N] (a : ZMod N) :
    (insTime N r a).val = a.val + insShift N r a := by
  unfold insTime
  rw [ZMod.val_natCast]
  have ha : a.val < N := ZMod.val_lt a
  refine Nat.mod_eq_of_lt ?_
  by_cases h0 : a.val = 0
  · rw [insShift_zero N r h0]; omega
  · by_cases h1 : a.val ≤ r
    · rw [insShift_of_pos_le N r h0 h1]; omega
    · rw [insShift_of_gt N r h0 (not_le.mp h1)]; omega

/-- The fold shift of an inserted time is the insertion
shift. -/
theorem foldShift_insTime (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (a : ZMod N) :
    foldShift N r (insTime N r a) = insShift N r a := by
  by_cases h0 : a.val = 0
  · have hv : (insTime N r a).val = 0 := by
      rw [insTime_val N r hrN, insShift_zero N r h0, h0]
    rw [foldShift_zero N r hv, insShift_zero N r h0]
  · by_cases h1 : a.val ≤ r
    · have hv : (insTime N r a).val = a.val + 1 := by
        rw [insTime_val N r hrN, insShift_of_pos_le N r h0 h1]
      rw [foldShift_of_pos_le N r (b := insTime N r a) (by rw [hv]; omega)
        (by rw [hv]; omega), insShift_of_pos_le N r h0 h1]
    · have hgt : r < a.val := not_le.mp h1
      have hv : (insTime N r a).val = a.val + 2 := by
        rw [insTime_val N r hrN, insShift_of_gt N r h0 hgt]
      rw [foldShift_of_gt N r (b := insTime N r a) (by rw [hv]; omega)
        (by rw [hv]; omega), insShift_of_gt N r h0 hgt]

/-- The fold inverts the insertion on times. -/
theorem foldTime_insTime (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (a : ZMod N) :
    foldTime N r (insTime N r a) = a := by
  have key : foldTime N r (insTime N r a)
      = (((insTime N r a).val - foldShift N r (insTime N r a) : ℕ) :
          ZMod N) := rfl
  rw [key, insTime_val N r hrN, foldShift_insTime N r hrN hr2,
    Nat.add_sub_cancel]
  exact ZMod.natCast_zmod_val a

/-- The representative of a lifted coordinate is the
original representative. -/
theorem liftCoord_val (N : ℕ) [NeZero N] (a : ZMod N) :
    (liftCoord N a).val = a.val := by
  unfold liftCoord
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by have := ZMod.val_lt a; omega)

/-- The fold inverts the lift on spatial coordinates. -/
theorem foldCoord_liftCoord (N : ℕ) [NeZero N] (a : ZMod N) :
    foldCoord N (liftCoord N a) = a := by
  show ((liftCoord N a).val : ZMod N) = a
  rw [liftCoord_val]
  exact ZMod.natCast_zmod_val a

/-- The fold of `1 +` a lifted coordinate is `1 +` the
original — the spatial shift commutes with the fold. -/
theorem foldCoord_one_add_lift (N : ℕ) [NeZero N] (a : ZMod N) :
    foldCoord N (1 + liftCoord N a) = 1 + a := by
  have hv : (1 + liftCoord N a).val = 1 + a.val := by
    rw [ZMod.val_add, liftCoord_val, val_one_two]
    exact Nat.mod_eq_of_lt (by have := ZMod.val_lt a; omega)
  show ((1 + liftCoord N a).val : ZMod N) = 1 + a
  rw [hv, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]

/-- The time coordinate of an inserted site. -/
theorem insSite_zero (N r : ℕ) (x : Fin 4 → ZMod N) :
    insSite N r x 0 = insTime N r (x 0) := if_pos rfl

/-- The spatial coordinates of an inserted site. -/
theorem insSite_of_ne (N r : ℕ) (x : Fin 4 → ZMod N) {i : Fin 4}
    (hi : i ≠ 0) : insSite N r x i = liftCoord N (x i) := if_neg hi

/-- The time coordinate of a folded site. -/
theorem foldSite_zero (N r : ℕ) (y : Fin 4 → ZMod (N + 2)) :
    foldSite N r y 0 = foldTime N r (y 0) := if_pos rfl

/-- The spatial coordinates of a folded site. -/
theorem foldSite_of_ne (N r : ℕ) (y : Fin 4 → ZMod (N + 2)) {i : Fin 4}
    (hi : i ≠ 0) : foldSite N r y i = foldCoord N (y i) := if_neg hi

/-- The fold inverts the insertion on sites. -/
theorem foldSite_insSite (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (x : Fin 4 → ZMod N) :
    foldSite N r (insSite N r x) = x := by
  funext i
  by_cases hi : i = 0
  · rw [hi, foldSite_zero, insSite_zero, foldTime_insTime N r hrN hr2]
  · rw [foldSite_of_ne _ _ _ hi, insSite_of_ne _ _ _ hi, foldCoord_liftCoord]

/-- Site insertion is injective: the transport loses no
site. -/
theorem insSite_injective (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] :
    Function.Injective (insSite N r) :=
  Function.LeftInverse.injective (foldSite_insSite N r hrN hr2)

/-- Plaquette-index insertion is injective. -/
theorem insPlaq_injective (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] :
    Function.Injective (insPlaq N r) := by
  intro p q hpq
  have h1 : insSite N r p.1 = insSite N r q.1 := congrArg Prod.fst hpq
  have h2 : p.2.1 = q.2.1 := congrArg (fun z => z.2.1) hpq
  have h3 : p.2.2 = q.2.2 := congrArg (fun z => z.2.2) hpq
  exact Prod.ext (insSite_injective N r hrN hr2 h1) (Prod.ext h2 h3)

/-- **Successor transport at the seam.** For an old time
at a seam base (`N/2 − 1` or `N − 1`), the fold of the
inserted successor time is the old successor time: the
time direction's step across the seam commutes with the
insertion. This is the arithmetic heart of the locality
transport. -/
theorem foldTime_add_one_seam (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (a : ZMod N)
    (ha : a.val = r - 1 ∨ a.val = r + r - 1) :
    foldTime N r (insTime N r a + 1) = a + 1 := by
  have cast_add_one : a + 1 = ((a.val + 1 : ℕ) : ZMod N) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← Nat.cast_one]
    rw [← Nat.cast_add]
  rw [cast_add_one]
  have key : foldTime N r (insTime N r a + 1)
      = (((insTime N r a + 1).val - foldShift N r (insTime N r a + 1) :
          ℕ) : ZMod N) := rfl
  rw [key]
  rcases ha with ha | ha
  · have hs : insShift N r a = 1 :=
      insShift_of_pos_le N r (by omega) (by omega)
    have hv : (insTime N r a).val = r := by
      rw [insTime_val N r hrN, hs]; omega
    have hv1 : (insTime N r a + 1).val = r + 1 := by
      rw [ZMod.val_add, hv, val_one_two]
      exact Nat.mod_eq_of_lt (by omega)
    have hf : foldShift N r (insTime N r a + 1) = 1 :=
      foldShift_of_pos_le N r (by omega) (by omega)
    rw [hv1, hf]
    have e2 : r + 1 - 1 = a.val + 1 := by omega
    rw [e2]
  · have hs : insShift N r a = 2 :=
      insShift_of_gt N r (by omega) (by omega)
    have hv : (insTime N r a).val = r + r + 1 := by
      rw [insTime_val N r hrN, hs]; omega
    have hv1 : (insTime N r a + 1).val = 0 := by
      rw [ZMod.val_add, hv, val_one_two]
      have e : r + r + 1 + 1 = N + 2 := by omega
      rw [e]
      exact Nat.mod_self _
    have hf : foldShift N r (insTime N r a + 1) = 0 :=
      foldShift_zero N r hv1
    rw [hv1, hf]
    have e : a.val + 1 = N := by omega
    show ((0 : ℕ) : ZMod N) = ((a.val + 1 : ℕ) : ZMod N)
    rw [e, ZMod.natCast_self, Nat.cast_zero]

/-- The fold of a time-shifted inserted seam site is the
old time-shifted site. -/
theorem foldSite_shift_zero_seam (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (x : Fin 4 → ZMod N)
    (hx : (x 0).val = r - 1 ∨ (x 0).val = r + r - 1) :
    foldSite N r (torusShift (N + 2) 0 (insSite N r x))
      = torusShift N 0 x := by
  have hstep : foldTime N r (insTime N r (x 0) + 1) = x 0 + 1 :=
    foldTime_add_one_seam N r hrN hr2 _ hx
  funext i
  by_cases hi : i = 0
  · rw [hi, foldSite_zero, torusShift_apply_coord, Pi.single_eq_same,
      add_comm, insSite_zero, hstep,
      torusShift_apply_coord, Pi.single_eq_same, add_comm]
  · rw [foldSite_of_ne _ _ _ hi, torusShift_apply_coord,
      Pi.single_eq_of_ne hi, zero_add, insSite_of_ne _ _ _ hi,
      foldCoord_liftCoord, torusShift_apply_coord,
      Pi.single_eq_of_ne hi, zero_add]

/-- The fold of a spatially-shifted inserted site is the
old spatially-shifted site — at every base time, since a
spatial step never touches the time coordinate. -/
theorem foldSite_shift_of_ne (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (x : Fin 4 → ZMod N) {ν : Fin 4} (hν : ν ≠ 0) :
    foldSite N r (torusShift (N + 2) ν (insSite N r x))
      = torusShift N ν x := by
  funext i
  by_cases hi0 : i = 0
  · rw [hi0, foldSite_zero, torusShift_apply_zero_of_ne hν, insSite_zero,
      foldTime_insTime N r hrN hr2, torusShift_apply_zero_of_ne hν]
  · by_cases hiν : i = ν
    · have hi0' : ν ≠ 0 := hiν ▸ hi0
      rw [foldSite_of_ne _ _ _ hi0, torusShift_apply_coord, hiν,
        Pi.single_eq_same, insSite_of_ne _ _ _ hi0', foldCoord_one_add_lift,
        torusShift_apply_coord, Pi.single_eq_same]
    · rw [foldSite_of_ne _ _ _ hi0, torusShift_apply_coord,
        Pi.single_eq_of_ne hiν, zero_add, insSite_of_ne _ _ _ hi0,
        foldCoord_liftCoord, torusShift_apply_coord,
        Pi.single_eq_of_ne hiν, zero_add]

/-- **The summand identity.** A seam plaquette of the old
torus, inserted, has the same group element in the
inserted configuration as in the old one: all four of its
links fold back to the old links. -/
theorem plaquette_insConfig (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) {ν : Fin 4} (hν : ν ≠ 0)
    (hx : (x 0).val = r - 1 ∨ (x 0).val = r + r - 1) :
    plaquette (torusShift (N + 2)) (insConfig N r U) (insSite N r x) 0 ν
      = plaquette (torusShift N) U x 0 ν := by
  show (insConfig N r U) (insSite N r x, 0)
      * (insConfig N r U) (torusShift (N + 2) 0 (insSite N r x), ν)
      * ((insConfig N r U) (torusShift (N + 2) ν (insSite N r x), 0))⁻¹
      * ((insConfig N r U) (insSite N r x, ν))⁻¹
    = U (x, 0) * U (torusShift N 0 x, ν)
      * (U (torusShift N ν x, 0))⁻¹ * (U (x, ν))⁻¹
  show U (foldSite N r (insSite N r x), 0)
      * U (foldSite N r (torusShift (N + 2) 0 (insSite N r x)), ν)
      * (U (foldSite N r (torusShift (N + 2) ν (insSite N r x)), 0))⁻¹
      * (U (foldSite N r (insSite N r x), ν))⁻¹
    = _
  have e1 : foldSite N r (insSite N r x) = x :=
    foldSite_insSite N r hrN hr2 x
  have e2 : foldSite N r (torusShift (N + 2) 0 (insSite N r x))
      = torusShift N 0 x := foldSite_shift_zero_seam N r hrN hr2 x hx
  have e3 : foldSite N r (torusShift (N + 2) ν (insSite N r x))
      = torusShift N ν x := foldSite_shift_of_ne N r hrN hr2 x hν
  rw [e1, e2, e3]

/-- The summand identity at the level of plaquette
densities — what the crossing action sums. -/
theorem plaquetteDensity_insConfig (N r : ℕ) (hrN : N = r + r)
    (hr2 : 2 ≤ r) [NeZero N] (U : Config (Fin 4 → ZMod N) G)
    (x : Fin 4 → ZMod N) {ν : Fin 4} (hν : ν ≠ 0)
    (hx : (x 0).val = r - 1 ∨ (x 0).val = r + r - 1) :
    plaquetteDensity (torusShift (N + 2)) ρ (insConfig N r U)
        (insSite N r x) 0 ν
      = plaquetteDensity (torusShift N) ρ U x 0 ν := by
  unfold plaquetteDensity
  rw [plaquette_insConfig N r hrN hr2 U x hν hx]

end Transport

section TransportB

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-! ## §3b. Stratum transport, the decomposition, and the
Haar marginal

The crossing action at the new size splits over the
transported old seam stratum — where the summand
identity of §3a identifies it with the old crossing
action term by term — plus an extra stratum of seam
plaquettes based at the same seam times but at spatial
positions the old torus does not have. The extra stratum
is nonempty: the differing factor is exhibited, not
hidden. Inserted-time plaquettes, by contrast, are
classified into the two half actions and never enter the
crossing action. -/

/-- The inserted link. -/
def insLink (N r : ℕ) (ℓ : Link (Fin 4 → ZMod N)) :
    Link (Fin 4 → ZMod (N + 2)) :=
  (insSite N r ℓ.1, ℓ.2)

/-- Link insertion is injective. -/
theorem insLink_injective (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] : Function.Injective (insLink N r) := by
  intro ℓ ℓ' h
  have h1 : (insLink N r ℓ).1 = (insLink N r ℓ').1 := congrArg Prod.fst h
  have h2 : (insLink N r ℓ).2 = (insLink N r ℓ').2 := congrArg Prod.snd h
  exact Prod.ext (insSite_injective N r hrN hr2 h1) h2

open Classical in
/-- The fiber sets of the restriction map: over the image
of the insertion, the old fiber set; elsewhere, the whole
space, so the marginal contributes a factor of `1`. -/
def restrSet (N r : ℕ) (s : Link (Fin 4 → ZMod N) → Set G)
    (ℓ' : Link (Fin 4 → ZMod (N + 2))) : Set G :=
  if h : ∃ ℓ, insLink N r ℓ = ℓ' then s (Classical.choose h) else Set.univ

/-- On the image of the insertion, the fiber set is the
old fiber set — the choice is forced by injectivity. -/
theorem restrSet_image (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] (s : Link (Fin 4 → ZMod N) → Set G) (ℓ : Link (Fin 4 → ZMod N)) :
    restrSet N r s (insLink N r ℓ) = s ℓ := by
  have hex : ∃ ℓ₀, insLink N r ℓ₀ = insLink N r ℓ := ⟨ℓ, rfl⟩
  unfold restrSet
  rw [dif_pos hex]
  congr 1
  exact insLink_injective N r hrN hr2 (Classical.choose_spec hex)

/-- Off the image of the insertion, the fiber set is the
whole space. -/
theorem restrSet_notMem (N r : ℕ) (s : Link (Fin 4 → ZMod N) → Set G)
    {ℓ' : Link (Fin 4 → ZMod (N + 2))}
    (h : ¬∃ ℓ, insLink N r ℓ = ℓ') :
    restrSet N r s ℓ' = Set.univ := by
  unfold restrSet
  rw [dif_neg h]

set_option maxHeartbeats 1600000 in
/-- The crossing action is the sum over the crossing
stratum — a restatement that names the stratum. -/
theorem wilsonActionZero_eq_sum (K : ℕ) [NeZero K] (β : ℝ)
    (U : Config (Fin 4 → ZMod K) G) :
    wilsonActionZero ρ β U
      = β * ∑ p ∈ zeroFinset (N := K),
          plaquetteDensity (torusShift K) ρ U p.1 p.2.1 p.2.2 := by
  unfold wilsonActionZero
  rw [zeroFinset_eq]

set_option maxHeartbeats 1600000 in
/-- **Stratum transport.** The insertion carries the old
crossing stratum into the new crossing stratum: an old
seam plaquette (temporal direction, base time `N/2 − 1`
or `N − 1`) inserts to a new seam plaquette (base time
`(N+2)/2 − 1` or `(N+2) − 1`). -/
theorem insPlaq_mem_zeroFinset (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] [NeZero (N + 2)] {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}
    (hp : p ∈ zeroFinset (N := N)) :
    insPlaq N r p ∈ zeroFinset (N := N + 2) := by
  rw [zeroFinset_eq] at hp ⊢
  obtain ⟨hpI, hp0⟩ := Finset.mem_filter.mp hp
  obtain ⟨hμ, ht⟩ := (isZeroPlaq_iff ⟨r, hrN⟩ p hpI).mp hp0
  have hmem : insPlaq N r p ∈ plaqIndex (N := N + 2) := by
    simp only [plaqIndex, Finset.mem_filter, Finset.mem_univ, true_and]
    show p.2.1 < p.2.2
    exact mem_plaqIndex hpI
  refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
  apply (isZeroPlaq_iff (even_succ_two N r hrN) (insPlaq N r p) hmem).mpr
  refine ⟨hμ, ?_⟩
  have htv : ((insSite N r p.1) 0).val
      = (p.1 0).val + insShift N r (p.1 0) := by
    rw [insSite_zero, insTime_val N r hrN]
  show ((insPlaq N r p).1 0).val = (N + 2) / 2 - 1
    ∨ ((insPlaq N r p).1 0).val = (N + 2) - 1
  rw [show (insPlaq N r p).1 = insSite N r p.1 from rfl, htv]
  rcases ht with ht | ht
  · left
    have hs : insShift N r (p.1 0) = 1 :=
      insShift_of_pos_le N r (by omega) (by omega)
    rw [hs]; omega
  · right
    have hs : insShift N r (p.1 0) = 2 :=
      insShift_of_gt N r (by omega) (by omega)
    rw [hs]; omega

/-- **The transported-stratum sum identity.** Summed over
the transported stratum, the new crossing action's
density on the inserted configuration is the old crossing
action's sum: term-by-term equality by the summand
identity, reindexed by the injective insertion. -/
theorem sum_zeroFinset_insConfig (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] [NeZero (N + 2)] (β : ℝ) (U : Config (Fin 4 → ZMod N) G) :
    ∑ q ∈ (zeroFinset (N := N)).image (insPlaq N r),
        plaquetteDensity (torusShift (N + 2)) ρ (insConfig N r U)
          q.1 q.2.1 q.2.2
      = ∑ p ∈ zeroFinset (N := N),
          plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2 := by
  classical
  rw [Finset.sum_image (fun x _ y _ h => insPlaq_injective N r hrN hr2 h)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [zeroFinset_eq] at hp
  obtain ⟨hpI, hp0⟩ := Finset.mem_filter.mp hp
  obtain ⟨hμ, ht⟩ := (isZeroPlaq_iff ⟨r, hrN⟩ p hpI).mp hp0
  have hlt : p.2.1 < p.2.2 := mem_plaqIndex hpI
  have hν : p.2.2 ≠ 0 := by omega
  have htr : (p.1 0).val = r - 1 ∨ (p.1 0).val = r + r - 1 := by
    rcases ht with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  show plaquetteDensity (torusShift (N + 2)) ρ (insConfig N r U)
        (insSite N r p.1) p.2.1 p.2.2
      = plaquetteDensity (torusShift N) ρ U p.1 p.2.1 p.2.2
  rw [hμ]
  exact plaquetteDensity_insConfig ρ N r hrN hr2 U p.1 hν htr

/-- **The decomposition — the K-DB2(a) exhibit.** The new
crossing action on the inserted configuration is the old
crossing action plus `β` times an extra-stratum sum:
seam plaquettes at the new seam times over spatial
positions the old torus lacks, created because the
corpus's size parameter is isotropic. The total identity
`S₀^{N+2}(insert U) = S₀^N(U)` is therefore FALSE as an
unrestricted statement; the differing factor is this
term, exhibited at full rank. -/
theorem wilsonActionZero_insConfig_decomp (N r : ℕ) (hrN : N = r + r)
    (hr2 : 2 ≤ r) [NeZero N] [NeZero (N + 2)] (β : ℝ)
    (U : Config (Fin 4 → ZMod N) G) :
    wilsonActionZero ρ β (insConfig N r U)
      = wilsonActionZero ρ β U
        + β * ∑ q ∈ zeroFinset (N := N + 2)
              \ (zeroFinset (N := N)).image (insPlaq N r),
            plaquetteDensity (torusShift (N + 2)) ρ (insConfig N r U)
              q.1 q.2.1 q.2.2 := by
  have hsub : (zeroFinset (N := N)).image (insPlaq N r)
      ⊆ zeroFinset (N := N + 2) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact insPlaq_mem_zeroFinset N r hrN hr2 hp
  rw [wilsonActionZero_eq_sum, wilsonActionZero_eq_sum,
    ← Finset.sum_sdiff hsub, sum_zeroFinset_insConfig ρ N r hrN hr2 β U]
  ring

/-- The extra stratum is nonempty: the seam plaquette at
the new lower seam time over the spatial position `N`
(which the old torus, of spatial extent `N`, does not
contain) lies in the new crossing stratum but is not the
insertion of any old plaquette, whose spatial coordinates
all have representatives `< N`. -/
theorem insert_extra_nonempty (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] [NeZero (N + 2)] :
    (zeroFinset (N := N + 2)
      \ (zeroFinset (N := N)).image (insPlaq N r)).Nonempty := by
  classical
  refine ⟨⟨fun i => if i = 0 then ((r : ℕ) : ZMod (N + 2))
      else if i = 1 then ((N : ℕ) : ZMod (N + 2)) else 0, 0, 1⟩,
    Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
  · rw [zeroFinset_eq]
    have hmem : (⟨fun i => if i = 0 then ((r : ℕ) : ZMod (N + 2))
        else if i = 1 then ((N : ℕ) : ZMod (N + 2)) else 0, 0, 1⟩ :
          (Fin 4 → ZMod (N + 2)) × Fin 4 × Fin 4) ∈ plaqIndex := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (0 : Fin 4) < 1
      decide
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    apply (isZeroPlaq_iff (even_succ_two N r hrN) _ hmem).mpr
    refine ⟨rfl, Or.inl ?_⟩
    show ((r : ℕ) : ZMod (N + 2)).val = (N + 2) / 2 - 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : r < N + 2)]
    omega
  · intro himg
    rw [Finset.mem_image] at himg
    obtain ⟨p, -, hqp⟩ := himg
    have h1 : (insSite N r p.1) 1 = ((N : ℕ) : ZMod (N + 2)) :=
      congrArg (fun q : (Fin 4 → ZMod (N + 2)) × Fin 4 × Fin 4 => q.1 1) hqp
    have h2 : (insSite N r p.1) 1 = liftCoord N (p.1 1) :=
      insSite_of_ne N r _ (by decide)
    have h4 : (p.1 1).val = N := by
      rw [h2] at h1
      have hv := congrArg ZMod.val h1
      rw [liftCoord_val, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega : N < N + 2)] at hv
      exact hv
    have h5 : (p.1 1).val < N := ZMod.val_lt _
    omega

/-- **The boundary-weight factor form of the
decomposition**: at the level of `Bdry` itself, the new
boundary weight on an inserted configuration is the old
boundary weight times the exponential of the extra
factor. (Positivity of `Bdry` is neither asserted nor
used — K-DB1(c).) -/
theorem bdry_insConfig_factor (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] [NeZero (N + 2)] (β : ℝ)
    (p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G))
    (q : (↥(halfLinks (N := N + 2)) → G) × (↥(negLinks (N := N + 2)) → G))
    (U : Config (Fin 4 → ZMod N) G)
    (hp : (splitEquiv (halfLinks (N := N))).symm p = U)
    (hq : (splitEquiv (halfLinks (N := N + 2))).symm q = insConfig N r U) :
    (Bdry ρ β q : ℝ) = (Bdry ρ β p : ℝ)
      * Real.exp (-(β * ∑ q' ∈ zeroFinset (N := N + 2)
              \ (zeroFinset (N := N)).image (insPlaq N r),
            plaquetteDensity (torusShift (N + 2)) ρ (insConfig N r U)
              q'.1 q'.2.1 q'.2.2)) := by
  have e1 : (Bdry ρ β q : ℝ)
      = Real.exp (-(wilsonActionZero ρ β (insConfig N r U))) := by
    rw [bdry_apply, hq]
  have e2 : (Bdry ρ β p : ℝ)
      = Real.exp (-(wilsonActionZero ρ β U)) := by
    rw [bdry_apply, hp]
  rw [e1, wilsonActionZero_insConfig_decomp ρ N r hrN hr2 β U, e2,
    neg_add, Real.exp_add]

/-- **(b0), cross-size form.** At zero coupling the
boundary weight is the same trivial weight at the old and
the new size, for arbitrary configurations on both sides:
the expansion creates no boundary content at `β = 0`. -/
theorem bdry_zero_expansion (N : ℕ) [NeZero N] [NeZero (N + 2)]
    (p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G))
    (q : (↥(halfLinks (N := N + 2)) → G) × (↥(negLinks (N := N + 2)) → G)) :
    Bdry ρ 0 q = Bdry ρ 0 p := by
  rw [bdry_zero, bdry_zero]

/-- Plaquettes based at the first inserted time lie in
the positive (first-half) stratum at the new size: they
belong to a half action, never to the crossing action. -/
theorem isPosPlaq_inserted_one (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    (p : (Fin 4 → ZMod (N + 2)) × Fin 4 × Fin 4)
    (hμ : p.2.1 = 0) (ht : (p.1 0).val = 1) :
    IsPosPlaq p := by
  show plaqTimeHi p.1 p.2.1 < (N + 2) / 2
  rw [hμ, plaqTimeHi_zero, ht]
  omega

/-- Plaquettes based at the second inserted time lie in
the negative (second-half) stratum at the new size. -/
theorem isNegPlaq_inserted (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    (p : (Fin 4 → ZMod (N + 2)) × Fin 4 × Fin 4)
    (hμ : p.2.1 = 0) (ht : (p.1 0).val = r + 2) :
    IsNegPlaq p := by
  show (N + 2) / 2 ≤ (p.1 0).val ∧ plaqTimeHi p.1 p.2.1 < N + 2
  refine ⟨by omega, ?_⟩
  rw [hμ, plaqTimeHi_zero, ht]
  omega

/-- **Inserted times are invisible to the crossing
action**: two configurations at the new size that agree
off the inserted link times have the same crossing
action — §1's locality, transported. -/
theorem wilsonActionZero_inserted_times_invariant (N r : ℕ)
    (hrN : N = r + r) (hr2 : 2 ≤ r) [NeZero (N + 2)] (β : ℝ)
    {Ũ Ũ' : Config (Fin 4 → ZMod (N + 2)) G}
    (h : ∀ ℓ : Link (Fin 4 → ZMod (N + 2)),
      (ℓ.1 0).val ≠ 1 → (ℓ.1 0).val ≠ r + 2 → Ũ ℓ = Ũ' ℓ) :
    wilsonActionZero ρ β Ũ = wilsonActionZero ρ β Ũ' := by
  apply wilsonActionZero_congr_seam ρ (even_succ_two N r hrN)
  intro ℓ hℓ
  exact h ℓ (by omega) (by omega)

/-- **(b0), the Haar marginal.** Product Haar measure on
configurations pushes forward, under restriction along
the insertion, to product Haar measure at the old size:
the inserted layers carry product Haar and marginalize
to product Haar — the inserted layer pair contributes
only its Haar factor, which integrates to `1`. Proved by
Q1's rectangle machinery: the fiber sets are `restrSet`,
equal to the old fiber sets on the image of the insertion
and to the whole space off it. -/
theorem configMeasure_map_insLink (N r : ℕ) (hrN : N = r + r) (hr2 : 2 ≤ r)
    [NeZero N] [NeZero (N + 2)] :
    (configMeasure (Λ := Fin 4 → ZMod (N + 2)) μG).map
        (fun Ũ : Config (Fin 4 → ZMod (N + 2)) G => fun ℓ => Ũ (insLink N r ℓ))
      = configMeasure (Λ := Fin 4 → ZMod N) μG := by
  classical
  symm
  refine MeasureTheory.Measure.pi_eq ?_
  intro s hs
  have hmeas : Measurable
      (fun Ũ : Config (Fin 4 → ZMod (N + 2)) G => fun ℓ => Ũ (insLink N r ℓ)) := by
    fun_prop
  have hpre : (fun Ũ : Config (Fin 4 → ZMod (N + 2)) G =>
        fun ℓ => Ũ (insLink N r ℓ)) ⁻¹' (Set.pi Set.univ s)
      = Set.pi Set.univ (restrSet N r s) := by
    ext Ũ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h ℓ'
      by_cases hℓ' : ∃ ℓ, insLink N r ℓ = ℓ'
      · obtain ⟨ℓ, rfl⟩ := hℓ'
        rw [restrSet_image N r hrN hr2]
        exact h ℓ
      · rw [restrSet_notMem N r s hℓ']
        exact Set.mem_univ _
    · intro h ℓ
      have e := h (insLink N r ℓ)
      rw [restrSet_image N r hrN hr2] at e
      exact e
  rw [Measure.map_apply hmeas
    (MeasurableSet.pi (Set.countable_univ) (fun ℓ _ => hs ℓ)), hpre]
  have hcm : configMeasure (Λ := Fin 4 → ZMod (N + 2)) μG
      = Measure.pi (fun _ : Link (Fin 4 → ZMod (N + 2)) => μG) := rfl
  rw [hcm, MeasureTheory.Measure.pi_pi]
  show (∏ ℓ' : Link (Fin 4 → ZMod (N + 2)), μG (restrSet N r s ℓ'))
    = ∏ ℓ, μG (s ℓ)
  have hsplit : (∏ ℓ' : Link (Fin 4 → ZMod (N + 2)), μG (restrSet N r s ℓ'))
      = (∏ ℓ' ∈ (Finset.univ : Finset (Link (Fin 4 → ZMod (N + 2))))
            \ ((Finset.univ : Finset (Link (Fin 4 → ZMod N))).image (insLink N r)), μG (restrSet N r s ℓ'))
        * (∏ ℓ' ∈ (Finset.univ.image (insLink N r) : Finset (Link (Fin 4 → ZMod (N + 2)))), μG (restrSet N r s ℓ')) :=
    (Finset.prod_sdiff (Finset.subset_univ
      ((Finset.univ.image (insLink N r) : Finset (Link (Fin 4 → ZMod (N + 2))))))).symm
  rw [hsplit]
  have hoff : (∏ ℓ' ∈ (Finset.univ : Finset (Link (Fin 4 → ZMod (N + 2))))
        \ ((Finset.univ : Finset (Link (Fin 4 → ZMod N))).image (insLink N r)), μG (restrSet N r s ℓ')) = 1 := by
    refine Finset.prod_eq_one (fun ℓ' hℓ' => ?_)
    have hni : ℓ' ∉ (Finset.univ.image (insLink N r) : Finset (Link (Fin 4 → ZMod (N + 2)))) := (Finset.mem_sdiff.mp hℓ').2
    have hne : ¬∃ ℓ, insLink N r ℓ = ℓ' := by
      intro hcon
      obtain ⟨ℓ, hℓ⟩ := hcon
      exact hni (Finset.mem_image.mpr ⟨ℓ, Finset.mem_univ _, hℓ⟩)
    rw [restrSet_notMem N r s hne]
    exact measure_univ
  have hon : (∏ ℓ' ∈ (Finset.univ.image (insLink N r) : Finset (Link (Fin 4 → ZMod (N + 2)))), μG (restrSet N r s ℓ')) = ∏ ℓ, μG (s ℓ) := by
    rw [Finset.prod_image (fun x _ y _ h => insLink_injective N r hrN hr2 h)]
    refine Finset.prod_congr rfl (fun ℓ _ => ?_)
    rw [restrSet_image N r hrN hr2]
  rw [hoff, hon, one_mul]

end TransportB

end ThetLogos
