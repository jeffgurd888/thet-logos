/-
# WP2 character route, Module A, brick A4 — multi-factor
# site contraction

A **word** at one site is a finite product of tensor entries
at the same group element, over an arbitrary finite family
of slot families (conjugate factors included — the conjugate
of a slot family is another slot family, by A1's
`tensorEntry_star`).  Its site average contracts by A2: the
product over the factor family is the single tensor entry of
the combined (Sigma-type) slot family, so the word average
is A2b's `tensorAvg` of the combined family and inherits its
channel decomposition — the separated-squares form with no
bound on the number of factors.  This is the uniform form of
the D₄ seat's word contraction (there discharged for words
of length `m ≤ 6` by seat computation); the scope's
"induction on word length" is realized by the combination
over an arbitrary finite factor family, which subsumes every
length at once.  (Disclosed re-cut of the working label, not
of the content: the contraction identity and its uniformity
are the scope's A4 statement.)

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at general
finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of this
line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.LayerKernelTensorChannel

open Finset MeasureTheory
open scoped Matrix ENNReal NNReal InnerProductSpace

namespace ThetLogos

section WordContraction

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [TopologicalSpace G] [DiscreteTopology G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [MeasurableInv G]
variable [CompactSpace G] [LocallyCompactSpace G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable {n : ∀ i, κ i → ℕ}
  (σ : ∀ i, ∀ j, G →* ↥(Matrix.unitaryGroup (Fin (n i j)) ℂ))

/-- **The word entry**: the product over the factor family
of the factors' tensor entries at one group element. -/
def wordEntry (g : G) (A B : ∀ i, ∀ j, Fin (n i j)) : ℂ :=
  ∏ i, tensorEntry (σ i) g (A i) (B i)

/-- The word entry is the tensor entry of the combined
(Sigma-type) slot family, at the combined index tuples. -/
theorem wordEntry_eq_tensorEntry (g : G)
    (A B : ∀ i, ∀ j, Fin (n i j)) :
    wordEntry σ g A B
      = tensorEntry (fun p : Σ i, κ i => σ p.1 p.2) g
          (fun p => A p.1 p.2) (fun p => B p.1 p.2) := by
  conv_rhs => rw [tensorEntry, Fintype.prod_sigma]
  rw [wordEntry]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [tensorEntry]

/-- **The word average**: the counting-measure site average
of a word entry. -/
noncomputable def wordAvg (A B : ∀ i, ∀ j, Fin (n i j)) : ℂ :=
  ((Fintype.card G : ℂ))⁻¹ * ∑ g, wordEntry σ g A B

/-- The word average is A2b's site average of the combined
slot family. -/
theorem wordAvg_eq_tensorAvg (A B : ∀ i, ∀ j, Fin (n i j)) :
    wordAvg σ A B
      = tensorAvg (fun p : Σ i, κ i => σ p.1 p.2)
          (fun p => A p.1 p.2) (fun p => B p.1 p.2) := by
  rw [wordAvg, tensorAvg]
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  exact wordEntry_eq_tensorEntry σ g A B

/-- **The word contraction (channel form).**  The site
average of any finite word of tensor entries separates:
there are finitely many channels `f c` with
`wordAvg σ A B = ∑ c, star (f c A) * f c B`. -/
theorem wordAvg_channel_form :
    ∃ (m : ℕ) (f : Fin m → (∀ i, ∀ j, Fin (n i j)) → ℂ),
      ∀ A B, wordAvg σ A B = ∑ c, star (f c A) * f c B := by
  obtain ⟨m, F, hF⟩ := tensorAvg_channel_form
    (fun p : Σ i, κ i => σ p.1 p.2)
  refine ⟨m, fun c A => F c (fun p => A p.1 p.2), fun A B => ?_⟩
  rw [wordAvg_eq_tensorAvg σ A B, hF]

/-- The word average is conjugate-symmetric in its two
indices. -/
theorem wordAvg_conj_symm (A B : ∀ i, ∀ j, Fin (n i j)) :
    star (wordAvg σ A B) = wordAvg σ B A := by
  rw [wordAvg_eq_tensorAvg σ A B, wordAvg_eq_tensorAvg σ B A,
    tensorAvg_conj_symm]

end WordContraction

end ThetLogos
