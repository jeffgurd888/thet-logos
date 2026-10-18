import ThetLogos.FermionicFock
import ThetLogos.BosonicFock
import ThetLogos.SecondQuantDGamma
import ThetLogos.SecondQuantGamma
import ThetLogos.FermionicInteraction
import ThetLogos.FermionicLimit
import ThetLogos.FermionicLimitOps
import ThetLogos.BosonicAssembly
import ThetLogos.BosonicSecondQuant
import ThetLogos.BosonicInteraction
import ThetLogos.BosonicLimitOps
import ThetLogos.FockPackagingBos
import ThetLogos.FockPackagingFerm

/-!
# Co-import smoke module — the `adag` repair's certificate,
extended by the `numberOp` repair (2026-10-18)

This module contains **no declarations of its own** — by design. Its
green build is the machine-checked proof that the fermionic and
bosonic Fock stacks can now live in one Lean environment, which the
duplicate declarations `ThetLogos.adag`, `ThetLogos.ann`,
`ThetLogos.adag_basis`, `ThetLogos.ann_basis` previously made
impossible. The repair (2026-10-17) renamed the bosonic side to
`adagBos`, `annBos`, `adagBos_basis`, `annBos_basis`; the fermionic
side is untouched. Dossier: `whitepaper/adag-repair-2026-10-17.md`.

The `#check` lines below name both sides' creation and annihilation
operators, with their basis-action statements, in a single
environment — the statement-level prerequisite for any mixed
fermion–boson (Yukawa) term.

## The second fence — discharged 2026-10-18

The bosonic *assembly* stack (`BosonicAssembly` and everything above
it: `BosonicSecondQuant`, `BosonicGamma`, `BosonicGammaFunctor`,
`BosonicInteraction`, `BosonicLimit`, `BosonicLimitOps`) was NOT
imported here, for one named reason: `BosonicAssembly` also declared
`ThetLogos.numberOp` and `ThetLogos.numberOp_basis`, colliding with
`FermionicFock`'s declarations of the same names. That second rename
has now been executed (2026-10-18): the bosonic side is renamed to
`numberOpBos` / `numberOpBos_basis` at the definitions in
`BosonicAssembly` and at every bosonic use site (16 lines in 3 files;
the fermionic side is untouched). Dossier:
`whitepaper/numberop-rename-2026-10-18.md`. The assembly stack is
therefore imported above, and the `#check` / `example` lines below
exercise BOTH statistics' number operators in this single
environment — the certificate that the fence is gone.

## The third fence — discharged 2026-10-18 (packaging modules)

The two Fock *packaging* modules (`FockPackagingBos`,
`FockPackagingFerm`) could not be co-imported either: six helper
names were declared by both — `inner_linearCombination_mixed`,
`exists_forall_mem_of_monotone`, `linearCombination_eq_sum`,
`ofReal_norm_sq`, `summable_mul_of_summable_sq`,
`tsum_eq_of_tendsto_sum_exhaustion`. (The Fock *stacks* below the
packaging layer were already co-importable — the two fences above.)
The repair renames the bosonic side of all six by the house suffix
(`...Bos`), at the definitions and every bosonic use site (20 lines
across `FockPackagingBos.lean` and `FockLorentzBos.lean`; the
fermionic side is untouched). Both packaging modules are therefore
imported above, and the `#check` lines at the end of this module
name both sides' helpers in this single environment. Dossier:
`whitepaper/packaging-rename-2026-10-18.md`. Nothing in this module
is a physics claim.
-/

-- Fermionic side (Rung 5/8 lineage; names unchanged by the repair).
#check @ThetLogos.adag
#check @ThetLogos.ann
#check @ThetLogos.adag_basis
#check @ThetLogos.ann_basis

-- Bosonic side (renamed by the repair: `adag` → `adagBos`, etc.).
#check @ThetLogos.adagBos
#check @ThetLogos.annBos
#check @ThetLogos.adagBos_basis
#check @ThetLogos.annBos_basis

-- Number operators, both statistics, one environment (2026-10-18).
-- Fermionic side: names unchanged by either repair.
#check @ThetLogos.numberOp
#check @ThetLogos.numberOp_basis
#check @ThetLogos.numberOp_apply_basis

-- Bosonic side: renamed by the `numberOp` repair
-- (`numberOp` → `numberOpBos`, `numberOp_basis` → `numberOpBos_basis`).
#check @ThetLogos.numberOpBos
#check @ThetLogos.numberOpBos_basis
#check @ThetLogos.numberOp_vacuum

/-- Joint vacuum certificate (anonymous — this module carries no named
declarations): in one environment, the fermionic number operator kills
the empty-occupation basis vector and the bosonic number operator
kills the bosonic vacuum. -/
example (d : ℕ) :
    ThetLogos.numberOp d (ThetLogos.fockBasis d ∅) = 0 ∧
    ThetLogos.numberOpBos d (ThetLogos.vacDom d) = 0 := by
  refine ⟨?_, ThetLogos.numberOp_vacuum d⟩
  rw [ThetLogos.numberOp_apply_basis]
  simp

/-- Joint basis-action certificate (anonymous): in one environment,
the fermionic number operator acts on the occupation basis by the
eigenvalue `S.card`, and the bosonic number operator acts on the
occupation basis by the total occupation count `∑ i, c i`. -/
example (d : ℕ) (S : Finset (Fin d)) (c : ThetLogos.Config d) :
    ThetLogos.numberOp d (ThetLogos.fockBasis d S)
      = (S.card : ℂ) • ThetLogos.fockBasis d S ∧
    ThetLogos.numberOpBos d
        ⟨ThetLogos.boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (∑ i, (c i : ℂ)) •
        ⟨ThetLogos.boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ :=
  ⟨ThetLogos.numberOp_apply_basis d S, ThetLogos.numberOpBos_basis d c⟩

-- Packaging-module helpers, both statistics, one environment
-- (2026-10-18, the third fence's certificate).
-- Bosonic side: renamed by the packaging repair (`...` → `...Bos`).
#check @ThetLogos.inner_linearCombination_mixedBos
#check @ThetLogos.exists_forall_mem_of_monotoneBos
#check @ThetLogos.linearCombination_eq_sumBos
#check @ThetLogos.ofReal_norm_sqBos
#check @ThetLogos.summable_mul_of_summable_sqBos
#check @ThetLogos.tsum_eq_of_tendsto_sum_exhaustionBos

-- Fermionic side: names unchanged by the packaging repair.
#check @ThetLogos.inner_linearCombination_mixed
#check @ThetLogos.exists_forall_mem_of_monotone
#check @ThetLogos.linearCombination_eq_sum
#check @ThetLogos.ofReal_norm_sq
#check @ThetLogos.summable_mul_of_summable_sq
#check @ThetLogos.tsum_eq_of_tendsto_sum_exhaustion
