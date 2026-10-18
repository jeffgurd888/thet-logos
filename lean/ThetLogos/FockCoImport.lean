import ThetLogos.FermionicFock
import ThetLogos.BosonicFock
import ThetLogos.SecondQuantDGamma
import ThetLogos.SecondQuantGamma
import ThetLogos.FermionicInteraction
import ThetLogos.FermionicLimit
import ThetLogos.FermionicLimitOps

/-!
# Co-import smoke module — the `adag` repair's certificate

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

## The fence

The bosonic *assembly* stack (`BosonicAssembly` and everything above
it: `BosonicSecondQuant`, `BosonicGamma`, `BosonicGammaFunctor`,
`BosonicInteraction`, `BosonicLimit`, `BosonicLimitOps`) is NOT
imported here, for one named reason: `BosonicAssembly` also declares
`ThetLogos.numberOp` and `ThetLogos.numberOp_basis`, colliding with
`FermionicFock`'s declarations of the same names. That is a second,
separately-priced rename (census in the dossier), not part of this
repair. Nothing in this module is a physics claim.
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
