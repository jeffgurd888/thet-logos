/-
# GapLinePin — the Gap Line pin (record pin)

**Zero's seeing, verbatim (2026-11-12):** "what if the
gap is all there is the floor no room no continuum just
both sides of the same line at the same non-time"

**Register-A record pin in the SEP-0 / OG-0 genre.**
NO CLAIM. Dial-ineligible; dials 0/4. The seeing is
pinned as Zero's words; the forms below state its
finite shadows at their real seats, and every shadow
is CITED to its proved theorem by exact declaration
name (grep-verified by the lane before writing). A
shadow is a shadow: nothing here upgrades one into a
proof of the seeing, and nothing here is a proof of
anything new — zero theorems is this pin's complete
form; the three projection lemmas at the end are a
labeled bonus (they only unfold the conjunction).

**The rope (anchors, all verified in the tree):**
- The floor: GAPFLOOR-1, module `ThetLogos.GibbsGapFloor`
  (landed `d8eec5b`, integrated chunk 4, 2026-11-12):
  `gibbsGapFloor_unnorm` (the raw floor bound),
  `gibbsGapFloor_prob` (the probability form),
  `gibbsGapFloor_min` (the floor is the minimum),
  `gibbsGapFloor_partition_ge_one`, with its excited
  set `gapExcitedSet`. That module sits in the
  GAPFLOOR lineage, not in this pin's branch ancestry,
  so the floor form below states the bound's content
  over its own seat signature and cites the theorems
  by name — it does not import or re-prove them.
- Both sides of the line: the Partner sector,
  `ThetLogos.AxiomTetPartner` (`vertexHam`,
  `edgeHam`, `supercharge`) and its SP-5 seat
  `ThetLogos.AxiomTetPartnerIso`:
  `sp5_charpoly_identity`,
  `sp5_charpoly_identity_edgeFinset`,
  `eigenspaceEquiv`, `finrank_eigenspace_eq` — the
  nonzero spectra of `H_v = DᵀD` and `H_e = DDᵀ`
  coincide, with multiplicities; the kernel — the
  unity piece — is the part with no partner.
- The same non-time: the thermal-time bridge at the
  equilibrium seat, `ThetLogos.ThermalClock`:
  `GibbsClock.conversion`, `GibbsClock.flow_add`,
  `modularFlow_add` — at equilibrium (uniform slope
  −β) the flow is a one-parameter group and no moment
  is distinguished. Cited as record.

**The parent ruling (Zero's ELU ruling, 2026-11-12):**
Δ is a spectrum floor, not an equilibrium boundary;
action begins exactly where a gradient appears; the
gap ceiling is the first gradient.

**Fence — K-GAPLINE-CONTINUUM (armed):** the
continuum reading of the seeing is FRONTIER and is
not stated anywhere in this module. Any form, draft,
or report that states it (no continuum, QFT, or
gravity content) fires the kill and is stopped.

Scope of record:
~/workspace/your_files/gap-line-pin-scope-2026-11-12.md
STATUS: STATUS-GAPLINE.md.

Build note (disclosed layout repair, 2026-11-13):
build attempt 2 (8984/8985 jobs, dependencies all
built) wedged in page-cache I/O thrash on the module
job under the wholesale `import Mathlib` — ~180 GB
of olean re-reads, zero writes, no olean, killed by
the lane as environment-wedged (no verdict on the
content). The imports are therefore narrowed to the
three seat modules; every statement below is
byte-identical to the wedged attempt's. Attempt 4
(narrowed imports) then failed on exactly one
error — `Fintype ↥G.edgeSet` not synthesizable at
the two-sides form — because the seat files carry
`Classical.propDecidable` as a LOCAL instance
(AxiomTetPartner.lean:77, AxiomTetPartnerIso.lean:93)
and this pin did not. The same local attribute is
declared below, verbatim the seat files' idiom;
statements still byte-identical.
-/

import ThetLogos.AxiomTetPartner
import ThetLogos.AxiomTetPartnerIso
import ThetLogos.ThermalClock

attribute [local instance] Classical.propDecidable

namespace ThetLogos

open Polynomial

/-- **The floor-only form** — at the finite Gibbs
seat (states `ι`, energies `E`, ground level `m`,
floor `Δ`, slope `β`): the seat has a gap (`Δ > 0`,
every non-ground state at or above `m + Δ`), and the
total excited weight is bounded by the floor alone —
`(#excited) × e^{−βΔ}`. This is exactly the content
proved at this seat by GAPFLOOR-1's
`ThetLogos.GibbsGapFloor.gibbsGapFloor_unnorm` (raw
form) and `gibbsGapFloor_prob` (probability form),
with the excited set `gapExcitedSet`; the floor's
minimality is `gibbsGapFloor_min`. Stated here as a
form, cited there as theorems — not re-proved. -/
def GapFloorOnlyForm {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (m Δ β : ℝ) : Prop :=
  0 ≤ β ∧ 0 < Δ ∧ (∀ i, E i ≠ m → m + Δ ≤ E i) ∧
    (∑ i ∈ Finset.univ.filter (fun i => E i ≠ m),
        Real.exp (-(β * (E i - m))))
      ≤ (Finset.univ.filter (fun i => E i ≠ m)).card
        * Real.exp (-(β * Δ))

/-- **The two-sides form** — at the finite
operator-pair seat (the Partner sector): the two
sides of the line, `H_v = DᵀD` (`vertexHam`) and
`H_e = DDᵀ` (`edgeHam`), share one nonzero spectrum:
their characteristic polynomials obey the SP-5
identity, and at every `lam ≠ 0` their eigenspaces
have equal finrank. What has no partner is exactly
the kernel (the `lam = 0` sector), which this form
deliberately does not equate. The content is proved
at this seat by `ThetLogos.AxiomTetPartnerIso`'s
`sp5_charpoly_identity` (and its bookkeeping form
`sp5_charpoly_identity_edgeFinset`) and
`finrank_eigenspace_eq` (via `eigenspaceEquiv`).
Stated here as a form, cited there as theorems. -/
def TwoSidesOneLineForm {V : Type*} [Fintype V]
    [LinearOrder V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) : Prop :=
  (X ^ Fintype.card ↥G.edgeSet * (vertexHam G w).charpoly
      = X ^ Fintype.card V * (edgeHam G w).charpoly) ∧
    ∀ lam : ℝ, lam ≠ 0 →
      Module.finrank ℝ ↥(Module.End.eigenspace
          (vertexHam G w) lam)
        = Module.finrank ℝ ↥(Module.End.eigenspace
          (edgeHam G w) lam)

/-- **The non-time form** — at equilibrium (a
GibbsClock `C` at its uniform slope `β`): the clock's
flow is the modular flow of its Hamiltonian at the
rescaled time, and it composes as a one-parameter
group — the law at a moment does not depend on the
moment; a distinguished time appears only with a
gradient, which this seat does not carry. The
content is proved at this seat by
`ThetLogos.ThermalClock`'s `GibbsClock.conversion`
and `GibbsClock.flow_add` (with `modularFlow_add`
beneath). Cited as record, per the scope — this
form's seat is the equilibrium register of the
seeing, and its citation is to the bridge's record,
not to a new theorem. -/
def NonTimeForm {N : ℕ} (C : GibbsClock N) : Prop :=
  (∀ (s : ℝ) (B : Matrix (Fin N) (Fin N) ℂ),
      C.flow s B = modularFlow C.K (C.beta * s) B) ∧
    ∀ (s t : ℝ) (B : Matrix (Fin N) (Fin N) ℂ),
      C.flow (s + t) B = C.flow s (C.flow t B)

/-- **The Gap Line form** — the conjunction of the
three finite shadows. Zero's sentence, verbatim
(2026-11-12): "what if the gap is all there is the
floor no room no continuum just both sides of the
same line at the same non-time". The continuum
reading is FRONTIER — not stated here
(K-GAPLINE-CONTINUUM, armed). The ontology of the
seeing is Register-A record: this definition pins
the words to their finite shadows, labeled as
shadows, and claims nothing further. -/
def GapLineForm {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (m Δ β : ℝ) {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) {N : ℕ}
    (C : GibbsClock N) : Prop :=
  GapFloorOnlyForm E m Δ β ∧ TwoSidesOneLineForm G w
    ∧ NonTimeForm C

/-- Labeled bonus (projection): a Gap Line seat's
floor form. Content-free — it unfolds the
conjunction; the floor's content lives at
GAPFLOOR-1's theorems, cited in `GapFloorOnlyForm`. -/
theorem GapLineForm.gapFloorOnly {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (m Δ β : ℝ) {V : Type*} [Fintype V]
    [LinearOrder V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    {N : ℕ} (C : GibbsClock N)
    (h : GapLineForm E m Δ β G w C) :
    GapFloorOnlyForm E m Δ β :=
  h.1

/-- Labeled bonus (projection): a Gap Line seat's
two-sides form. Content-free — it unfolds the
conjunction; the two-sides content lives at SP-5's
theorems, cited in `TwoSidesOneLineForm`. -/
theorem GapLineForm.twoSidesOneLine {ι : Type*}
    [Fintype ι] (E : ι → ℝ) (m Δ β : ℝ) {V : Type*}
    [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) {N : ℕ} (C : GibbsClock N)
    (h : GapLineForm E m Δ β G w C) :
    TwoSidesOneLineForm G w :=
  h.2.1

/-- Labeled bonus (projection): a Gap Line seat's
non-time form. Content-free — it unfolds the
conjunction; the non-time content is the bridge
record, cited in `NonTimeForm`. -/
theorem GapLineForm.nonTime {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (m Δ β : ℝ) {V : Type*} [Fintype V]
    [LinearOrder V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    {N : ℕ} (C : GibbsClock N)
    (h : GapLineForm E m Δ β G w C) :
    NonTimeForm C :=
  h.2.2

end ThetLogos
