/-
# F2-GATE-SEAT: seat separation at `4 ≤ N`

First brick after the re-pin
(`ThetLogos.Span3SeatSchurGateRepin`): the seat
separation underlying the re-pinned gate's honest
domain.

**What this brick proves, and what it does not.**
GATE-2's kill of the original GATE-0 pin
(`g2c_counterexample`, in
`ThetLogos.Span3SeatSchurGateFiber`) ran through one
exact mechanism: at `N = 2` the two seat embeddings
COINCIDE — `embLayerTop = embLayerBot` at `N = 2`
(`embLayerTop_eq_embLayerBot_at_two`), because the
top extraction site time `N / 2 - 1` equals `0`, the
bottom extraction's time. This brick proves that
mechanism is excluded at every even `N ≥ 4`: the two
embeddings differ at EVERY layer link `ℓ` (the
`∀ ℓ` form below — the definitions give it for every
`ℓ`, since the embeddings differ in the time
coordinate of the site alone, independently of `ℓ`'s
spatial data and direction). The embeddings differ in
a time coordinate: the top embedding's site is
`topSite ⟨ℓ.1.1, ℓ.2.1⟩`, whose time coordinate has
value `N / 2 - 1 ≥ 1` at `4 ≤ N`, while the bottom
embedding's site is `ℓ.1.1` itself, whose time
coordinate has value `0`.

**Scope fence, on the face:** this brick decides the
SEAT, not G2c. The re-pinned gate's decision lemma
(`fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback_gate4`)
remains OPEN; proving the embeddings apart at
`4 ≤ N` removes the `N = 2` coincidence mechanism and
nothing more — it does not prove the dressed
fiber-average invariance, any G2a / G2b identity, or
any part of the gate discharge.

**NO CLAIM** — parts of any official Millennium
statement closed by this module: 0. Dials: 0/4. Even
a completed re-pinned gate plus F2-W3 proves neither
FACT nor clause (a); `LayerKernelPos`, `𝒜 ⪰ 0`, and
uniformity remain open. No Gram factorization of `𝒜`
appears or is used here (the weld fence): this is a
statement about two landed link embeddings and a
natural-number inequality.

This module is NOT in the root import list of the
library; it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchur

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Span3SeatSchurGateSeat

variable {N : ℕ} [NeZero N]

/-- **Seat separation at `4 ≤ N` (headline).** For
even `N` with `4 ≤ N`, the top and bottom seat
embeddings do not coincide — at any layer link, hence
at every layer link: if `embLayerTop hN ℓ` equalled
`embLayerBot hN ℓ`, their sites' time coordinates
would agree, but the top site's time coordinate has
value `N / 2 - 1` (`topSite_val`), which is `≥ 1`
at `4 ≤ N`, while the bottom site is `ℓ`'s own site,
whose time coordinate has value `0` (the defining
property `ℓ.2.1` of a layer link). This is exactly
the coincidence mechanism of the `N = 2` kill
(`embLayerTop_eq_embLayerBot_at_two`, where
`N / 2 - 1 = 0`), PROVED excluded at `4 ≤ N`. G2c
itself remains the re-pinned gate's open
decision lemma — it decides the seat, not G2c. -/
theorem embLayerTop_ne_embLayerBot_of_four_le (hN : Even N)
    (hN4 : 4 ≤ N) :
    ∀ ℓ : LayerLink N, embLayerTop hN ℓ ≠ embLayerBot hN ℓ := by
  intro ℓ hEq
  have htop : ((embLayerTop hN ℓ).1.1 0).val = N / 2 - 1 :=
    topSite_val ⟨ℓ.1.1, ℓ.2.1⟩
  have hbot : ((embLayerBot hN ℓ).1.1 0).val = 0 := ℓ.2.1
  have hv : ((embLayerTop hN ℓ).1.1 0).val
      = ((embLayerBot hN ℓ).1.1 0).val :=
    congrArg (fun m : ↥(posLinks (N := N)) => (m.1.1 0).val) hEq
  rw [htop, hbot] at hv
  omega

end Span3SeatSchurGateSeat

end ThetLogos
