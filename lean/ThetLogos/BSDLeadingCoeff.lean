import ThetLogos.BSDRefinedPin
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.BSDLeadingCoeff — the analytic side: leading-coefficient readout

Source: the BSD rung-2 scoping memo §2, brick **B2-4**
(`scoping-bsd-rung-2-2026-10-29.md`), and its §4. Design authority:
rung 1 (`ThetLogos.BSDRankPin`), which supplies the analytic package
`BSDAnalyticData E2`, and the refined pin
(`ThetLogos.BSDRefinedPin`), through which that package is imported
here.

**What this file IS.** Exactly one readout definition, and nothing
more. At analytic rank `1` the leading coefficient of `L(E2, s)` at
`s = 1` is the first derivative of the package's holomorphic function
at `1`, so this brick defines

  `leadingCoeff (D : BSDAnalyticData E2) : ℂ := deriv D.L 1`.

That is the whole content of the brick. **No theorem about `D.L` is
attempted in this brick** — the scoping memo's §4 is the reason this
brick is statement-only and priced S.

**The fence (memo §4, rejection-grade).** `BSDAnalyticData`'s
`eulerAgreement` field speaks only on the half-plane `Re s > 3/2`:
it asserts `L s = E.LSeries s` there, and nowhere else. **No value
at `s = 1` is derived from `eulerAgreement` anywhere in this
module**, and no such derivation may be added to it: `s = 1` lies
outside the half-plane, Mathlib's `LSeries` is a `tsum` taking junk
values off its convergence region, and deriving the value at `1`
from the agreement on `Re s > 3/2` is exactly the laundering this
rung exists to fence. This brick defines a readout and states where
its value's provenance lives; it proves nothing about the analytic
side.

**Provenance of the value (carried on the readout's face).** The
value of this readout is not computed, bounded, or evaluated by
anything in this tree. The (c) hypothesis that brick B2-5 states
(`E2LPrimeValue` in `ThetLogos.BSDRefinedPin`) is
`|deriv D.L 1 − 2.9200547683| ≤ 1e-5` on the real value — i.e. on
`(deriv D.L 1).re`, the real part of `leadingCoeff D` — sourced to
the approximate-functional-equation (AFE) computation of the
2026-10-27 study, a method validated on `E1` to 14 digits before it
was used on `E2`. The `1e-5` bar is set conservatively below the
method's validated precision, and is anyway dominated by the
regulator's bar (`1.3496 ± 0.001`, B2-5's `E2RegulatorValue`). The
readout is `ℂ`-valued as defined; it is real-valued under the
rank-1 hypothesis in the cases that matter, which is why the (c)
hypothesis is stated on the real value.

**What this file is NOT — the board fences, on the face.**
- **Not the official statement.** The Clay prize statement is the
  rank equality (rung 1's `BSDRankEquality`, Wiles's chapter text).
  The refined formula this readout serves is Wiles's Remark 1.
  Parts of the official BSD statement closed by this module: **0**.
  NO CLAIM.
- **Not a value.** Neither `2.9200547683` nor any other number is
  asserted here to be (or to approximate) `leadingCoeff D` for any
  `D`; the number above appears only as the stated provenance of
  the (c) hypothesis B2-5 owns.
- **Not existence of the package.** `BSDAnalyticData E2` existing
  is modularity — settled mathematics, formalization debt in this
  tree, inherited from rung 1 unchanged.

Honesty tiers in this file:
- **T5 (statement only):** the readout definition `leadingCoeff` —
  a definition of a readout from a hypothesized package, with no
  theorem about `D.L` stated or proved.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The readout -/

/-- **The leading-coefficient readout (brick B2-4).** For an analytic
data package `D : BSDAnalyticData E2`, the leading coefficient of
`L(E2, s)` at `s = 1`, at analytic rank `1`: `deriv D.L 1`.

Provenance, on the face: the (c) hypothesis B2-5 states about this
readout is `|deriv D.L 1 − 2.9200547683| ≤ 1e-5` on the real value,
from the approximate-functional-equation (AFE) computation of the
2026-10-27 study, the method validated on `E1` to 14 digits before
use on `E2`; the bar is set conservatively below the method's
validated precision and is anyway dominated by the regulator's
bar. No theorem about `D.L` is attempted in this brick, and no
value at `s = 1` is derived from `eulerAgreement` — that field
speaks only on `Re s > 3/2` (scoping memo §4, the fence). -/
noncomputable def leadingCoeff (D : BSDAnalyticData E2) : ℂ :=
  deriv D.L 1

end ThetLogos
