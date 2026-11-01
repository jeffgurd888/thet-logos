import ThetLogos.BSDLeadingCoeff
import ThetLogos.BSDCanonicalHeight
import ThetLogos.BSDPeriod

namespace ThetLogos

namespace BSDIntervalPack

/-!
# ThetLogos.BSDIntervalPack — the numeric interval pack (BSD rung 2, brick B2-5)

Source: the BSD rung-2 scoping memo §2, brick **B2-5**, and §1.2
(`scoping-bsd-rung-2-2026-10-29.md`). Design authority: brick B2-4
(`ThetLogos.BSDLeadingCoeff`, the readout `leadingCoeff`), brick
B2-2 (`ThetLogos.BSDCanonicalHeight`, the regulator object `regE2`),
and brick B2-3 (`ThetLogos.BSDPeriod`, the period object
`periodE2`).

**What this file IS.** Exactly three class-(c) HYPOTHESIS Props —
recorded values with their bars, stated and **proved nowhere**:

- `E2LPrimeValue` — `|(leadingCoeff D).re − 2.9200547683| ≤ 1e-5`;
- `E2RegulatorValue` — `regE2 ∈ Set.Icc 1.3486 1.3506`
  (`1.3496 ± 0.001`, exactly, no tighter bar);
- `E2PeriodValue` — `periodE2 ∈ Set.Icc 2.1636817 2.1636818`
  (bar `1e-7`).

Each Prop carries its provenance in its own docstring. These are
hypotheses where only computation owns the values: the tree can
neither compute nor bound the analytic value (memo §4), and the
values of the exact in-tree reals `regE2` and `periodE2` are not
proved by their defining bricks. Nothing in this module asserts
that any of the three Props holds.

**Namespacing note (on the face).** Brick B2-0 already landed
parameterized Props of the same short names in
`ThetLogos.BSDRefinedPin` — `E2RegulatorValue (Reg : ℝ)` and
`E2PeriodValue (Ω : ℝ)` over a free real, and `E2LPrimeValue`
stated on `(deriv D.L 1).re`. This brick's Props are the
specialized forms the memo §1.2 / §2 B2-5 specifies — the regulator
and period Props take **no** argument and are stated on the
concrete objects `regE2` and `periodE2` as landed, and the
`L′` Prop is stated on `(leadingCoeff D).re`, the B2-4 readout
(`leadingCoeff D` is defined as `deriv D.L 1`, so this is the
memo's §1.2 shape on the real value, through the readout). Because
the short names are already taken in `ThetLogos`, this pack's Props
live in the nested namespace `ThetLogos.BSDIntervalPack`; no
existing declaration is edited, shadowed, or redefined.

**Precision fence (inherited from the pin, memo §1.2 / §1.3).**
No statement anywhere may quote Reg or Sha to more precision than
1.3496 / 1.000 ± 0.001. Quoting past the computation is the
specific dishonesty this rung exists to fence. In particular, no
tighter bar may be substituted for the regulator's `±0.001`
without a new computation (memo §2, B2-5 kill condition).

**What this file is NOT — the board fence, on the face.**
- **Not the official statement.** The Clay prize statement is the
  rank equality (rung 1's `BSDRankEquality`, Wiles's chapter text).
  The refined formula these hypotheses serve is Wiles's Remark 1.
  Parts of the official BSD statement closed by this module: **0**.
  NO CLAIM.

Honesty tiers in this file:
- **T5 (statement only):** the three hypothesis Props below —
  `def`s stating `Prop`s, deliberately left unproved.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-- **Class-(c) hypothesis: the value of `L′(E2, 1)` (brick B2-5).**
For an analytic data package `D : BSDAnalyticData E2`, the real
part of the B2-4 leading-coefficient readout lies within `1e-5`
of `2.9200547683`:

  `|(leadingCoeff D).re − 2.9200547683| ≤ 1e-5`.

Stated on the real part, per the memo (§1.2 / §2 B2-5): the
hypothesis is on the real value (`leadingCoeff D` is defined as
`deriv D.L 1`, so this is the memo's shape through the readout).

Provenance: the approximate-functional-equation (AFE) computation
of the 2026-10-27 study, the method validated on E1 to 14 digits
before use on E2; the bar is set two orders looser than the
validation and is dominated by the regulator's bar regardless.
This is a hypothesis `Prop`: stated here, proved nowhere. -/
def E2LPrimeValue (D : BSDAnalyticData E2) : Prop :=
  |(leadingCoeff D).re - 2.9200547683| ≤ 1e-5

/-- **Class-(c) hypothesis: the value of the regulator (brick
B2-5).** The exact in-tree real `regE2` (`canonHeight P35`, brick
B2-2) lies in the closed interval

  `regE2 ∈ Set.Icc 1.3486 1.3506`,

i.e. `1.3496 ± 0.001`.

Provenance: the duplication limit's own bar, from the 2026-10-27
study. The bar is `±0.001` **exactly** — no tighter bar may be
substituted without a new computation (memo §2, B2-5 kill
condition). This is a hypothesis `Prop`: stated here, proved
nowhere. -/
def E2RegulatorValue : Prop :=
  regE2 ∈ Set.Icc 1.3486 1.3506

/-- **Class-(c) hypothesis: the value of the period (brick B2-5).**
The exact in-tree real `periodE2`, as landed by brick B2-3, lies in
the closed interval

  `periodE2 ∈ Set.Icc 2.1636817 2.1636818`,

a bar of `1e-7`.

Provenance: in the 2026-10-27 study, quadrature and the Beta
closed form agreed to 14 digits; the bar is conservative against
that agreement. This Prop is the same statement whether B2-3
landed `periodE2` as the integral object (a) — as it in fact did —
or as the (c)-only parameter: it is stated against the name
`periodE2` as landed. This is a hypothesis `Prop`: stated here,
proved nowhere. -/
def E2PeriodValue : Prop :=
  periodE2 ∈ Set.Icc 2.1636817 2.1636818

end BSDIntervalPack

end ThetLogos
