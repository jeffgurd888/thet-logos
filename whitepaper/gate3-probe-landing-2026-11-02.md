# F2-GATE-3 FALSITY PROBE — LANDING DOSSIER: **PROBE EXHAUSTED; K-GATE-3 does NOT fire** (2026-11-02)

**Brick:** the falsity probe on GATE-3, fired under Jeff's
2026-11-02 00:49 EST decision (the probe chosen over the
core-chain route and over leaving GATE-3 standing).
Parent-verified: main-tree targeted build green
(`lake build ThetLogos.Span3SeatSchurGateProbe`, 3,646
jobs); CI axiom fence PASS 33/33 (registry grown 32 → 33
by this landing); zero-sorry gate PASS (475 files).

## VERDICT, at full rank

**PROBE EXHAUSTED. No counterexample was produced, in
tree or in the finite seat. K-GATE-3 stays DOSSIER-GRADE
— it is NOT machine-killed by this run.** The probe's
searched box and methods are recorded below (§4–§6) so
nobody re-runs the same search blind. **Failure to kill
is NOT evidence that GATE-3's general form is true**: at
every seat the probe could certify, the form is either
provably true or the seat is beyond the probe's
certifying power (§3). The core-chain route (proving the
PSD fact about `𝒜` itself) remains Jeff's untaken
option, exactly as before this run. GATE-3's headline
remains **not dischargeable through the registered
route**, on the strength of the proceed run's dossier
obstruction — unchanged.

## §1 — The target, pinned verbatim

GATE-0 item 5, frozen in
`lean/ThetLogos/Span3SeatSchurGatePost.lean` (lines
290–299), in that module's section context
(`{G} [Group G] … (μG : Measure G) [IsProbabilityMeasure
μG] [IsMulLeftInvariant] [IsMulRightInvariant]
[IsInvInvariant] (ρ : G →* ↥(Matrix.unitaryGroup
(Fin d) ℂ)) {N} [NeZero N]`):

```lean
def pullBotKernel_seatFactorApproxExpansion : Prop :=
  ∀ (hN : Even N) (β : ℝ), 0 ≤ β →
    LayerKernelPos (N := N) μG ρ β →
    SeatFactorApproxExpansion μG ρ hN β
```

with item 1 (`SeatFactorApproxExpansion`, same module):
there exist finite types `ι n`, `c n i ≥ 0` real, layer
functions `φ n i`, factors pulled back
`a n i = φ n i ∘ tauBot hN`, each difference kernel
`pullBotKernel − Σ i, c i • (a i ⊗ conj (a i))` in
`MemLp 2` on the product probability space, and its HS
norm (`eLpNorm · 2 (μ.prod μ)`) tending to `0`.

A counterexample — what this probe was ordered to build
— is one seat `(G, μG, ρ, N)`, one `Even N` witness, one
`β ≥ 0`, with `LayerKernelPos` PROVED there and
`SeatFactorApproxExpansion` REFUTED there.

**The bridge (dossier grade, the proceed run's
equivalence).** If the expansion exists at `(hN, β)`,
every layer pairing at that seat is nonnegative: a Gram
sum pairs nonnegatively against any pulled-back test
function (`seatPairing` of `Σ cᵢ aᵢ⊗conj aᵢ` against
`F ∘ tauBot` is `Σ cᵢ |∫ (F∘tauBot)·aᵢ|² ≥ 0`), HS
limits preserve the inequality (the seat pairing is
HS-continuous in the kernel at bounded test functions),
and the pullback pairing of `F ∘ tauBot` against
`pullBotKernel` is the layer pairing of `F` (landed
stage-2 transports). So **one** layer observable `F`
with `layerPairing F < 0` at a seat where
`LayerKernelPos` holds refutes the expansion at that
seat. The cheapest witness shape is
`F = δ_u − δ_{u'}`, whose pairing sign is the sign of
`𝒜(u,u) + 𝒜(u',u') − 𝒜(u,u') − 𝒜(u',u)`.

## §2 — What landed in tree: the β = 0 fence (FULL)

`lean/ThetLogos/Span3SeatSchurGateProbe.lean`
(strict 3 / defs 0, all three theorems on exactly
`[propext, Classical.choice, Quot.sound]`):

- `layerKernel_zero` — at `β = 0` the layer kernel is
  the constant `1` (the action carries the prefactor
  `β`; every Boltzmann factor is `exp 0`; the stratum
  average of `1` over a probability measure is `1`).
- `pullBotKernel_zero` — the bottom pullback kernel at
  `β = 0` is the constant `1`.
- `seatFactorApproxExpansion_zero` — **item 1's
  expansion EXISTS at `β = 0` at every seat,
  unconditionally** (constant Gram family
  `ι n = PUnit`, `c = 1`, `φ = 1`; difference kernel
  identically zero). No `LayerKernelPos` hypothesis is
  used.

Consequence, on the face: **the probe has no
counterexample seat at `β = 0`, at any `(G, ρ, N)`.**
Item 5 holds at `β = 0` outright. This fences the
probe's search space to `β > 0` in-tree. It is a
degenerate-seat fence, **not** progress on item 5 at
any `β > 0` (K-F2-4 hygiene: no sentence in this
dossier describes it as such).

## §3 — The squeeze: why no in-tree kill was available

A machine-checked kill needs, at ONE seat, BOTH halves
proved: `LayerKernelPos` (the hypothesis) and a
negative layer pairing (the refutation). The corpus's
only route to `LayerKernelPos` anywhere is from `FACT`
(`Span3FactLayerKernelPos`: FACT ⇒ `LayerKernelPos`) —
FACT itself is open. The seats where the hypothesis is
certifiable by degenerate means are exactly the seats
where the kernel degenerates with it:

- `β = 0`: kernel `≡ 1`; expansion proved (§2).
- Trivial `G`, or `ρ` with `plaquetteDensity ≡ 0`
  (e.g. `ρ` trivial): kernel `≡ 1`; expansion trivial.
- Dimension-1 `ρ` (abelian shadow): §5 — the kernel is
  PSD on ALL layer observables, so no negative pairing
  exists there at all.

At every remaining seat (genuine nonabelian `ρ` of
dimension `≥ 2`, `β > 0`) the hypothesis half is
exactly as unproved as FACT. The probe is squeezed
out: **where a kill could live, its hypothesis cannot
currently be certified; where the hypothesis can be
certified, no kill lives.** This is a statement about
the probe's reach, recorded at dossier grade — not a
theorem about GATE-3, and not evidence for item 5.

## §4 — The finite-seat probe (BR1-031): the concrete kernel at its smallest nonabelian seat

**Seat.** The concrete corpus kernel itself, evaluated
at `N = 2` (`LayerSite = (ZMod 2)³`, 8 sites; 24 layer
links; stratum `α ∈ G⁸` averaged uniformly), `G = S₃`,
`ρ` = the standard 2-dimensional irrep (trace by cycle
type: `e ↦ 2`, transposition `↦ 0`, 3-cycle `↦ −1`;
density `1 − tr/2 ∈ {0, 1, 3/2}`), `β ∈ {1/2, 1, 2}`.
The plaquette word is the corpus's own
(`PlaneCrossingCube.layerConfig`):
`w(c,ν) = α_c · u'(c,ν) · α_{c+ν}⁻¹ · u(c,ν)⁻¹`, and
`𝒜(u,u') = 6⁻⁸ Σ_α Π_{c,ν} exp(−β·density(w(c,ν)))`.
Script `routeb-general-scratch/f2gate3-probe.py`,
record `f2gate3-probe-out.txt`; registered as
**BR1-031**.

**Evaluators.** Two independent implementations (flat
enumeration over `S₃⁸`; tensor contraction on the cube
graph) agree on sampled pairs to `0.0` printed
difference (`𝒜 = 1.3820180733e-5` at `β = 1/2`,
`1.100427e-9` at `β = 1`, for the drawn pair).

**Detector controls (all pass).**
- `β = 0`: `𝒜(u,u') = 1.000000000000000` exactly
  (matches §2's theorem).
- Gauge-orbit identity: `𝒜(u, γ•u) = 𝒜(u,u)` holds to
  `9.5e-22` for a drawn `γ` at `β = 1` — the stratum
  right-multiplication substitution, verified in the
  implementation; orbit-difference pairing `≈ 2e-21`.
- Abelian control seat (`ρ` = sign, `d = 1`): 30 drawn
  pair-differences, **zero negative** — as §5's Fourier
  computation requires. A detector that cannot fire on
  the control and fires nowhere else is the honest
  configuration.

**Search box (exactly this, no more).** At each
`β ∈ {1/2, 1, 2}`: 640 pair-differences
`D(u,u') = 𝒜(u,u) + 𝒜(u',u') − 𝒜(u,u') − 𝒜(u',u)` —
the one-link neighbourhoods (24 links × 5 alternative
values) of 5 base configurations (identity + 4 drawn),
plus 40 drawn random pairs. At `β = 1`: 24 drawn
low-support observables (support 3 drawn from a
6-configuration family of identities, drawn configs,
and gauge transforms, random complex coefficients),
full pairing evaluated.

**Results.** **Zero negative pair-differences in all
1,920; zero negative pairings in the 24 draws** (min
real part `4.399098e-07 > 0`). Minimum `D = 0.000000e+00`
attained at the same structured pair at all three `β`
(base = identity configuration, link 0 changed to the
3-cycle `(2,0,1)`) — a β-independent exact zero,
consistent with a symmetry zero of the seat; it is
`≥ 0` either way. Kernel magnitudes at this seat are
small (`𝒜(u,u) ≈ 6.4e-7` at `β = 1` for the drawn
config); all kernel values are means of positive terms
(no cancellation inside `𝒜`), and the negative
threshold `−1e-9` sits far above the float64 noise of
the differences. **The `LayerKernelPos` half at this
seat was NOT probed** (sampling cannot certify a
universal statement over invariant observables); the
probe searched only the refutation half, and found
nothing in the box.

## §5 — The dimension-1 fence (dossier-grade computation)

For `ρ` = the sign character (any `G` with a surjective
sign, any `N`): the plaquette word's sign is
`ε_c ε_{c+ν} · s(u') s(u)` per slot (`ε_c = sign(α_c)`
uniform independent), so `𝒜(u,u') = κ(s(u) ⊙ s(u'))`
for a kernel `κ` on the pattern group `{±1}^{links}`,
`κ(τ) = E_ε Π_{slots} g(ε_c ε_{c+ν} τ_slot)`,
`g(1) = 1`, `g(−1) = r = e^{−2β}`. Its Fourier
coefficients are
`κ̂(S) = 2^{−|slots|} (1−r)^{|S|} (1+r)^{|slots|−|S|} · [S \text{ Eulerian}] ≥ 0`
(Eulerian: every site has even degree in `S`, else the
`ε`-expectation vanishes) — all `≥ 0`, so `κ` is
positive-definite on the pattern group and `𝒜` is PSD
on **all** layer observables at any sign-rep seat. No
counterexample lives at a dimension-1 seat of this
form; combined with GATE-1's class result (BR1-028),
the abelian side of the search space is closed at
dossier grade. (Hand computation, labeled as such;
not a Lean theorem. A general character of order `> 2`
is NOT covered by this computation and was not
searched.)

## §6 — What remains, named

1. **GATE-3's general form stands unrefuted and
   undisposed**, dossier-obstructed (proceed run) and
   probe-exhausted (this run). `seatSchurProductStepOpen`
   (W3) stays OPEN behind GATE-3/GATE-4 as registered;
   GATE-4's conditional form is a separate live lane
   (GATE-4C, registered 2026-11-02).
2. **The core-chain route is untouched by this run**
   and remains Jeff's option: it, not the probe, is the
   route that could decide item 5 at nonabelian seats —
   by proving the PSD fact about `𝒜` (which would make
   item 5 TRUE) or by a core-grade counterexample
   (which would need `LayerKernelPos` certified
   independently of FACT — no such certification is
   currently known at any nonabelian seat).
3. **Re-running this probe's box is wasted motion**:
   the one-link neighbourhoods and drawn pairs at
   `S₃ / d = 2 / N = 2`, `β ∈ {1/2, 1, 2}`, and the
   `β = 0` / trivial / sign seats, are closed. A future
   probe must change the box (larger support
   observables, character order `> 2`, `N ≥ 4` seats,
   or a certified-`LayerKernelPos` seat if one is ever
   built) — or not run.

## Fences

No `𝒜 ⪰ 0` proof work was done or attempted; nothing
in this run factored `𝒜`; the weld consumed nothing.
S-8B-4 remainder untouched; FRONTIER unpriced; no
sends/posts/signatures/spending/accounts; no
LIFE-fleet. **NO CLAIM** — parts of any official
Millennium statement closed: 0. Dials: 0/4.

## Census

Contribution +3 strict / +0 defs / +1 module:
**12,748 strict / 13,274 total / 458 modules**, zero
sorrys (on HEAD `a1d0cea`, GATE-4C's registration;
README verified in HEAD at these figures).

## BRIDGE-1

BR1-031 added by this landing (the §4 probe). No
Lean/Python interface changed.

---

## ERRATUM ADDENDUM (2026-11-04, WB-1) — §3's FACT framing is superseded

§3 above states that "the corpus's only route to
`LayerKernelPos` anywhere is from `FACT`" and that "FACT
itself is open". Both clauses are superseded as of
2026-11-04: **K-FACT-SEAT fired** (LK-P0, integrated at
main-tree commit `798c680`, census 13,441 strict / 500
modules, ledger record `lk-p0-seat-probe`) — FACT is
*refuted as stated* at the smallest seat for every β > 0,
not open; and `LayerKernelPos` has two proved supports
that do not come from FACT: at β = 0 for general (G, ρ)
(`layerKernelPos_zero`) and at the N = 2 / ZMod 2 / sign
seat for every β ≥ 0 (`layerKernelPos_seat`). §3's text
stands as written (dated record); this addendum is the
correction of record. The squeeze itself — why this probe
could not fire K-GATE-3 — is unaffected.
