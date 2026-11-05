# LK-P0 — Fused Seat Probe: Landing Dossier (2026-11-04)

Brick LK-P0, LayerKernelPos front (fire-all front 1 of 5). Contract:
`layerkernelpos-attack-scoping-2026-11-04.md`. Module:
`lean/ThetLogos/LayerKernelPosSeatProbe.lean` (worktree
`~/workspace/thet-logos-lkp0`, branch `lk-p0-lane`, final commit
`55e5bad`). **39 strict** (`theorem`/`lemma` at column 0), zero sorry,
no `native_decide`, warning-clean; `#print axioms` on every headline
returns exactly {propext, Classical.choice, Quot.sound}.

## The seat (stated on the face, per contract)

- N = 2; gauge group G = Multiplicative (ZMod 2); d = 1; ρ = the sign
  representation (seatMat 1×1, entry `seatSign g = if toAdd g = 0 then
  1 else -1`); μ = seatμ = (2 : ℝ≥0∞)⁻¹ • Measure.count on G, a
  probability measure, left/right invariant (instances hand-proved).
- Geometry: LayerSite 2 has **8 sites**; LayerColumn 2 has **24
  columns** (8 sites × 3 nonzero directions, directions are Fin 4);
  stratum configurations 2^8 = **256**; layer configurations 2^24
  are never enumerated — the pairing is manipulated symbolically via
  a closed form. The configuration-space stop-line was NOT breached.

## Verdict 1 — β = 0: PROVED, at general (G, ρ)

`layerKernelPos_zero`: **LayerKernelPos holds at β = 0 for every
group G, representation, and invariant measure the corpus definitions
admit.** The scoping's UNVERIFIED flag is resolved: no β = 0
LayerKernelPos existed in the tree before this brick; the corpus's
`layerKernel_zero` (kernel ≡ 1 at β = 0, in
Span3SeatSchurGateProbe) supplies the kernel, and the pairing then
separates as conj(∫F) · (∫F), whose real part is ‖∫F‖² ≥ 0. Gauge
invariance is not consumed.

## Verdict 2 — FACT at the seat: FALSE for every β > 0 — K-FACT-SEAT FIRES

`seat_not_stratumColumnFactorization {β : ℝ} (hβ : 0 < β) :
¬ StratumColumnFactorization (N := 2) seatμ seatρ β`.

Engine: with dens_P ∈ {0, 2}, writing a(β) = (1 + e^{−2β})/2 and
b(β) = (1 − e^{−2β})/2, one has exp(−β·dens) = a + b·χ(word), and the
stratum average is a parity filter (a family character averages to 1
iff every site has even column multiplicity, else 0). This gives the
closed form (`layerKernel_seat`): the kernel is the sum over even
column families S of a^{24−|S|} b^{|S|} · configProd S u · configProd
S u'.

Exact values at the diagonal test configuration (u = u' = 1):

- FACT side: zPolymer = **a(β)^24** (`seat_zPolymer`; every single
  column integral is `seat_colZ` = a(β), the odd singleton family
  averaging to 0).
- Kernel side: K(1, 1) = ∑_{S even} a^{24−|S|} b^{|S|}
  **≥ a(β)^24 + a(β)^22 · b(β)^2 > a(β)^24** for every β > 0.

The excess term is one certified summand: the even **reverse pair**
{seatCol0, seatCol0'} — the two columns over the same site with
swapped base/shift (at N = 2 the shift is an involution, σ² = id, so
the pair has every site multiplicity even: (A+B) + (B+A) = 2(A+B)).
FACT equates the two sides; they differ by a strictly positive
amount for every β > 0. One certified kernel-value mismatch kills
FACT **generally**, per the contract: the FACT route to
LayerKernelPos is dead at every seat, not just this one. At β = 0
FACT holds at the seat (both sides are 1), consistent with Verdict 1.

**Per the contract, the FACT side stops here. LayerKernelPos
survives for other routes** — see Verdict 3.

## Verdict 3 — PSD at the seat: TRUE for every β ≥ 0 — K-LKP-SEAT does NOT fire

`layerKernelPos_seat {β : ℝ} (hβ : 0 ≤ β) :
LayerKernelPos (N := 2) seatμ seatρ β`.

Proof shape: at the seat the double integral is a finite double sum;
substituting the closed form and swapping sums exhibits the pairing
as a positive scalar multiple of **∑_{S even} w_S · ‖Z_S‖²**, where
w_S = a^{24−|S|} b^{|S|} ≥ 0 for β ≥ 0 and Z_S = ∑_u configProd S u ·
F u is the S-th Gram vector. A sum of nonnegative terms: the pairing
is nonnegative for every test observable F (gauge invariance again
not consumed). β < 0 at the seat is left undecided (b(β) < 0 there;
no verdict either way is claimed).

## Honesty paragraph

A seat decision is a seat decision: it kills generally if negative,
but a positive seat result is evidence at ONE seat, not the general
statement. Accordingly: FACT is dead generally (Verdict 2 is a
negative decision, and one mismatch suffices). LayerKernelPos itself
remains **open in general** — Verdict 3 proves it at this single
smallest seat only, and Verdict 1 proves it at β = 0 only; neither is
the general statement at β > 0, and no other route (LOC-3 / α-wall)
is touched by this brick. **NO CLAIM; dials 0/4.** A general
discharge of LayerKernelPos would move no dial.

## Deviation (declared, not widened silently)

The brick landed at **39 strict against the contracted band of
8–18**. The overage is the seat infrastructure the three decisions
share (seat measure and its invariance instances, the sign-rep
algebra, the parity-filter engine, the closed form, and the two
decision proofs); no decision was weakened to fit the band, and the
contract's actual stop-line — the seat's configuration space — was
honored throughout (256 stratum configurations; 2^24 layer
configurations handled symbolically, never enumerated).

## Addendum (2026-11-04) — integration hygiene: explicit seat-instance names

The first integration attempt stopped at the axiom-fence step on a
PRE-EXISTING corpus landmine of the duplicate-name class (the same
class as the `ThetLogos.Config` double definition resolved by hygiene
commit 296e935): this module's four anonymous seat instances on
`Multiplicative (ZMod 2)` — `TopologicalSpace := ⊥`,
`MeasurableSpace := ⊤`, `DiscreteTopology`, `BorelSpace`
(LayerKernelPosSeatProbe.lean:119–129) — were declared identically in
LatticeBlockingFlow.lean:89–96, generating identical auto-names
(`ThetLogos.instTopologicalSpaceMultiplicativeZModOfNatNat_thetLogos`,
`...instMeasurableSpace...`, `...instDiscreteTopology...`,
`...instBorelSpace...`; verified by `#synth` against the
LatticeBlockingFlow environment), so the two modules were
un-co-importable in either order. LatticeBlockingFlow is already in
the fence's environment (via the registered BlockedKernelDiagNotOne
lineage), so admitting this module would have errored the whole fence
check file for all declarations — and CI runs the same runner, so the
push would have turned CI red corpus-wide. The fence append was
reverted and nothing was committed or pushed from that attempt.

Resolution, on this module's side only (integrated files untouched):
the four instances received explicit seat-probe-specific names —
`seatInstTopologicalSpace`, `seatInstMeasurableSpace`,
`seatInstDiscreteTopology`, `seatInstBorelSpace` (collision scan of
`seatInst` against the whole main tree: zero hits). DECLARED
DEVIATION: the integrated module text differs from the landing commit
(55e5bad; dossier commit bb38cf6) by exactly these four instance-name
tokens — no statement, proof, or other text changed, and the three
verdicts above are unchanged. After the rename: targeted module build
green (3647 jobs, module warning-clean); all 39 headlines re-verified
by `#print axioms` on exactly {propext, Classical.choice, Quot.sound},
no sorryAx; and a scratch file importing BOTH
LayerKernelPosSeatProbe and LatticeBlockingFlow compiles — the
landmine is defused by construction, not by assumption.
