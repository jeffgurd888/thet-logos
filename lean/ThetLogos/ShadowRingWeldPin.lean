import ThetLogos.BridgeMagneticCycle
import ThetLogos.BridgeCompletion

/-!
# ShadowRingWeldPin — the weld brick for the Ring Residue hypothesis

Commissioned by Zero ("weld it", 2026-11-26). Working module name only —
final naming is Zero's hand.

TIER: T5 design study made finite. NO CLAIM. Dial-ineligible: Dial 2
(derived gravity object) stays 0 under EVERY outcome of this brick,
including total success. No gravity object, no `G`, no continuum field
is constructed or fed by anything below.

## The hypothesis being welded

The Shadow line's geometry, as its own scopes state it: (1) the
interior of a region cancels in adjoint pairs — only boundary flux
survives (S-2); (2) every edge field splits into a drop (potential)
part plus a circulation part, exactly orthogonal (S-3 / V-1, the
finite 90°); (3) the shadow relations hold for EVERY weighting, so the
potential sector distinguishes nothing (S-4 / K-SHADOW-IDENTITY);
(4) a connection's gauge class is determined by its fundamental-cycle
holonomies (BridgeMagneticCycle). The Ring Residue hypothesis: what a
shadow can say about its source is carried entirely by its ring
sector — shadow data modulo the universal potential sector is
cycle-holonomy data.

## BOUNDED AUDIT (this tree, grep-verified 2026-11-26)

This lane (thet-logos-shadow1) was cut from main HEAD d348bd5 at
census 13,266 / 489 modules — BEFORE the T11 integration (census
16,431) landed the Shadow and Vortex pins in the main tree. The audit
therefore records, plainly, what is and is not in THIS tree:

(a) **S-4 universality (the Shadow line's named theorem).**
    `GravityShadowPin.lean` is NOT in this tree; it exists only in the
    main tree. The in-tree universality facts this brick actually
    consumes are: `BridgeCompletion.circulation_eq_zero` and
    `BridgeCompletion.faceFluxOf_dropVec` — for EVERY potential `Φ`,
    its circulation and its face flux vanish identically, i.e. the
    potential sector contributes zero ring-sector data, universally;
    `BridgeLaplacian.eq_const_of_energy_eq_zero` — a zero-energy
    potential is constant (the field determines the potential only up
    to constants); and this lane's own `PoissonTotalMassBlindness`
    decision (`not_exists_fieldFactor_detects_totalMass`,
    `not_exists_meanSubFactor_detects_totalMass`) — no quantity
    factoring through the Poisson output detects total mass.

(b) **Helmholtz split / gradient ⊥ circulation orthogonality.**
    NOT FOUND in this tree as a standalone theorem (grep over the
    Bridge family and the full tree). `VortexAdjointPin.lean` (V-1)
    exists only in the main tree. The factor-of-2 pairing identity
    in-tree is `BridgeLaplacian.bilin_identity` (polarized form).
    The NAIVE adjoint pairing is false under this tree's conventions
    and is never stated in this module, in any form.

(c) **Holonomy determination. FOUND.** `BridgeMagneticCycle`:
    `determination` (line 378 — gauge-equivalence ↔ equality of all
    fundamental-cycle holonomies, a full `↔`), `cycleHol_gauge`
    (line 353 — gauge invariance of `cycleHol`), `cycleHol_readings`
    (line 467 — equal holonomy tables give equal face holonomies,
    equal `magLin` spectrum, equal heat trace), `normalConn_eq_cycleHol`
    (line 322), `cycleHol_one` (line 488 — zero-field weld check).
    `BridgeMagneticFlux`: `faceHol` (line 96), `faceHol_one`
    (line 113), `faceHol_gauge` (line 160).

(d) **Exhibit seats.** The Shadow line's concrete Fin 3 / Fin 4
    exhibits live in the main-tree pins and are NOT in this tree.
    This tree's face machinery is general: `BridgeCompletion.GraphFace`
    over any `Fintype V`. The weld below is therefore stated at a
    general finite seat carrying a tree datum and a face structure —
    which is stronger than the exhibit-seat form wherever the audited
    declarations are general, and the zero-field check uses `θ ≡ 1`,
    matching `BridgeMagneticCycle.cycleHol_one`.

## THE GAP, at full rank

The full real-valued Helmholtz form of the weld — "an edge field's
shadow data modulo its gradient part equals its circulation data,
with the orthogonality of the two parts as a theorem" — is NOT proved
in this brick, because its orthogonality half (V-1) does not exist in
this tree. What IS proved below:

(i)  the potential sector is ring-blind, universally
     (`potential_sector_ring_blind`): every potential's circulation
     around every face is zero;
(ii) in the connection dialect, ALL ring-sector readings of a
     connection — its face-holonomy table, its magnetic spectrum,
     its heat trace — are functions of its fundamental-cycle
     holonomy table alone (`ring_data_eq_of_cycleHol_eq`,
     `shadow_data_factors_through_cycleHol`), and that table is a
     complete invariant of the gauge class (`determination`, cited,
     with the forward direction restated as `cycleHol_eq_of_gaugeConn`).

The weld is the package (i) + (ii) at one seat. K-SHADOW-RING stays
armed exactly as pre-registered: one potential-sector quantity that
distinguishes two configurations with identical ring data kills the
hypothesis; nothing below claims otherwise.

## Fences

- No gravity object, no `G`, no Einstein slot, no continuum limit.
- The corrected pairing only; the naive pairing is never stated.
- Dial 2 stays 0; this brick is fence/bookkeeping about the shadow,
  not an object.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ring-sector shadow data of a connection, as this brick uses
the term: its table of face holonomies — one `Circle` value per face,
the multiplicative circulation data of the connection.
(Noncomputable because `faceHol` is.) -/
noncomputable def faceHolTable {F : Type*} (bd : F → GraphFace V)
    (θ : V → V → Circle) : F → Circle :=
  fun f => faceHol bd θ f

/-- **The potential sector is ring-blind, universally.** For EVERY
potential `Φ` whatsoever and every face `f`, the circulation of `Φ`
around `f` is zero: potential drops telescope around the closed
boundary loop. This is the in-tree universality half of the weld
(`BridgeCompletion.circulation_eq_zero`, the discrete Stokes identity
for potentials) — the potential sector contributes no ring-sector
data, for any weighting, which is exactly why it can distinguish
nothing. -/
theorem potential_sector_ring_blind {F : Type*} (bd : F → GraphFace V)
    (Φ : V → ℝ) (f : F) : circulation bd f Φ = 0 :=
  circulation_eq_zero bd f Φ

/-- **Forward direction of determination, restated.** Gauge-equivalent
connections have identical fundamental-cycle holonomy tables: the
endpoint factors of the gauge telescope away around the closed walk.
Cites `BridgeMagneticCycle.cycleHol_gauge`. -/
theorem cycleHol_eq_of_gaugeConn (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (h : V → Circle) (θ : V → V → Circle) (i j : V) :
    cycleHol par depth θ i j
      = cycleHol par depth (gaugeConn h θ) i j :=
  (cycleHol_gauge r par depth hdepth_r hstep h θ i j).symm

/-- **Ring data is a function of the holonomy table.** Two connections
with equal fundamental-cycle holonomy tables have equal face-holonomy
tables — equal ring-sector shadow data. Proved through
`BridgeMagneticCycle.cycleHol_readings`, whose first component is
exactly this equality face by face. -/
theorem ring_data_eq_of_cycleHol_eq {F : Type*} (bd : F → GraphFace V)
    (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (θ₁ θ₂ : V → V → Circle)
    (h : ∀ i j, cycleHol par depth θ₁ i j
      = cycleHol par depth θ₂ i j) :
    faceHolTable bd θ₁ = faceHolTable bd θ₂ := by
  funext f
  exact (cycleHol_readings bd r par depth hdepth_r hstep
    (fun _ _ => 0) θ₁ θ₂ h f 0 0).1.symm

/-- **Zero-field weld check.** At the trivial connection `θ ≡ 1` —
the zero field — both tables are trivial: every fundamental-cycle
holonomy is `1` (`BridgeMagneticCycle.cycleHol_one`) and every face
holonomy is `1` (`BridgeMagneticFlux.faceHol_one`). The weld
specializes to the exhibit's vanishing shadow, as it must. -/
theorem zero_field_tables_trivial {F : Type*} (bd : F → GraphFace V)
    (par : V → V) (depth : V → ℕ) :
    (∀ i j, cycleHol par depth (1 : V → V → Circle) i j = 1)
      ∧ faceHolTable bd (1 : V → V → Circle) = fun _ => 1 :=
  ⟨fun i j => cycleHol_one par depth i j,
   funext fun f => faceHol_one bd f⟩

/-- **THE WELD (headline).** At a finite seat carrying a tree datum
and a face structure, let `θ₁ θ₂` be two connections whose
fundamental-cycle holonomy tables agree. Then every ring-sector
reading of the two connections agrees — face-holonomy table,
magnetic spectrum, heat trace at every time — while the potential
sector contributes zero ring-sector data for every potential `Φ`
and every face `f`. In one package: the shadow data that can
distinguish the two configurations is exhausted by the cycle-holonomy
table (which `BridgeMagneticCycle.determination` proves is a
complete invariant of the gauge class), and the universal potential
sector is silent on the ring. Proved by assembling
`BridgeMagneticCycle.cycleHol_readings` (the readings are functions
of the table) with `BridgeCompletion.circulation_eq_zero` (the
potential sector's universal blindness). NO CLAIM beyond this finite
statement; no gravity object is named or implied. -/
theorem shadow_data_factors_through_cycleHol {F : Type*}
    (bd : F → GraphFace V)
    (r : V) (par : V → V) (depth : V → ℕ)
    (hdepth_r : depth r = 0)
    (hstep : ∀ v : V, v ≠ r → depth (par v) + 1 = depth v)
    (w : V → V → ℝ) (θ₁ θ₂ : V → V → Circle)
    (h : ∀ i j, cycleHol par depth θ₁ i j
      = cycleHol par depth θ₂ i j)
    (Φ : V → ℝ) (f : F) (μ : ℂ) (t : ℝ) :
    faceHolTable bd θ₁ = faceHolTable bd θ₂
      ∧ (Module.End.HasEigenvalue (magLin w θ₁) μ
          ↔ Module.End.HasEigenvalue (magLin w θ₂) μ)
      ∧ magHeatTrace w θ₁ t = magHeatTrace w θ₂ t
      ∧ circulation bd f Φ = 0 :=
  ⟨ring_data_eq_of_cycleHol_eq bd r par depth hdepth_r hstep θ₁ θ₂ h,
   (cycleHol_readings bd r par depth hdepth_r hstep w θ₁ θ₂ h f μ t).2.1.symm,
   (cycleHol_readings bd r par depth hdepth_r hstep w θ₁ θ₂ h f μ t).2.2.symm,
   circulation_eq_zero bd f Φ⟩

end ThetLogos
