# Phase 5 — Electroweak Sector Mapping: the SELECTION theorem

*2026-10-02. Tier T4 numerical. LOCAL — not pushed. Parent: E13-D.*
*Code: `python/thet_logos/e13d_ew_selection.py` (seeded, exit 0).*

## Circularity firewall (binding)

The value 228.8 GeV = 0.93 × 246.0 is **input**: `Y_PHYS["Yu"] = 0.93`
and `VEV = 246.0` in `python/thet_logos/finite_thermal_flow.py`.
Nothing in this document predicts, derives, or "explains" the top mass.
What is proved/witnessed here is **selection**: the Connes distance
functional structurally locks onto the heaviest-Yukawa block of D_F,
i.e. d(C,H)⁻¹ = max(Y)·VEV, regardless of which position holds the
maximum and regardless of its value. Any reading beyond selection is
forbidden.

## P_EW — the electroweak sector projector

On H_F = ℂ³², with the E13-D probe embedding π_full:

```
P_EW = diag(0₁₆, I₈, 0₈)      (probe dims 16..23: u1·I₄ ⊕ I₂⊗q)
```

Verified: idempotent, Hermitian. Algebraic characterization: the
element z = (1, I₂, 0₃) ∈ A_F is central, and

```
π_full(z) = Q_top + P_EW + Q_tail
```

verified numerically, where Q_top projects onto dims {0,1,8,9}
(Option-A electroweak support) and Q_tail = diag(0₃₀, I₂) (probe
trailing u1 block, dims 30..31). Hence P_EW is exactly the
electroweak-summand part of the central element's image in the probe
sector. Ran(P_EW) is the joint support of the C and all 12 H pure
states (verified). The M₃ blocks (dims 24..29) are projected out.

## Selection theorem (T4, numerically witnessed)

**Statement.** For the C–H pure-state pair, d(C,H)⁻¹ = max(Y)·VEV,
where the maximum is over the four Yukawa inputs. The value is
inherited from input; the *selection of the maximum* is structural.

**Evidence.** Eight Yukawa configurations; C–H distance recomputed from
scratch each time (D_F rebuilt, E13-D solver re-run, 3 H-samples each):

| configuration      | max(Y)·VEV (GeV) | 1/d(C,H) (GeV)              | rel. err |
|--------------------|------------------|-----------------------------|----------|
| baseline Y_PHYS    | 228.780          | 228.7800 (×3 samples)       | 0.00%    |
| democratic (0.3)   | 73.800           | 73.8000                     | 0.00%    |
| max moved to Ye    | 228.780          | 228.7800                    | 0.00%    |
| max moved to Ynu   | 228.780          | 228.7800                    | 0.00%    |
| max lowered (0.05) | 12.300           | 12.3000                     | 0.00%    |
| max moved to Yd    | 123.000          | 123.0000                    | 0.00%    |
| KO: max-only       | 228.780          | 228.7800                    | 0.00%    |
| KO: max removed    | 5.904            | 5.9040                      | 0.00%    |

All H-samples uniform to <1% within each config. The knockouts pin the
mechanism: the max-Yukawa block alone suffices (KO max-only unchanged),
and removing it moves the scale to the next-heaviest (KO max-removed →
5.904 = Yd·VEV). If the distance had not tracked, the selection
hypothesis would have been reported FAILED per spec — it did not fail.

**Mechanism diagnostic.** For the maximizing A* at baseline, the
dominant entries of the [D_F, A*] Yukawa-coupling block (24..32, 16..24):
99.1% of the top-8 entry weight involves the max-Yukawa positions
{2,4,6}; the single largest entry is pure max-Yukawa (228.78, 228.78).
The Lipschitz constraint binds on the heaviest block.

**Baseline refutation of positionality.** The C state sits at dim 16,
whose own D_F coupling is Ynu = 0 in Y_PHYS — yet 1/d = 228.8, not ∞.
The selection is global (max over all Yukawa positions), not local to
the states' own coupling. The max@Ynu / max@Ye shuffles confirm:
moving the maximum to another position does not change the selected
scale.

## Analytic core (proved) vs open

Proved: P_EW construction and the π_full(z) decomposition; Ran(P_EW)
support lemma; D_F block structure (‖D_F‖ = max|Y|·VEV;
D_F maps Ran(P_EW) into the Yukawa blocks via B = conj(A)); the
positionality refutation above.

Open: the exactness (0.00% in all 8 configs) is consistent with an
exact analytic identity d(C,H) = 1/(max(Y)·VEV), but the closed-form
proof is not given here — natural Phase-3 target. Status: **selection
theorem numerically witnessed (T4)**; analytic proof open.

## Frozen boundary (explicit)

The spectral-action half of the original Phase 5 is **frozen** per the
ledger (SA-4): no effective-action derivation, no Higgs-doublet
construction, no GR linkage is attempted or claimed here.
"Electroweak" in the title refers strictly to the C⊕H summand sector
of the finite algebra. The quarantine wall holds: no continuum, no
d_spec→4, no clock-time, no Lorentzian/GR, no experimental prediction —
verified by output scan in the script.

## Status

SELECTION-CONFIRMED (8/8 configs, knockouts included). Kill condition
(distance fails to track max(Y)·VEV) not triggered. The finite Connes
distance functionally reads off the heaviest Yukawa scale — a structural
property of the (D_F, P_EW) pair, with the scale's numerical value
honestly attributed to input.
