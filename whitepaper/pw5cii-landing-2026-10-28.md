# PW-5c-ii — the Endpoint: Φ ≥ 0, and the β⁴ Diagonal Sign

*Landing dossier, 2026-10-28. Module:
`lean/ThetLogos/PhiAssembly.lean`, final section
§EndpointAssembly appended (section strict 8;
module total strict 56, defs 18; zero placeholders,
zero `native_decide`; main-tree build green, 3,558
jobs, parent-verified — the parent re-checked the
axiom sets of both endpoint theorems directly:
exactly `[propext, Classical.choice, Quot.sound]`).
**Parts of the Clay Yang–Mills statement closed by
this landing: 0.** What closes here is a question
this program posed to itself: the sign of the
dependent part of the β⁴ coefficient on the
diagonal. It is nonnegative — a theorem, at the
scope stated, with the fences stated. NO CLAIM on
anything beyond it; dials 0/4.*

## The endpoint, as scoped and as landed

At (hN : Even N), (hN3 : 3 ≤ N), continuous ρ,
**RepIrreducible ρ**:

- `phi_diag_nonneg : 0 ≤ phiFunctional ρ μG u`
- `kappa4dep_diag_nonneg : 0 ≤ kappa4dep ρ μG u u`

**No hypothesis drift**: the statements are the
scoping's, hypothesis for hypothesis. The case split
resolved internally: 2 ≤ d and d = 1 nontrivial go
through e1 = 0 (§5a) plus per-moment nonnegativity
(§PatternEvaluation: every Re M_t = d⁻¹⁴·‖RN‖²);
d = 1 trivial goes through a bridge (character
identically 1 ⇒ representation identically 1) into
§5a's trivial pack, summand 1 − 1⁴ = 0; d = 0 through
a vanishing pack, summand 0. Every primitive quad
contributes a nonnegative summand; the sum is the
theorem.

## What this is, in the program

κ₄^dep is the β⁴ coefficient of the layer kernel
𝒜's small-β expansion on the diagonal — the first
order at which the coefficients stop being constant
(the β2 core finding: 𝒜's coefficients are constant
through β³, first dependence at β⁴). Its sign was
the β2 core's named open component after the closed
form landed: reduced by PW-2 to Φ, obstructed there
by the ρ ⊗ ρ twirl (evaluated by PW-3) and by the
pattern landscape (corrected by PQ-0: at the
assembly's N there are only 4-cycles), and closed
here through a uniform row/column network
separation stronger than the case analysis that was
priced for it. The chain, for the record: probe
(two seats, margins zero) → closed form at general
(G, ρ) → PW-1 mixed twirl → PW-2 reduction →
PW-3 same-orientation twirl → PQ-0 pattern
correction → PW-5a interface → PW-5b engine →
PW-5c-i pairing/evaluation → this endpoint.

## What this is not

- **Not 𝒜 ⪰ 0.** One coefficient, on the diagonal,
  at one order. The off-diagonal form Φ(u, u′) is
  untouched; β⁵ and beyond are untouched — and the
  β2-core scoping's warning stands unamended: at
  every computed order the dependent form has margin
  exactly zero in most directions, so order-5 or
  order-6 negativity at some seat remains a live
  possibility that this theorem does not speak to.
- **Not a gap, not a continuum statement, not a
  Millennium part.** The endpoint is finite-volume
  algebra at fixed N and fixed irreducible ρ. N = 2
  remains open (all four patterns live there). No
  cushion: Φ is not bounded away from 0.
- Dials: 0/4, unchanged. The four events that would
  move the ToE odds are untouched by this landing.

Census effect: 7,005 → **7,013 strict** /
7,083 → **7,091 attribute-inclusive** / modules
unchanged at **239**; the seven quarantined
placeholders are unchanged. (A builder-side count
note: one sub-brick handoff quoted a file total of
55 from an inconsistent method; the parent's count
governs — module strict 56 = 48 + 8 — and the delta
method agrees at every step.)

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
