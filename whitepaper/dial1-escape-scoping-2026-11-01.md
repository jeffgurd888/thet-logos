# DIAL-1 ESCAPE SCOPING — 2026-11-01

*Scoping only: nothing built, nothing proved, no code touched, no
entry fired. Authorized by Jeff 2026-11-01 as PREPARATION ONLY.
This dossier lands for a decision in chat; it does not commission
anything. **Parts of any official statement closed by this pass:
0. Dial 1 stays 0. All dials: 0/4. NO CLAIM.***

*Tier key: T1 = machine-checked in the landed tree (cited, not
re-proved here). T2 = definitions, statement shapes, and scoping
arithmetic performed in this pass on landed data (reproducible,
not Lean-checked). Every number below that is not cited to a
landed theorem is T2 scoping arithmetic and is labelled as such.*

---

## 0. Headline verdicts, per family

| # | Family | Verdict at scoping |
|---|--------|--------------------|
| 1 | Anomaly cancellation | **SURVIVES as a condition** (π₁ holds, piFlip fails 3 of 4 equations — T2 arithmetic on T1 weights). **Cannot force alone**: its solution cone has a continuous B−L direction and a degenerate branch (§2.4). Statement price is dominated by a weight-extraction gap (M–L). |
| 2 | Second-order / junk conditions | **UNRESOLVED, ranked last of the live three.** Statable (S–M to pin), but the π₁-holds pre-check is genuinely in doubt for junk-vanishing (prior: π₁ FAILS — in CCM the junk is quotiented, not zero), and the order-two variants are invented conditions, discounted as such. Pre-checks M. |
| 3 | Linear seat functionals (γ_F-trace on raw π) | **SURVIVOR, ranked #1.** Escapes `lifted_diag_partner` by two independent features: first power of π (not the lifted product) and a partner-ODD weight (γ_F). π₁ holds (coeffs (0,0)), piFlip fails (α-coeff +2) — T2 arithmetic on T1 tables. Cheapest honest entry in this audit: **S–M, pin + both pre-checks**, explicitly NOT a forcing attempt (§4.5). |
| 4 | D_F kernel/image intertwining | **KILLED AT SCOPING, full rank (K-ESC-1).** Both horns fail: at generic Yukawas the data is vacuous (ker = 0, im = ⊤, piFlip passes); at special Yukawas the kernel splitting is finer than π₁'s own doublet mixing (π₁ itself fails). The only D_F decompositions π₁ preserves are the four coarse blocks already in the base set — and piFlip preserves those too. |
| 5 | Further families found | Two subfamilies **KILLED AT SCOPING** (γ-inserted lifted traces, K-ESC-7; raw J-intertwining at RH seats, K-ESC-8). The rest are re-exports of Families 1/3, standing kills, or parked at L with named gaps (§6). |

**No global no-go.** The partner symmetry's reach is wide but
exactly characterizable (§1.2), and Families 1 and 3 both step
outside it. What no surviving family does — stated now, at the
top, so it cannot be misread later — is *force the ratios by
itself*. Family 3 is one linear equation; Family 1 is a cone with
a free direction. Either would be a *clause* of a future
strengthened set, not a forcing theorem. Dial 1: **0/4**.

---

## 1. The symmetry, and exactly how far it reaches

### 1.1 The landed fact (T1)

`lifted_diag_partner` (`DialOneSeatTieChecks.lean`, T1): for
EVERY matrix `M` and seat `s`,

```
(M * piOp M) s s = (M * piOp M) (partner s) (partner s)
```

by partner-reindexing of the sum and commutativity of each
product. Consequences already landed (T1): `SeatTie π` holds for
every π (`seatTie_universal`); piFlip satisfies the D1-A′
strengthened set; `¬ DialOneForcing` (`kD1A1_fires_by_piFlip`);
the vacuity prong is a theorem (`kD1A2_vacuity_reading`).

Vocabulary used throughout (all landed): `partner` and `gammaF`
and `UJ` (`Scaffold32.lean`, T2 defs / T1 identities, incl.
`gammaF_partner_flip : gammaF (partner i) (partner i) =
-gammaF i i`); `pi1`, `W`, `pi1AVal`, `pi1BVal`, `u1ParamGen`
(`Track1RouteB.lean`); `piFlip`, `piFlip_unimodular_direction`,
`piFlip_lifted_nuR` (`HyperchargeForcing.lean`); `DF_oneGen
(Ynu Ye Yu Yd : ℝ)` (`FiniteSpectralTriple.lean`, Yukawas
universally quantified in every condition-set use); `DialOneBase`
(`DialOneSeatTiePin.lean`). piFlip's lifted sector weights along
its own unimodular direction `(−2, 1)` are (T1, module header +
the pattern arithmetic of §2.3 below):

```
x(piFlip) = (nuL 2, eL 2, uL −1, dL −1, nuR 4, eR 4, uR −3, dR 1)
x(pi1)    = (−3, −3, 1, 1, 0, −6, 4, −2)        (= 3·Y_f)
```

### 1.2 The symmetry's reach (scoping lemma, proof-shaped, T2)

The reindexing argument generalizes to a precise fence. A
condition C(π) is **inside the symmetry's reach** — hence dead
or vacuous before any pre-check — if its content factors through
any of:

- **(R1) Partner-even functionals of the lifted diagonal.**
  Any per-seat comparison, or partner-even weighted sum, of the
  entries `(π * piOp π) s s`. This is D1-A′'s grave (T1 above).
- **(R2) Partner-odd weightings of the lifted diagonal.**
  These are not merely undiscriminating, they are *identically
  zero*: for any diagonal weight `c` with `c (partner s) =
  −c s` (γ_F is the landed instance), `∑ s, c s · (M * piOp M)
  s s = 0` for every `M`, by pairing `s` with `partner s` and
  using T1 `lifted_diag_partner` + `gammaF_partner_flip`. With
  the base set's order-zero clause the same pairing kills
  γ-weighted traces of lifted *products* `π a * piOp (π b)`
  (reindex, commute by order-zero, pair, cancel). So γ_F must
  multiply π to the **first power only** — see Family 3, and
  the kill K-ESC-7 in §6.
- **(R3) Support / kernel / image / spectral-subspace data of
  the landed D_F class.** See Family 4's kill (§5): the data is
  either vacuous or already in the base set, on both horns.

A condition **escapes** only if it uses at least one of:

- **(E1)** π to the first power, weighted by a partner-odd
  operator (γ_F), so a single seat's conjugation flip is seen
  with no partner compensation — Family 3.
- **(E2)** A global polynomial in the *sector* lifted weights
  whose coefficients attach to sectors/chirality/multiplicity —
  not to seat-vs-partner pairs — so the functional is a function
  on the 8-vector `x(π)` that is not invariant under moving one
  coordinate of `x` — Family 1.
- **(E3)** Full-matrix (off-diagonal) expressions in `π`, `piOp
  π`, and `DF_oneGen` that are not diagonal entries of a lifted
  product — Family 2 (junk / second-order commutators).

This trichotomy is the scoping-level answer to task item 5's
"wider reach" alternative: the reach *is* wider than D1-A′'s
single clause (R2 and R3 are new graves, both used below), and
it is *not* total (E1–E3 are outside it, with pre-checks priced).

---

## 2. Family 1 — Anomaly cancellation

### 2.1 The physics (T4 literature shape, stated for the audit)

For one generation with the seated content (left doublets
`(ν_L,e_L)`, `(u_L,d_L)×3 colours`; right singlets `ν_R, e_R,
u_R×3, d_R×3`), anomaly cancellation is the vanishing of four
coefficients, here written directly in the eight **sector lifted
weights** `x_f` of a candidate π (along π's unimodular
direction; all four are homogeneous, so the overall scale of
`x` is irrelevant — no value is named by any of them):

```
A3  (SU(3)²U(1)) : (x_uL + x_dL) − x_uR − x_dR                       = 0
A2  (SU(2)²U(1)) : (x_nuL + x_eL) + 3·(x_uL + x_dL)                 = 0
Agrav (grav-U(1)) : (x_nuL + x_eL) + 3·(x_uL + x_dL)
                    − (x_nuR + x_eR) − 3·(x_uR + x_dR)              = 0
A111 (U(1)³)     : (x_nuL³ + x_eL³) + 3·(x_uL³ + x_dL³)
                    − (x_nuR³ + x_eR³) − 3·(x_uR³ + x_dR³)          = 0
```

Derivation of the sector form (T2): sum over left-handed Weyl
fermions — particle L seats with multiplicity (colour 3 for
quarks, 1 for leptons) plus the conjugates of the R seats with
weight `−x_R` — which is why the right-handed seats enter **as
themselves, with a chirality sign**, never routed through a
partner-seat equality. That is exactly escape route E2. The
multiplicities (3, 1) and the doublet groupings are the seated
sector decomposition (`SMFermions.fermionIndex`, `colorRep` —
T2 structural input, the same standing conditional the whole
Dial-1 line already carries), not weight values. The Witten
SU(2) global anomaly (even doublet count: 3 + 1 = 4) is
weight-free and piFlip-invariant; it discriminates nothing and
is not part of C.

**Corpus status: ABSENT, as previously receipted.** The
2026-10-27 scoping (§2, A4) and `BRSTFinite.lean`'s own header
(T1-adjacent, on its face): "The anomaly side is absent, named…
vanishing is not anomaly cancellation." There is no anomaly
object, trace, or theorem in the tree to reuse. Everything in
this family is new vocabulary.

### 2.2 Statability

Two statement shapes, honestly distinguished:

- **Shape A (sector-weight polynomial).** C(π) := for every
  primitive unimodular direction `(α, β)` of π, the four
  polynomials above vanish on `x(π, α, β)`. This presupposes a
  π-general **weight extraction**: a landed definition of the
  sector weight `x_f(π, α, β)` for an arbitrary base-set π.
  The corpus owns weights only for the two constructed
  representations (π₁'s `W`/`pi1AVal`/`pi1BVal`; piFlip's pattern
  via its det/diag lemmas). For a general π, the only landed
  π-general weight notion is the lifted eigenvalue
  `(π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))) s s`
  itself — a complex number, not an integer weight; that it is
  a pure character `exp(i·x·t)` with `x` constant across each
  sector's seats (colour copies included) is **not landed and
  not implied by anything cited in the base set** (the base
  clauses do not obviously force `π (u1ParamGen α β t)` to be
  seat-diagonal). **This is the family's main vocabulary gap.**
  Price to close it: **L** (a diagonality/character lemma for
  the base set, or an extraction definition via the generator
  of §4.2 plus a sector-constancy lemma — either is a real
  brick, and either might *fail*, which would itself be a
  finding: the base set may admit non-diagonal π for which
  "the weights" do not exist, in which case Shape A is not a
  condition on the base set at all).
- **Shape B (trace form).** The anomaly coefficients as traces
  over `H_F` of products of `π` applied to fixed AF Lie-algebra
  elements (the U(1) generator of §4.2; ℍ- and M₃-summand
  generators for the SU(2)/SU(3) factors), weighted by γ_F /
  sector data. Statable with the same one new definition as
  Family 3 plus trace functionals (Mathlib `Matrix.trace`).
  **Audit flag:** that Shape B's traces *equal* the sector
  polynomials of Shape A is a theorem that would have to be
  proved per-representation (it is a computation for π₁ and for
  piFlip, not a formality); an unproved Shape B is a different
  condition wearing anomaly's name — registered as K-ESC-2(c).

### 2.3 Pre-checks (T2 arithmetic on the T1 weight tables of §1.1)

**π₁: HOLDS, all four.** On `x(π₁) = (−3,−3,1,1,0,−6,4,−2)`:
A3 `= 2 − 4 + 2 = 0`; A2 `= −6 + 6 = 0`; Agrav `= −6 + 6 + 6 −
6 = 0`; A111 `= −54 + 6 + 216 − 168 = 0`. (This is the familiar
fact that the SM table is anomaly-free, re-derived here in the
corpus's lifted normalization `3Y`.)

**piFlip: FAILS, three of four.** On `x(piFlip) =
(2,2,−1,−1,4,4,−3,1)`: A3 `= −2 + 3 − 1 = 0` — **passes**;
A2 `= 4 − 6 = −2 ≠ 0`; Agrav `= 4 − 6 − 8 + 6 = −4 ≠ 0`;
A111 `= 16 − 6 − 128 + 78 = −40 ≠ 0`. Hence C must be the
**conjunction**; the SU(3)²U(1) equation alone does not
discriminate (registered as K-ESC-3, fired at scoping against
that subfamily). In-tree price of the formal pre-checks, once
Shape A or B is pinned: π₁ **S** (its pattern is T1, the rest
is `decide`/`norm_num` over 8 sectors); piFlip **S–M** (its
ν_R lifted entry and determinant are T1, but a full 8-sector
lifted pattern for piFlip is stated in the module header, not
landed as one theorem — assembling it is the M part).

### 2.4 The solution set's shape — why anomaly cannot force alone

Solve the system in doublet variables `(Q, L, U, D, E, N)`
(T2 algebra, this pass). The three linear equations give
`L = −3Q`, `U + D = 2Q`, `E + N = −6Q`. Writing `U = Q + t`,
`D = Q − t`, `E = −3Q + s`, `N = −3Q − s`, the cubic reduces to

```
A111  =  18 · Q · (s − t) · (s + t)  =  0.
```

So the solution cone (projectively, `Q ≠ 0`) is **two
one-parameter branches** `s = ±t`, plus a **degenerate branch**
`Q = 0` (then `L = 0`, `U + D = 0`, `E + N = 0`, cubic automatic
— a further projective line of exotic assignments). The SM
point is `Q=1, t=3, s=−3` on the `s = −t` branch. The free
parameter along a branch is the textbook fact: with a ν_R seat
present, `B−L` is itself anomaly-free, so `Y + ε·(B−L)` cancels
for every ε — anomaly cancellation alone has a **continuous**
family of solutions and does not determine the ratios. (If the
ν_R seat were *removed*, the same computation gives
`t = ±3Q`: the discrete u_R↔d_R swap ambiguity instead. The
corpus seats ν_R, so the continuous version is the one that
applies.) Consequence, at full rank: **any future entry whose
condition set is base + anomaly alone has its forcing statement
FALSE at the physics level**, before any Lean question arises —
unless the B−L direction is not realizable by base-set
representations, which is itself an unproved classification
question (the realizable weight patterns of base-set π may be
discrete — piFlip's was — in which case anomaly + discreteness
could in principle isolate the table; scoping cannot price
that hope above a hope). Registered as K-ESC-2(a).

### 2.5 Circularity / fence audit

(c) **Passes.** No weight value, no `hypercharge`, no Y_f
upstream; the equations are homogeneous polynomials *in* a
candidate's weights; Yukawas never appear. (d) **Passes under
the house's operational reading, flagged.** K-D1A′-2's test was:
over the base set, the clause is equivalent to *fixing a seat's
weight directly*. The anomaly system fixes no seat (its zero
set is a cone of dimension ≥ 2 in weight space, §2.4). Under a
stricter reading — "any condition whose content is a system of
equations in the weights is a weight equation" — this family
would die by the fence; that reading would also have banned
the task's own candidate #1 in advance, so the operational
reading is used and the ambiguity is put on the face for
Jeff's decision. What the family does *not* survive is any
claim to be a forcing proof (§2.4).

**Kill registrations (Family 1):**
- **K-ESC-2(a) (forcing-by-anomaly-alone).** Any entry claiming
  base + anomaly forces the ratios dies on the §2.4 cone
  (B−L direction / degenerate branch), unless it first proves
  the B−L-mixed patterns are not realizable over the base set.
- **K-ESC-2(b) (counterexample).** Any π′ in base + anomaly
  with weights not proportional to the table kills that entry
  (standard relabeling-rule form).
- **K-ESC-2(c) (costume).** A Shape-B trace condition shipped
  as "anomaly cancellation" without the proved identification
  with the §2.1 polynomials is a fit in costume: kill on sight.
- **K-ESC-3 (FIRED AT SCOPING, subfamily).** The SU(3)²U(1)
  equation alone as C: piFlip satisfies it (A3 = 0, §2.3).
  Dead; not re-enterable as a standalone clause.

**Family 1 price summary:** pin **M** (Shape A statement +
sector formalism, *excluding* extraction) or **S–M** (Shape B,
with K-ESC-2(c) armed); extraction gap **L** if Shape A is
chosen; pre-checks **S / S–M**. Rank: **#2**.

---

## 3. Family 2 — Second-order conditions / vanishing junk

### 3.1 What is statable

Everything here is built from landed operations: `π a`,
`piOp (π b)`, commutators with `DF_oneGen` (Yukawas ∀), matrix
products, and the 1-form vocabulary of `InnerFluctuations.
lean` (`IsAlgebraicOneForm`, `oppositeOneForm`,
`fluctuatedDirac` — T1/T2, but note: stated for the
`MartinettiRep.smGen`/`smDirac` seat, **not** for π₁/πFlip's
`DF_oneGen` seat; bridging that seat difference is a named
gap, not a detail). Three distinct conditions are routinely
conflated under "second-order"; they are priced separately:

- **2a. Junk-vanishing.** The finite-triple junk: expressions
  `∑ᵢ π(aᵢ)[D,π(bᵢ)][D,π(cᵢ)]` attached to universal 2-forms
  whose 1-form part vanishes (`∑ᵢ π(aᵢ)[D,π(bᵢ)] = 0` with
  `∑ᵢ aᵢbᵢ = 0` in the algebra) are required to vanish as
  operators. One new definition (the junk predicate) over
  landed operations; no weight values; Yukawas ∀. **Statable:
  S–M to pin.**
- **2b. Order-two commutator conditions.** E.g.
  `[[D, π a], [D, piOp (π b)]] = 0`, or the same with `D²` in
  one slot. Statable in one line each over landed operations.
  These are **not standard axioms** for the SM finite triple;
  they are invented conditions, and are discounted accordingly
  (§3.3).
- **2c. Fluctuation / Majorana stability.** Conditions on the
  fluctuated Dirac's Majorana block under π-generated
  fluctuations, in the shape of `InnerFluctuations`'
  `IsMajoranaSubspace` / `majorana_Eblock_rigidity` (T1, at
  the `smDirac` seat with its fifth Yukawa yR). The D1-A base
  seat (`DF_oneGen`, C = E = 0, no Majorana block) does not
  own the object this condition constrains. **Gap: the seat
  bridge. Price: L. Parked, not ranked.**

### 3.2 Escape analysis

All of 2a/2b are full-matrix identities (escape route E3):
they involve off-diagonal entries of products of commutators,
in which the ν_R seat's conjugation choice enters multiplied
by Yukawa entries (`DF_oneGen` couples seat 8 to seat 0 via
`Ynu`), in expressions that are **not** diagonal entries of a
`π * piOp π` product. `lifted_diag_partner` says nothing about
them. Escape: **genuine, in principle, for both π₁/piFlip
discrimination and against R1–R3.**

### 3.3 Pre-checks — the honest prior is bad for 2a, unknown for 2b

- **π₁-holds, 2a: prior NEGATIVE.** In the CCM finite geometry
  the standard representation's junk does **not** vanish as
  operators; the differential algebra is *quotiented* by the
  junk. Requiring outright vanishing is stronger than the
  axiom the corpus's model was built to satisfy, so the
  expected outcome of the pre-check is K-ESC-4 firing (the
  strengthened set excludes π₁ — mis-posed, exactly the
  K-D1A′-3 shape). This is a prior, not a result: the corpus's
  `DF_oneGen` is a simplified diagonal Dirac (C = E = 0), not
  the full CCM Dirac, so the computation is genuinely open.
  Price: **M** (symbolic AF parameters (λ, q, m) in a
  two-commutator product over 32 seats; entrywise, with the
  ∀-Yukawa quantifier making it a polynomial identity check,
  not a `decide`).
- **π₁-holds, 2b: UNKNOWN, no literature cover.** Neither
  condition is a named axiom of the model, so there is no
  external reason π₁ satisfies either; and a condition with no
  motivation independent of "it might exclude piFlip" carries
  the D1-A′ disease in a new form — it would be a clause
  invented against a known counterexample. That is not
  circularity under (c)/(d) (no values, no weight equation),
  but it is a *standing* discount Jeff should see on the face:
  a future entry on 2b must argue the condition is a law of
  the geometry before its pre-checks are worth their price.
- **piFlip-fails, both: UNKNOWN** (if π₁ passes, piFlip may
  also pass — its defect seat enters only through `Ynu`
  terms, and factorization `Ynu · (vanishing factor)` is a
  live possibility, as it was for first-order). Price: **M**
  each, after the π₁ check.

**Kill registrations (Family 2):**
- **K-ESC-4 (consistency).** If π₁ fails the pinned condition,
  the entry dies as mis-posed (the K-D1A′-3 shape).
- **K-ESC-5 (counterexample).** If piFlip satisfies base + the
  pinned condition, the entry dies at the gate (the K-D1A′-1
  shape).

**Family 2 price summary:** pin **S–M**; pre-checks **M + M**,
sequenced π₁ first, with a negative prior on 2a. Rank: **#3**
of the live families — statable and genuinely escaping, but
the only family whose *first* pre-check is expected to kill
it or whose motivation is in question.

---

## 4. Family 3 — Linear seat functionals: the γ_F-trace on raw π

### 4.1 Why linearity + partner-oddness evades the symmetry

`lifted_diag_partner` is a statement about a **quadratic,
partner-even** object: the diagonal of `M * piOp M`. Two
independent changes break its grip:

1. **First power.** Take π itself, not `π * piOp π`. There is
   no landed (and no true) identity forcing a linear functional
   of `π a` to be partner-symmetric: piOp enters only if the
   statement puts it there.
2. **Partner-odd weight.** γ_F satisfies
   `gammaF (partner i) (partner i) = −gammaF i i` (T1,
   `Scaffold32.gammaF_partner_flip`): γ_F is the grading
   `diag(+I₈, −I₈, −I₈, +I₈)` on `(H_L, H_R, H_L^c, H_R^c)`.
   A γ-weighted trace therefore adds a seat's contribution and
   *subtracts* its partner's, instead of identifying them. A
   conjugation flip at ONE seat (piFlip's whole content) moves
   the trace by twice that seat's γ-weighted contribution,
   with no compensating move at the partner seat, whose π-entry
   piFlip does not touch.

Note the contrast computed in §1.2 (R2): the same γ_F inserted
against the *lifted* product gives `0` for every π. γ_F is not
magic; its placement — first power, not lifted — is the whole
mechanism. Also computed and rejected as variants (§4.4): the
plain trace and the left-handed-projection trace.

### 4.2 The statement (exact shape)

One new definition — the only vocabulary gap in this family:

```
u1Gen (α β : ℤ) : AF := ⟨(α : ℂ) * Complex.I, 0, (β : ℂ) * Complex.I • 1⟩
```

the Lie-algebra element of `AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)` whose
exponential curve is the landed `u1ParamGen α β` (same seat
pattern: ℂ-component, zero ℍ-component, scalar M₃-component;
no value is named — α, β are bound variables). Then:

```
C3 (π) : Prop := ∀ α β : ℤ, Matrix.trace (gammaF * π (u1Gen α β)) = 0
```

`gammaF` is landed (T2 def, `Scaffold32`); `Matrix.trace` is
Mathlib. C3 names no weight, no sector, no Yukawa, no table.
It is a condition on π as a whole, of exactly the species of
the base set's grading clause (`∀ a, gammaF * π a = π a *
gammaF`) — γ_F was already a condition-set citizen before
this family was proposed; nothing is imported for the purpose.

### 4.3 Pre-checks (T2 arithmetic on T1 tables)

`π (u1Gen α β)` is seat-diagonal for both constructed
representations, with diagonal exponent coefficients given for
π₁ by the landed `pi1AVal`/`pi1BVal` tables (the generator's
diagonal at seat `v` is `i·(A(v)·α + B(v)·β)`). Summing
`gammaF v v · (A(v), B(v))` over the 32 seats:

- **π₁: HOLDS.** α-coefficient: `(−1) + (+1) + 0 + (+2) + (−2)
  = 0` (seats 8; 9; 10–15 alternating, sum 0; 16–17; 24–25;
  all other seats A = 0). β-coefficient: seats 18–23 contribute
  `γ·B = (−1)(−1)·6 = +6`; seats 26–31 contribute
  `(+1)(−1)·6 = −6`; total `0`. So `Tr (γ_F π₁ (u1Gen α β)) =
  0` for all α, β. In-tree price: **S** — the sums are the same
  species as the landed `sum_A`/`sum_B` (`decide` over the
  A/B tables), plus the diagonality of `π₁ (u1Gen α β)`, which
  is a specialization of the landed `pi1_eq_diagonal`
  machinery.
- **piFlip: FAILS.** piFlip differs from π₁ only at seat 8,
  where the generator entry flips `+iα → −iα`, and `γ_F(8,8)
  = −1`: the trace changes by `(−1)·(−iα − iα) = +2iα`. Hence
  `Tr (γ_F piFlip (u1Gen α β)) = 2α·i`, which is `≠ 0` at
  `(α, β) = (1, 0)`. In-tree price: **S–M** — the perturbation
  is one `Matrix.single` (the landed `piFlip = pi1 +
  Matrix.single s8 s8 (star a.u1 − a.u1)`), and the
  `single_*` entry lemmas for exactly this perturbation are
  landed in `HyperchargeForcing.lean`; the M part is assembling
  the trace computation, not new ideas.

Both pre-check computations are scoping arithmetic (T2) in
this dossier; the T1 versions are the priced entry of §4.5.

### 4.4 Variants checked and rejected (T2 arithmetic, same tables)

- **Plain trace** `Tr (π (u1Gen α β))`: π₁ gives `(−4, −12)`
  (the landed `sum_A`, `sum_B`), piFlip `(−6, −12)`. A clause
  naming `(−4, −12)` as its target names π₁'s own weight sums
  — value-adjacent, and redundant with the base set's
  determinant/unimodularity content. **Rejected**: C3's target
  `0` against a partner-odd weight is the clean form.
- **Left-handed projection** (sum over γ_F = +1 seats only):
  `(−2, −6)` for **both** π₁ and piFlip — the flip lives in
  the γ = −1 (right-handed particle) block, which an
  LH-only functional never sees. **Does not discriminate.**
  Recorded so nobody re-proposes it: the functional must
  weight the RH particle block with the opposite sign to its
  antiparticle block, which is precisely what γ_F does and a
  projection does not.

### 4.5 What C3 is, and is not — forcing power, fence, kills

C3 is **one linear equation** in the raw weights (two scalar
equations: α- and β-coefficients). It does not, and cannot,
force the ratios: weight assignments off the table satisfy it
whenever a second change compensates the first. The concrete
compensator candidate, at T2 arithmetic: flipping **both**
the ν_R seat (γ-trace change `+2α`) and the e_R seat (seat 9:
γ = −1, generator weight `−α → +α`, change `−2α`) restores
`Tr = 0`. Whether that double-flip representation satisfies
the full base set is **unproved** (the single ν_R flip did;
the e_R flip's first-order status is a computation nobody has
run — the D1-A mechanism, antiparticle ties vs free particle
seats, suggests particle-seat flips are the free ones, but
suggestion is not a theorem). This is registered, not hidden:

- **K-ESC-6 (compensator — pre-registered against any forcing
  claim at base + C3).** If a representation satisfying
  `DialOneBase ∧ C3` is exhibited whose lifted weights are not
  proportional to the COMMON HYPERCHARGE MATRIX — the ν_R+e_R
  double flip being the named first candidate to test — then
  base + C3 forcing is FALSE, permanently, at that set. Any
  entry on this family is therefore scoped as **pin +
  pre-checks only**; a forcing attempt at base + C3 alone is
  not priced, because §4.5's arithmetic already shows the
  clause is one equation short of the job by a wide margin.
  (A strengthened C3-family — e.g. γ-traces against a *family*
  of partner-odd operators, if any others are landed or
  honestly nameable — is a NEW scoping question, not this
  entry.)
- **K-ESC-4 / K-ESC-5 shapes apply** (π₁-fails / piFlip-passes
  at the gate), with §4.3's arithmetic making both unlikely;
  they stay registered because the entry's proofs, not this
  dossier's arithmetic, are the verdict.

**Fence audit.** (c) **Passes**: no value, sector, or Yukawa
named; γ_F's entries are the chirality grading (±1 by L/R
block), structural input of the same standing as the sector
decomposition itself — it encodes *handedness*, not
hypercharge (sectors with equal γ_F carry weights −3, 1, 0,
4 in π₁; γ_F cannot be a table in costume). (d) **Passes
under the operational reading**: over the base set, C3 is not
equivalent to any seat's weight equation — its solution set
in weight space is a hyperplane through the origin containing
off-table assignments (§4.5's compensator direction is a
nonzero vector in it), so it fixes no seat, directly or by
implication over base. The stricter-reading flag of §2.5
applies here too and is Jeff's call, once, for both families.

**Family 3 price summary:** one new definition; pin **S**;
pre-checks **S / S–M**; cheapest honest entry in this audit
(§7). Rank: **#1** — as an *escape condition with both
pre-checks priced and expected to pass*, not as a forcing.

---

## 5. Family 4 — Intertwining with the fixed D_F's pattern

**Legitimacy question (answered first): PASS.** Referencing
`DF_oneGen` is legitimate in principle: it is a landed corpus
object, its Yukawas are universally quantified in every
condition-set use, and no value is chosen at statement time.
The base set already references it (first-order clause). This
family does not die of smuggling. It dies of discrimination:

**K-ESC-1 — FIRED AT SCOPING (argument-grade, full rank).**
Let C be any condition on π factoring through the
kernel/image/support/spectral-subspace data of the
`DF_oneGen (Ynu Ye Yu Yd)` class (including `D_F²`, whose
spectral data is the same pairing data). Then C cannot
separate π₁ from piFlip:

- *Generic horn.* For all `Y ≠ 0`, `DF_oneGen` is invertible
  (it is `buildDirac A Ā 0 0` with `A` diagonal — T2 def,
  `FiniteSpectralTriple`): ker `= 0`, im `= ⊤`. Every
  preservation/intertwining condition on that data is vacuous,
  and piFlip passes it exactly as π₁ does.
- *Special horn.* At a vanishing Yukawa (say `Ynu = 0`,
  `Ye ≠ 0`), the kernel is the coordinate span of the ν seats
  `{0, 8, 16, 24}` — a decomposition **finer** than the one
  π₁ preserves: π₁'s ℍ action mixes seat 0 with seat 1
  (the lepton doublet), so π₁ itself does **not** preserve
  that kernel. The strengthened set excludes the corpus's one
  model: mis-posed, the K-D1A′-3 shape, for π₁ this time by
  proof-shaped argument rather than by prior.
- *The middle is empty.* The decompositions π₁ *does*
  preserve are the four coarse blocks `(H_L, H_R, H_L^c,
  H_R^c)` — which are the grading/sector data already in the
  base set, and which piFlip also preserves (its perturbation
  is a scalar change *inside* the H_R block at one seat).

A condition using D_F's actual *entries* against π's entries
(traces of `D_F π(a) D_F π(b)`, commutator products) is not
this family — it is Family 2 / Family 1-Shape-B territory and
is audited there. As posed — kernel/image intertwining with
the fixed D_F — **the family is dead, and the kill is the
two-horn argument above, not a missing effort.** No entry on
this family should be priced. (Turning the argument into a
T1 theorem would be a small formalization, **S**, if Jeff ever
wants the kill at theorem grade; the scoping verdict does not
wait for it.)

---

## 6. Family 5 — Further families, swept

- **5a. γ-inserted lifted traces** — `Tr (γ_F · π a · piOp
  (π b)) = 0`-shaped clauses. **K-ESC-7 — FIRED AT SCOPING
  (proof-shaped, §1.2 R2):** given the base set's order-zero
  clause, these vanish for **every** π in the base set,
  piFlip included. Vacuous; dead.
- **5b. Raw J-intertwining at the right-handed seats** —
  e.g. `(UJ * π (u1Gen α β) * UJ) s s = (π (u1Gen α β))ᴴ s s`
  required at RH particle seats `s`. This *does* discriminate
  in arithmetic (at seat 8: π₁ gives `−α = −α`; piFlip gives
  `−α ≠ +α`). **K-ESC-8 — KILLED BY THE FENCE (d), at
  scoping:** at a single seat the clause is exactly `w_s +
  w_{partner s} = 0`, i.e. "lifted weight at seat s equals
  0" — a per-seat weight equation, the precise shape
  K-D1A′-2 bans; and required at *all* RH seats it is also
  false for π₁ (x_eR = −6 ≠ 0), a consistency failure on top
  of the fence failure. The family shows the fence has teeth
  in both directions: it bans this, and (§4.5) it does not ban
  C3, whose content is a global sum, not a seat equation.
  (At L seats the raw intertwining fails π₁ outright — the
  J-opposite of the ℍ action is the ℂ action on the Lc block,
  so a single-summand generator is not J-real there —
  recorded as the reason no all-seats version exists.)
- **5c. Block-determinant / block-trace variants.**
  Logarithms of block determinants of `π (u1ParamGen α β t)`
  are block traces of `π (u1Gen α β)` — Family 3 with
  block-projection weights instead of γ_F. The block weights
  are partner-EVEN, so by §4.4's logic the discriminating
  member of this class is the γ-weighted one already ranked;
  the rest either name π₁'s sums (rejected, §4.4) or do not
  discriminate. No new content; not ranked separately.
- **5d. Spectral-action traces of D_F powers.** Already
  killed standing (Dial-1 scoping §2, D-c FREE; K-SA-4):
  polynomials in the input Yukawas. Not re-entered.
- **5e. Triplication / generation intertwining.** π₃ = π ⊗ I₃
  is imposed (T2); piFlip triplicates as readily as π₁.
  Generation-mixing intertwining constrains the *generation*
  index, which neither representation's defect touches.
  No discrimination; dead as an escape route (not registered
  as a numbered kill — it was never a live clause shape).
- **5f. Fluctuation stability at the Martinetti seat** —
  see §3.1 (2c): parked at **L** behind the seat bridge
  (`smDirac` with yR vs `DF_oneGen` without), unranked.

**Symmetry-reach note (task item 5, second half).** §§1.2,
5, 6 together are the proof-shaped statement scoping can
honestly offer: *every condition factoring through
partner-even lifted data (R1), partner-odd lifted data (R2),
or D_F subspace data (R3) is vacuous, base-implied, or
π₁-failing.* Families 1 and 3 stand outside R1–R3 by
construction (E2, E1). A *global* no-go — "no condition
outside the J-opposite/lifted-diagonal construction holds
the RH seats" — is **refuted at scoping** by Family 3's
arithmetic: a condition outside the construction, holding
for π₁ and failing for piFlip, exists on paper. What does
not exist on paper is a condition outside the construction
that *forces* — see §7.

---

## 7. Ranking, the cheapest honest entry, and its exact shape

**Survivors, ranked:**

1. **Family 3 (C3, the γ_F-trace on raw π).** Both pre-checks
   computed at scoping and expected to land; one new
   definition; total entry price **S–M**.
2. **Family 1 (anomaly conjunction, Shapes A/B).** Both
   pre-checks computed (π₁ holds; piFlip fails 3 of 4);
   statement price **M** (Shape B) to **M + L** (Shape A with
   extraction). Permanently barred from forcing alone by
   K-ESC-2(a) — its role, if any, is as a *second* clause
   beside a B−L-breaking one. Whether C3 breaks the B−L
   direction is a well-posed next scoping question (C3 is a
   statement about raw weights, the B−L line is a statement
   about lifted weights; their interaction is not computed
   here and is **not** claimed).
3. **Family 2 (second-order/junk).** Live only as a priced
   gamble: **S–M** pin, **M** first pre-check, negative prior
   on 2a, motivation discount on 2b, **L** and parked on 2c.

**Dead at full rank:** Family 4 (K-ESC-1); the SU(3)-only
anomaly subfamily (K-ESC-3); γ-inserted lifted traces
(K-ESC-7); raw RH J-intertwining (K-ESC-8, fence kill).

**The cheapest honest entry — exact statement shape.**
Nothing fires from this dossier. If Jeff fires one, the
priced recommendation is a **pin + pre-check entry on C3
only**, in full:

> **Definitions (new, one):** `u1Gen (α β : ℤ) : AF :=
> ⟨(α : ℂ) * Complex.I, 0, (β : ℂ) * Complex.I • 1⟩`.
> **Pin:** `GammaTraceCondition (π : AF → Matrix (Fin 32)
> (Fin 32) ℂ) : Prop := ∀ α β : ℤ, Matrix.trace (gammaF *
> π (u1Gen α β)) = 0`, stated beside `DialOneBase`
> (landed, `DialOneSeatTiePin.lean`), with K-ESC-4/5/6 on
> its face.
> **Stage 1 (pre-check i):** `GammaTraceCondition pi1` —
> expected proof by the landed diagonal machinery
> (`pi1_eq_diagonal` specialization + the A/B/γ sums of
> §4.3 by `decide`). Price **S**.
> **Stage 2 (pre-check ii):** `¬ GammaTraceCondition
> piFlip`, witnessed at `(α, β) = (1, 0)` with trace
> `2·Complex.I` — expected proof by the landed
> `Matrix.single` perturbation lemmas of
> `HyperchargeForcing.lean` over Stage 1's computation.
> Price **S–M**.
> **Explicit non-content:** no forcing statement is pinned,
> attempted, or implied. The entry's product is a *proved
> discriminating clause* — the first condition outside the
> J-opposite/lifted-diagonal construction, at theorem
> grade, that holds the ν_R seat's flip — plus the armed
> K-ESC-6 compensator test as the named next question.
> **Total: S–M.** Dial 1 remains 0 on every outcome of this
> entry, including FULL.

If both stages land, the honest next scoping (unpriced,
uncommissioned) is the *combination* question: base + C3 +
anomaly, with K-ESC-6's compensator and K-ESC-2(a)'s B−L
line as its two pre-registered counterexample hunts, run
before any forcing statement is drafted.

---

## 8. Fences

NO CLAIM — no Millennium problem is claimed solved or
advanced; no measured number is derived, or claimed
derivable, anywhere in this dossier. The COMMON HYPERCHARGE
MATRIX pin and its commonality stand untouched (T1); D1-A's
kill and D1-A′'s kill stand beside this pass at full rank —
this is a NEW scoping under the relabeling rule, not a rescue
of either. All kills registered here (K-ESC-1 … K-ESC-8) are
pre-registrations and scoping-grade firings as labelled; none
is a theorem until an entry lands it. **Dial 1: 0. All
dials: 0/4. Scoping is not progress toward the dial.**

## Backers since last landing

None new on the record since the last landing.
