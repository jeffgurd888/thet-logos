# DIAL-1 COMPENSATOR SCOPING — 2026-11-01

*Scoping only: nothing built, nothing proved in Lean, no code
touched, no entry fired. This dossier answers the named next
test left by entry D1-C3 (landed: pin
`DialOneGammaTracePin.lean` + checks
`DialOneGammaTraceChecks.lean`, both pre-checks PASS at T1) —
the compensator test pre-registered as **K-ESC-6** in the
escape scoping (`dial1-escape-scoping-2026-11-01.md` §4.5).
**Parts of any official statement closed by this pass: 0.
Dial 1 stays 0. All dials: 0/4. NO CLAIM.***

*Tier key: T1 = machine-checked in the landed tree (cited,
not re-proved here). T2 = definitions, statement shapes, and
scoping arithmetic / proof-shaped transport performed in this
pass on landed data (reproducible, not Lean-checked). Every
number below not cited to a landed theorem is T2 and is
labelled as such. All T2 arithmetic in this dossier was run
twice: by hand on the landed tables and by exhaustive
enumeration over the 256 particle-seat conjugation toggles
(§2.4); the two agree everywhere.*

---

## 0. Headline verdicts

| # | Question | Verdict |
|---|----------|---------|
| 1 | The ν_R+e_R compensator (K-ESC-6's named candidate) | **K-ESC-6 FIRES AT SCOPING LEVEL (T2, proof-shaped, full rank).** The double flip `piDouble` satisfies C3 exactly (T2, §1.2), its lifted weights are the table with ν_R ↔ e_R **swapped** — not proportional to the COMMON HYPERCHARGE MATRIX (T2, §1.3) — and every `DialOneBase` clause passes a clause-by-clause transport audit off landed proofs (§1.4), including first-order, the named unknown, which resolves **positively** by an exact seat transport (8→9, 24→25, 0→1; §1.5). Base + C3 forcing is therefore **FALSE on paper, permanently at scoping rank**. The T1 in-tree confirmation is priced **M** (§4) — it is a transport, not a new idea, and no step in it is unidentified. |
| 2 | Strengthened γ-trace family | **Separation exists in tiers (§2).** Clean tier (landed-motivation operators only: γ_F, lepton-sector and per-colour γ-traces, the e_R pair trace): joint toggle kernel = exactly the **three per-colour quark swaps** (8 of 256 toggles). Purpose-built tier (cross-colour mixed traces + one sector-weighted trace, both purpose-chosen to vanish — discount on the face): kernel = **{π₁ alone}** among toggles. **Scoping no-go at the clean tier for the quark swaps** (§2.5): no landed-motivation functional separates u_R^c from d_R^c within a colour. |
| 3 | Conjunction base + C3 + anomaly | **Does NOT rescue forcing (T2).** `piDouble` passes all four anomaly equations exactly (§3.1) — the anomaly system is symmetric under ν_R ↔ e_R (and under u_R ↔ d_R per colour), so it is blind to every swap compensator. C3's hyperplane and the anomaly branches intersect in at least the full swap group, not only at table-proportional assignments. Anomaly adds nothing against toggles that the clean γ-family does not already add more cheaply (§3.3). |
| 4 | Ranked next entry | **D1-CMP** (§4): pin-first, **M**, firing K-ESC-6 at T1, with K-CMP-1/2/3 pre-registered. No entry fires from this dossier. |

**Dial 1: 0/4 — on every outcome contemplated here, including
the T1 firing of K-ESC-6 (a kill is not a dial move).**

---

## 1. Q1 — The compensator test

### 1.1 The candidate (T2 construction on landed data)

π₁'s ℂ-seat actions at the two lepton R seats (T1 entry
lemmas, `Track1RouteB`):

- seat 8 (ν_R): `pi1 a 8 8 = a.u1` — raw generator weight
  `A₈ = +1` (landed table `pi1AVal`);
- seat 9 (e_R): `pi1 a 9 9 = star a.u1` — `A₉ = −1`. **π₁
  already conjugates the e_R seat.** The compensator flip at
  seat 9 is therefore *un*-conjugation, the mirror of
  piFlip's flip at seat 8.

```
piDouble a := pi1 a
  + Matrix.single s8 s8 (star a.u1 − a.u1)     -- piFlip's perturbation, landed form
  + Matrix.single s9 s9 (a.u1 − star a.u1)     -- its seat-9 mirror (NEW, T2 here)
```

i.e. seat 8 acts by `star a.u1`, seat 9 acts by `a.u1`, every
other entry is π₁'s. This is exactly the piFlip species
(`HyperchargeForcing.piFlip`, T1): a diagonal
`Matrix.single` perturbation at ℂ-summand particle seats.

### 1.2 C3 membership (T2, one landed half + one transport)

Landed at T1 (`DialOneGammaTraceChecks`):
`Tr (γ_F · pi1 (u1Gen α β)) = 0` and the seat-8 perturbation
contributes `+2α·i` (`trace_gammaF_single_s8`, γ_F(8,8) = −1
against `star(αi) − αi = −2αi`).

Seat-9 transport (T2): γ_F(9,9) = −1 (same H_R block); the
perturbation value at `u1Gen α β` is `αi − star(αi) = +2αi`;
trace contribution `(−1)·(+2αi) = −2αi`.

**Total: `Tr (γ_F · piDouble (u1Gen α β)) = 0 + 2αi − 2αi
= 0` for all α, β. C3(piDouble) holds (T2).** The β
coefficient is untouched (B₈ = B₉ = 0, landed tables).

### 1.3 Lifted weights — the swap (T2 arithmetic on T1 tables)

Along a direction (α, β) the raw slot weight is
`Aᵢα + Bᵢβ`. π₁'s unimodular direction is (3, −1) (T1,
`sum_A`/`sum_B`: −4α − 12β = 0). **piDouble's determinant is
π₁'s exactly**: the seat-8 flip changes the det exponent by
−2α (T1, `piFlip_det_gen`), the seat-9 flip by +2α (mirror
computation, T2), total change 0 — exponent `−4α − 12β`,
primitive unimodular direction **(3, −1)**, π₁'s own (unlike
piFlip, which moved to (−2, 1)).

Lifted sector weights `x_f = w(seat) + w(partner seat)`,
`w = 3A − B` along (3, −1):

| sector | ν_L | e_L | u_L | d_L | ν_R | e_R | u_R | d_R |
|---|---|---|---|---|---|---|---|---|
| table x(π₁) (T1) | −3 | −3 | 1 | 1 | **0** | **−6** | 4 | −2 |
| x(piDouble) (T2) | −3 | −3 | 1 | 1 | **−6** | **0** | 4 | −2 |

**The double flip exactly swaps the ν_R and e_R lifted
weights.** Not proportional to the COMMON HYPERCHARGE
MATRIX: any proportionality constant is fixed by ν_L
(κ = 1 in this normalization), which would force
x_νR = 0; piDouble has x_νR = −6. (Witness shape for the
in-tree test, T2: at t = π/12 the ν_R lifted eigenvalue is
`exp(−6·(π/12)·i) = −i ≠ 1`.)

### 1.4 `DialOneBase`, clause by clause

`DialOneBase` as assembled in `DialOneSeatTiePin` (T1):
representation laws (afMul / afAdd / afStar / afOne /
afZero), injectivity, grading, order-zero, first-order
(∀ Yukawas), unimodular direction.

| Clause | Status | Basis |
|---|---|---|
| afAdd | **Known computation** | Perturbation coefficients are additive in `a` (`star` additive); piFlip's `piFlip_afAdd` proof (T1) transports verbatim, twice. |
| afOne / afZero | **Known computation** | Both coefficients vanish at `a.u1 = 1` and `a.u1 = 0`; same two-line transport. |
| afMul | **Proof-shaped transport (T2)** | Seat-8 coefficient identity is T1 (`piFlip_afMul`). Seat-9 coefficient `d(a) = a.u1 − star a.u1` satisfies the mirror identity `d(ab) = star a.u1·d(b) + d(a)·star b.u1 + d(a)d(b)` (T2 algebra, checked in this pass: both sides equal `a.u1·b.u1 − star a.u1·star b.u1` after expansion against the seat's base value `star a.u1`). Cross terms between the two singles vanish (`single_mul_single`, seats 8 ≠ 9, T1 lemma shape). No new idea. |
| afStar | **Proof-shaped transport (T2)** | Conjugate-transpose of a diagonal single is the single of the conjugate (T1 pattern in `piFlip_afStar`); seat 9's identity `star (afStar a).u1 − …` mirrors seat 8's. |
| Injectivity | **Known computation — strictly easier than piFlip's** | piFlip's T1 proof recovered `a.u1` *from seat 9* (via `star`). piDouble's seat 9 gives `a.u1` directly; ℍ and colour recovery seats are untouched. |
| Grading | **Known computation** | γ_F is diagonal; a diagonal single at any seat commutes with it by the T1 pattern (`piFlip_grading_even`'s `hsingle`, which uses only diagonality). |
| Order-zero | **Proof-shaped transport (T2)** | `piOp` sends the seat-9 single to a seat-25 single (partner 9 = 25; `piOp_single`, T1). All perturbations are diagonal singles at seats {8, 9, 24, 25}; π₁'s H_R block is diagonal at the singlet seats and block-diagonal at quark seats, so every cross product is either a T1-proved commutation (seats 8/24) or its disjoint-index / diagonal mirror (seats 9/25). |
| Unimodularity | **Known computation** | §1.3: det exponent identical to π₁'s; direction (3, −1), gcd 1. Composes two landed det computations. |
| **First-order** | **NEW computation — resolved positively at proof-shaped level in §1.5; nobody has run it in Lean** | The named unknown of the escape scoping. All of its steps are transports of landed seat-8/24 arguments to seats 9/25 and 1; no step is unidentified, but the transport is a real brick (§4 price). |

### 1.5 First-order at seat 9 — the transport in detail (T2)

The landed piFlip first-order proof (T1,
`piFlip_first_order`) works because three coincidences hold
at the (0 ↔ 8) Dirac pairing. **All three hold verbatim at
the (1 ↔ 9) pairing:**

1. **Matched slots.** `md 9 = 1`, `md 1 = 9` (T1 `md_val_R` /
   `md_val_L`: md is ±8). The commutator `[DF_oneGen,
   piDouble a]` therefore differs from `[DF_oneGen, pi1 a]`
   by a seat-9 correction supported exactly at entries
   (1, 9) and (9, 1) — the transport of
   `piFlip_comm_entry` (T1, support (0, 8), (8, 0)).
2. **Equal Yukawa values.** `Dval` is mod-8 periodic (T1):
   `Dval 9 = Dval 1 = (Ye : ℂ)`, exactly as `Dval 8 = Dval 0
   = (Ynu : ℂ)` (T1 `Dval_s8`). The correction is
   `F = single 1 9 (Ye·d(a)) + single 9 1 (−Ye·d(a))`,
   `d(a) = a.u1 − star a.u1`.
3. **Equal ρ-diagonal values at the paired seats.**
   `rho1 b 1 1 = pi1 b 17 17 = star b.u1` (partner 1 = 17,
   Lc lepton diagonal, T1 entry lemma) and
   `rho1 b 9 9 = pi1 b 25 25 = star b.u1` (partner 9 = 25,
   Rc singlet, T1 entry lemma) — **equal**, which is the
   whole content of the landed `single_s0_s8_comm_rho1`
   (there: seats 0 and 8, both `star b.u1`). The off-diagonal
   vanishing also transports: ρ₁'s rows/columns at 1 and 9
   are diagonal-only in the relevant entries (row 9 reads
   π₁'s column-25 entries, nonzero only at row 25; row 1
   reads the Lc lepton block, which is diagonal). Hence
   `[F, rho1 b] = 0` proof-shaped.

The remaining new pieces are the same species:

- `[C₁, single 25 25 ·]` where `C₁ = [DF, pi1 a]`: needs
  C₁'s row/column 25 to vanish — the transport of the landed
  `comm_col_s24` / `comm_row_s24`: `md 25 = 17`,
  `Dval 25 = Dval 17 = (Ye : ℂ)`, `pi1 a 17 17 = star a.u1`,
  and the two terms cancel by `mul_comm`, exactly as at
  24/16 with Ynu.
- Cross terms between the seat-8 correction E, the seat-9
  correction F, and the ρ-side singles at 24/25: all are
  `single_mul_single` products at pairwise distinct indices
  ({0,8} × {1,9} × {24} × {25}); every mixed product is 0 on
  both sides (the landed `correction_comm_s24` pattern).

**What this teaches, whichever way the T1 run lands:** the
base set's grip on particle seats is *exactly* the three
coincidences above, and they are **per-Dirac-pair local** —
each ℂ particle seat is tied only to its own md-partner
through (equal Dval, equal ρ-diagonal), never to any other
particle seat. That is why single flips passed in D1-A, why
compensating pairs pass now, and why no condition factoring
through the base set's own mechanisms will ever see a
*pattern across* particle seats. The grip on the
*antiparticle* seats is genuinely stronger (first-order ties
their conjugation choices to each other — T1 mechanism,
`HyperchargeForcing` header), and §2.6 notes the one
C3-invisible direction that lives there.

### 1.6 Verdict on Q1

**K-ESC-6 FIRES AT SCOPING LEVEL.** piDouble satisfies
base + C3 on paper (§§1.2, 1.4, 1.5) with lifted weights not
proportional to the COMMON HYPERCHARGE MATRIX (§1.3).
**Base + C3 forcing is FALSE — permanently, at scoping
rank.** This is the kill the lane pre-registered, reported
at the same speed as a positive result per house law. The
fence on the firing: it is T2 proof-shaped, not T1; the
in-tree confirmation (entry D1-CMP, §4, price **M**) is a
transport audit with every step identified above — if it
were to fail, it would fail at a *named* clause, and that
failure (not a rescue of forcing) is pre-registered as
K-CMP-1. Dial 1: **0**.

---

## 2. Q2 — The strengthened γ-trace family

### 2.1 Framework (T2)

For a diagonal operator `D = diag(dᵢ)`, the functional
`F_D(π) := Tr (D · π (u1Gen α β))` on a seat-diagonal
candidate is `i · Σᵢ dᵢ (Aᵢα + Bᵢβ)`. Only `diag D`
matters against diagonal candidates. **Partner-odd** means
`d_{partner i} = −dᵢ`; for diagonal D this is the same class
as J-odd diagonal (`UJ_gamma_anticomm`, T1, is the γ_F
instance). Pairing seats (pair `s` = {s, partner s},
s = 0…15), each pair contributes
`γ_s · [(A_s − A_{partner s}) α + (B_s − B_{partner s}) β]`
for the γ-signed basis. π₁'s pair-contribution table (T2
from T1 A/B tables; exhaustive check in the scratch
enumeration):

| pair (particle seat) | 0 ν_L | 1 e_L | 2–7 q_L (each) | 8 ν_R | 9 e_R | 10 u_R⁰ | 11 d_R⁰ | 12 u_R¹ | 13 d_R¹ | 14 u_R² | 15 d_R² |
|---|---|---|---|---|---|---|---|---|---|---|---|
| (α, β) contrib | (1,0) | (1,0) | (0,1) | (−2,0) | **(0,0)** | (−1,−1) | (1,−1) | (−1,−1) | (1,−1) | (−1,−1) | (1,−1) |

Total (0, 0) — C3 itself (T1). Two structural facts drive
everything below: **pair 9 (e_R) contributes (0,0)** — its
particle and antiparticle raw weights already agree in π₁ —
and **no individual pair except pair 9 vanishes**, so the
family cannot be refined pair-by-pair (per-pair conditions
at any other pair fail π₁: K-ESC-4 shape, dead on arrival).

**Flip visibility.** A conjugation toggle at particle ℂ
seat s ∈ {8,…,15} changes pair s's α-contribution by
`γ_s · (−2A_s)`: seat 8: +2; 9: −2; u_R seats: +2; d_R
seats: −2 (β-contributions of particle seats are 0). The
toggle model — the base set's freedom as described by the
D1-A mechanism (T1 header) — is: 8 independent particle ℂ
toggles, antiparticle choices tied by first-order (§2.6).
A functional `F_S` over a pair-set S **vanishes for π₁**
iff Σ_{s∈S} contrib_s = (0,0), and **sees** exactly the
toggles in S. This is the complete scoping calculus of the
family; everything in §§2.2–2.5 is read off it and was
verified by enumeration over all 256 toggles.

### 2.2 Audit of candidate operators — what is landed, what is nameable

- **γ_F** — landed (T2 def / T1 identities, `Scaffold32`).
  The C3 functional itself.
- **Block splits G_L, G_R** (γ_F restricted to the pair
  blocks {0…7} / {8…15}, i.e. γ_F composed with the
  H_L∪H_L^c / H_R∪H_R^c projections): partner-odd ✓, but
  π₁-values **(2, 6) and (−2, −6)** (T2) — **π₁ FAILS
  both**. Dead as clauses (K-ESC-4 shape). Recorded so
  nobody re-proposes the chirality split.
- **Sector projections composed with γ_F** — no Fin-32
  sector projection is landed *as a named operator* (the
  tree's `AveragingProjection` / `BlockingProjection` are
  lattice objects on other spaces — audited, not this
  seat). Each is honestly **nameable in one definition**
  from landed vocabulary: `Matrix.diagonal` of the
  indicator of a `fermionIndex` sector / colour class
  (`SMFermions`, T2 structural input — the same standing
  conditional the whole Dial-1 lane carries). Lepton-sector
  and per-colour projections are the useful instances
  (§2.3).
- **UJ insertions** — `Tr (UJ · π (u1Gen ·))` and
  γ_F·UJ variants: **identically zero** on diagonal
  candidates (UJ is a pure partner permutation, zero
  diagonal). Vacuous; dead (not numbered — never a live
  shape).
- **Other AF Lie-algebra directions** — traces of γ_F·π at
  ℍ generators or off-diagonal/scalar-free M₃ generators:
  π₁'s entries there are traceless blocks (ℍ Lie elements)
  or colour matrices supported off the ℂ seats; the flipped
  seats carry 0 in those directions. **Blind to every ℂ
  toggle** (T2). The (α, β) plane of `u1Gen` already spans
  every direction that sees seat weights. No new functionals
  live here.
- **Non-diagonal D**: against diagonal candidates only
  diag D enters (§2.1); nothing gained.
- **Purpose-built diagonal weights** (sector scalars w_f
  with d = γ·w_sector, or cross-colour pair sets): statable
  in one definition each, no table values, no seat fixed —
  fence-clean under the operational reading of the escape
  scoping §2.5/§4.5 — but **chosen from the vanishing
  solution space because they separate**: the invented-
  condition discount (escape scoping §3.3, Family 2b)
  applies and is carried on their face in §2.4.

### 2.3 The clean tier (landed-motivation operators)

| Functional | Pair-set S | π₁ value | Sees (toggle form, ×2) |
|---|---|---|---|
| C3 (γ_F) | all 16 | (0,0) T1 | f₈ − f₉ + Σ_c (f_{u^c} − f_{d^c}) |
| C3_lep (γ_F · lepton projection) | {0,1,8,9} | (0,0) T2 — **new computation**, sub-sum of C3's; not implied by it | f₈ − f₉ |
| C3_col,c (γ_F · colour-c projection), c = 0,1,2 | {2c-lepton-free quark pairs of colour c} = pairs {2+2c, 3+2c, 10+2c, 11+2c} | (0,0) T2 each — new computations | f_{u^c} − f_{d^c} |
| F_eR (γ_F · e_R-sector projection) | {9} | (0,0) T2 — the (0,0) pair | −f₉ (particle side) |

Notes: C3 is implied by C3_lep + Σ_c C3_col,c (pair-sets
partition the 16 pairs) — keep C3 anyway; it is the landed
one. F_eR is a *two-seat tie in raw weights*
(A₉ = A₂₅ ∧ B₉ = B₂₅ over the base set): it names no value
and fixes no seat, so it passes the fence under the
operational reading — but it holds for π₁ at **exactly one
pair**, and that accident is its entire motivation. Flagged
as the clean tier's weakest-motivation member; the tier is
reported both with and without it.

**Joint toggle kernel (T2, enumerated):**
- {C3, C3_lep, C3_col,0/1/2, F_eR}: f₉ = 0, f₈ = f₉ = 0,
  f_{u^c} = f_{d^c} ∀c → **kernel = the three per-colour
  quark double flips** {(10,11)}, {(12,13)}, {(14,15)} and
  their unions — **8 of 256 toggles**. The named ν_R+e_R
  compensator is dead in this tier.
- Without F_eR: kernel additionally contains (8,9) — 16 of
  256. F_eR is load-bearing against the lepton swap; say so
  on its face if it is ever pinned.

Each surviving quark double flip is a **swap compensator**
of exactly piDouble's species: flipping (u_R^c, d_R^c)
swaps their lifted weights (x_{u^c} ↔ x_{d^c} per colour;
sector-uniform only if all three colours flip together).
Its base membership is the same transport species as §1.5
(md-pairs 2↔10, 3↔11; Dval Yu/Yd equal within each pair;
ρ-diagonals at 2 and 10 both `star (b.color c c)` — the
third coincidence holds with colour entries in place of
`b.u1`, T2) — priced in §4 as the follow-on test, **not**
audited to §1.5's depth in this pass.

### 2.4 The purpose-built tier (discount on the face)

Two more functionals close the kernel entirely:

- **Cross-colour mixed trace** F_×: pair-set
  {2, 10} ∪ {5, 13} (u-pairs of colour 0, d-pairs of
  colour 1). π₁ value (0,0) (T2: (0,1)+(−1,−1) + (0,1)+
  (1,−1)). Toggle form: f_{u⁰} − f_{d¹}. Nameable, but the
  pair-set is chosen *because* the contributions cancel —
  no landed structure singles out (colour 0 up) × (colour 1
  down).
- **Sector-weighted trace** F_w: d = γ_F · w_sector with
  w = (3 on ν_L pairs, 1 on u_L pairs, 1 on u_R pairs, 0
  elsewhere). π₁ value (0,0) (T2: α: 3·1 − 3·1 = 0 via the
  u_R aggregate; β: 3·1 − 3·1 = 0). Toggle form: aggregate
  (f_{u⁰}+f_{u¹}+f_{u²}).

Joint kernel of clean tier + F_× (+ its colour rotations)
+ F_w: colours force f_{u^c} = f_{d^c}; F_× chains
f_{u⁰} = f_{d¹} = f_{u¹} = … so all six quark toggles are
equal to a single g; F_w forces 3g = 0 → g = 0. **Kernel =
{empty toggle} = π₁ alone among the 256 toggles (T2,
enumerated).** So a finite family whose joint vanishing
leaves no compensator toggle **exists** — in purpose-built
vocabulary. The honest label: these clauses would be
*invented against known counterexamples*, the Family-2b
disease in γ-trace dress. They are fence-legal and
motivation-poor. Whether that trade is ever worth an entry
is Jeff's call, not this dossier's; §4 does **not** rank
them as the next entry.

### 2.5 The scoping no-go (clean tier, full rank)

**No family of γ-trace functionals built from γ_F and
landed sector/colour projections separates the seats.**
Proof-shaped (T2): such a functional's toggle form is a
{0, ±1}-combination of the sector/colour incidence forms;
π₁-vanishing forces its colour-c quark part to be
proportional to (f_{u^c} − f_{d^c}) (the colour-c
contributions (−1,−1), (1,−1) admit no other vanishing
combination, and mixing colours only reproduces the
per-colour differences or the aggregate). Every surviving
functional therefore vanishes on each per-colour swap
(f_{u^c} = f_{d^c} = 1) — the swaps are **invisible in
principle** to the clean tier, because within a colour the
u_R and d_R pairs differ only in the sign of their
α-contribution, and a vanishing sum must weight them
oppositely. Separating them requires a weight that breaks
the u/d symmetry *by hand* (§2.4) — i.e. the information
"u ≠ d" entered as a chosen coefficient, one step from the
table in costume. Registered as the clean-tier boundary;
not a numbered kill (it bounds a vocabulary, not an entry).

### 2.6 Scope fence on the whole family analysis

The toggle calculus covers particle ℂ-seat conjugation
toggles and (via pair differences) their antiparticle
mirrors. Two directions outside it, noted for completeness:
(i) the joint antiparticle M₃ un-conjugation (both
antiparticle blocks, β-side) is **C3-invisible** (T2: its
γ-weighted β-sum is 0 — it is the π₀↔π₁ axis) but is
base-killed by first-order (that is what Route B *is*,
T1); (ii) a general classification of base-set
representations (are toggles + π₁ all of them?) is **not
landed and not claimed** — every kernel statement above is
a statement about the toggle family, which is the family
every Dial-1 counterexample so far lives in.

---

## 3. Q3 — The conjunction option: base + C3 + anomaly

### 3.1 piDouble against the anomaly system (T2 on T1 weights)

Escape scoping §2.1's four equations on
x(piDouble) = (−3, −3, 1, 1, −6, 0, 4, −2):

- A3: (1+1) − 4 − (−2) = **0** ✓
- A2: (−6) + 3·(2) = **0** ✓
- A_grav: −6 + 6 − (−6+0) − 3·(4−2) = **0** ✓
- A111: (−27−27) + 3·(1+1) − (−216+0) − 3·(64−8)
  = −54 + 6 + 216 − 168 = **0** ✓

**piDouble passes the full anomaly conjunction.** The
reason is structural, not numerical luck: the right-handed
lepton singlets enter every anomaly coefficient only
through the symmetric combinations (x_νR + x_eR) and
(x_νR³ + x_eR³), and the swap preserves both
(−6 and −216 in the two assignments). The same holds per
colour for u_R ↔ d_R (A3 and A111 are symmetric in the
pair; A2 and A_grav see only sums). **Every swap
compensator is anomaly-invisible.**

### 3.2 Shape of the intersection (T2)

In lifted-weight space the anomaly solution set is the
escape scoping §2.4 cone: two branches s = ±t plus the
degenerate Q = 0 branch, with the continuous B−L direction
along a branch. The swap assignments are **discrete
off-table points on the same branch** as the table (the
swap is an isometry of the system, so it maps the branch
to itself). C3 is a condition on *raw* weights; its
hyperplane (in toggle space: the balanced-toggle plane)
contains every swap by §§1.2/2.1. Hence:

**base + C3 + anomaly does NOT intersect only at
table-proportional assignments. It contains, at scoping,
the full (ℤ/2)⁴ swap group generated by the lepton swap
and the three per-colour quark swaps** (each generator's
C3- and anomaly-vanishing is T2 above; each generator's
base membership is §1.5-transport grade — T1 only for none
yet, priced in §4). In the full 256-toggle enumeration,
C3 ∧ anomaly (seat-level) admits **40** toggles, including
non-swap balanced combos (e.g. cross-colour pairs
f_{d¹} + f_{u²}) — the conjunction is *weaker* on toggles
than the clean γ-family of §2.3 (8 toggles), not stronger.

On the continuous B−L direction specifically: toggles are
discrete (±2 steps in raw A), so no toggle *is* a B−L
point except the table; whether a non-toggle base-set
representation realizes B−L-mixed weights is the
realizability question the escape scoping already flagged
as unpriced hope (§2.4 there). **It remains open, and this
pass prices it no higher:** nothing in C3 or the anomaly
system speaks to it, because both are conditions that the
B−L line was *designed* (by the textbook algebra) to
satisfy/ignore. A forcing proof at the combined set would
have to exclude B−L realizability first — a classification
theorem about the base set, price **L+**, unscoped here.

### 3.3 What remains open on the combined set

1. T1 base membership of the swap generators (priced §4).
2. B−L realizability over the base set (above; L+, open).
3. The anomaly family's own vocabulary gap (escape scoping
   §2.2: weight extraction, **L** for Shape A; Shape B's
   identification theorem, K-ESC-2(c)) — **unchanged and
   now moot for forcing**: since the conjunction fails at
   scoping by symmetry, no anomaly pin should be bought
   for Dial-1 forcing purposes at any price. Its only
   remaining Dial-1 use would be as a *filter* in a set
   that already contains a swap-breaking family — and
   §2.3's clean family is that filter, cheaper (S–M pins,
   no extraction gap). **Recommendation at scoping: the
   anomaly conjunction is a dead end for this lane; do not
   price its pin.**

---

## 4. Q4 — The ranked, priced next entry

### Rank 1 — D1-CMP: fire K-ESC-6 at T1 (pin-first)

> **Pin (S):** `piDouble` beside `piFlip` in a new module
> (`DialOneCompensatorPin`-shaped): the two-single
> perturbation definition, read-backs, C3 and the
> strengthened set cited from `DialOneGammaTracePin`, the
> forcing target cited unchanged (COMMON HYPERCHARGE
> MATRIX), and K-CMP-1/2/3 on the face. NO forcing Prop
> restated; the entry's theorem is the kill.
> **Stage 1 (S):** `C3 piDouble` — landed seat-8 trace
> lemma + its seat-9 mirror (`trace_gammaF_single_s9`),
> composed over `trace_gammaF_pi1_u1Gen = 0`.
> **Stage 2 (M, the brick):** `DialOneBase piDouble`,
> clause by clause per §1.4's table; first-order is the
> bulk (seat-9/25/1 transports of `piFlip_comm_entry`,
> `comm_col_s24`→25, `single_s0_s8_comm_rho1`→(1,9), plus
> disjoint-index cross terms). Every lemma pattern exists
> landed at seats 8/24/0/16; this is transport, not search.
> **Stage 3 (S):** non-proportionality — lifted ν_R entry
> along (3, −1) is `exp(−6ti)` against the table's `1`
> (witness t = π/12, mirroring `piFlip_weights_not_
> proportional`), concluding
> `¬ DialOneForcing`-at-base+C3 in the registered shape:
> **K-ESC-6 FIRES at T1.**
> **Total: M.** Dial 1 remains 0 on every outcome.

**Pre-registered kills for D1-CMP:**
- **K-CMP-1 (transport failure).** If any base clause fails
  in-tree for piDouble, the entry reports the clause at
  full rank, the §0 scoping firing is revised to
  "undecided, failed at clause X", and the failure — which
  would localize the base set's first cross-seat grip — is
  itself the result. (Scoping expectation: does not fire;
  §1.5 identifies every step.)
- **K-CMP-2 (arithmetic).** If piDouble's lifted weights
  prove proportional to the COMMON HYPERCHARGE MATRIX,
  K-ESC-6 does not fire and this dossier's §1.3 is wrong at
  T2 — reported at full rank. (Expectation: does not fire;
  the swap is exact integer arithmetic on landed tables.)
- **K-CMP-3 (consistency, standing shape).** If the pin's
  C3(piDouble) pre-check fails, the entry dies at the gate
  (K-ESC-4 shape transposed). (Expectation: does not fire;
  §1.2.)

### Rank 2 — D1-CMP-FAM: the clean-tier family pin (only if Rank 1 lands)

Pin the four clean functionals of §2.3 (C3_lep, C3_col,c
×3, F_eR — five clauses, one definition pattern:
sector/colour diagonal projections composed with γ_F),
pre-checks π₁-holds (**S**, ℤ-shadow `decide` over sub-sum
tables, same species as `gamma_weighted_sum_A/B`) and
piDouble-fails (**S**, by F_eR alone — C3_lep passes
piDouble, since the compensation is internal to the lepton
sector; F_eR is load-bearing, §2.3), then the
three quark-swap base tests (one transport species,
**M** total) with their own K-CMP kills. Product if FULL:
base + clean family excludes *all* toggle compensators
except the quark swaps, and then those too if their base
tests fail — or **K-CMP-F1 fires** (a quark swap in base +
family ⇒ forcing at that set is FALSE, permanently) if
they pass. Price: pin + pre-checks **S–M**, swap tests
**M**. F_eR's weak motivation (§2.3) is stated on the pin's
face; the family is reported with/without it.

### Explicitly NOT ranked

- **The anomaly pin** (any shape) for Dial-1 forcing —
  dead at scoping by §3's symmetry; buying its L extraction
  gap purchases a filter strictly weaker than Rank 2's.
- **The purpose-built tier (§2.4)** as an entry — fence-
  legal, kernel-closing, and motivation-invented; ranking
  it would spend the lane's credibility to exclude toggles
  by coefficients chosen to exclude them. Parked, with its
  arithmetic on the record, for Jeff's explicit call only.
- **Any forcing attempt** at base + C3, base + C3 +
  anomaly, or base + clean family (pre-swap-tests): all
  FALSE at scoping or one named test away from a registered
  kill. The lane's honest frontier after D1-CMP is the
  classification question (base-set realizability, L+,
  unscoped) — **that**, not another clause, is where a
  forcing proof would have to come from, if one exists.

---

## 5. Fences

NO CLAIM — no Millennium problem is claimed solved or
advanced; no measured number is derived, or claimed
derivable, anywhere in this dossier. The COMMON HYPERCHARGE
MATRIX pin and its commonality stand untouched (T1); D1-A's
kill, D1-A′'s kill, and D1-C3's landed exclusion of piFlip
stand beside this pass at full rank — K-ESC-6's scoping
firing kills **base + C3 forcing**, not D1-C3's proved
content (a discriminating clause, first of its kind in the
lane, exactly as its dossier stated its rank). All kills
registered here (K-CMP-1/2/3, the clean-tier no-go of §2.5)
are scoping-grade as labelled; K-ESC-6 itself is a
pre-registration from the escape scoping, fired here at
scoping (T2) rank and priced for T1 confirmation as Rank 1.
**Dial 1: 0. All dials: 0/4. Scoping is not progress toward
the dial — including this scoping's kill, which closes a
door, not a dial.**

## Backers since last landing

None new on the record since the last landing.
