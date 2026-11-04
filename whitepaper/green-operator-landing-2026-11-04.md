# The Green operator — the well-posed inverse of the seat Laplacian, landed

## VERDICT: FULL — the well-posed object forms exactly as pinned. Dial-ineligible by pre-registration: Dial 2 = 0.

**Item:** the Green operator (working label — Jeff names), the
well-posed inverse of the seat Laplacian, in the shadow program's
family (post-SR-5 bookkeeping). Commission: Jeff's seeing of
2026-11-04 ("we have the nested space and an ill-posed solution.
Now just form a well posed object") → BONES' bounded reading
(form the Green operator as a named T1 object under the
pre-registered Dial-ineligibility fence) → Jeff's "yes" (12:54
EST) to the scoping and "build it" (12:58 EST). Governing
scoping: `~/workspace/your_files/green-operator-scoping-2026-11-04.md`
(route A, headlines §2.2, price S–M / strict 12–20, kills
K-GREEN-1/2/3, fence §0), inside the gravity-object audit
(`gravity-object-audit-scoping-2026-11-04.md`: D2-0…D2-6, P-D2)
and the shadow scoping (`dial2-shadow-scoping-2026-11-04.md`).
Consumes landed stock at its exact landed shapes — T2
`ThermalChargePoisson` (existence, the restriction `lapRestrict`,
its injectivity), SHADOW-TEST-1 `PoissonTotalMassBlindness`
(the `meanSub` projection API, `poissonPotential`),
`BridgeLaplacian` / `BridgeCompletion` (the operator, its
linearity, `laplacianOp_symm_form`); no landed module edited.

Module: `lean/ThetLogos/GreenOperator.lean` (NEW).
Lane: `green-operator-lane`, isolated worktree
`~/workspace/thet-logos-green`, cut from main HEAD `58d35b9`
(census 13,340 strict / 493 modules; fence 378/378 — verified
at cut). Targeted build green (**3,319 jobs**), **ZERO
sorrys**, module **WARNING-CLEAN** (forced rebuild: zero
warning lines name this module; warnings in the wider build
log belong to pre-existing corpus dependency modules), **no
`native_decide`** (the header's prose mention is the phrase
"no `native_decide`", as in landed modules). **Measured
strict count: 17 theorems + 2 defs** — inside the priced
band of **12–20** (see the count note under Deviations).
Axiom audit (`#print axioms`, run against the built module):
**all 17 theorems depend on exactly `{propext,
Classical.choice, Quot.sound}`** — no `sorryAx`, nothing
outside the standard trio. NO integration, NO push — lane
commit only.

## The fence (scoping §0, verbatim in spirit — it is part of the registration)

This object is **the shared inversion made well-posed**.
Nothing more. The corpus's one Laplacian inversion serves
heat, entropy, charge, and potential readings alike;
packaging its inverse does not promote any one reading.
**K-SR-4 stands over it.** SHADOW-TEST-1
(`PoissonTotalMassBlindness`) proved the inversion factors
through the mean-subtracted source `meanSub g` and is
therefore **blind to total mass**: a constant shift of the
source — pure total mass at fixed contrast — changes nothing
downstream. The Green operator inherits this exactly, and
this module states the inheritance at the operator itself
(`greenOp_const`, `greenOp_meanSub`, `greenOp_eq_zero_iff`).
**Pre-registered Dial-INELIGIBLE.** This brick does not move
Dial 2, under any outcome, including this full landing. It
asserts no response law: it does not state that matter
falls, that geometry responds, that anything is attracted
to anything. It is a bookkeeping/well-posedness brick, the
same family and ceiling as SR-5 (`ThermalSourceComposite`),
whose ceiling was kernel-fenced by SHADOW-TEST-1 in exactly
the same way. **NO CLAIM; dials 0/4 regardless of outcome.**

## What landed

**Support (§1 of the module)** — the genuinely new proof work,
small as scoped:

| Declaration | Content |
|---|---|
| `meanSub_add` | the projection is additive: `meanSub (g + h) = meanSub g + meanSub h` — NOT previously landed (SHADOW-TEST-1's API had shift-invariance and idempotence, not linearity) |
| `meanSub_smul` | the projection is homogeneous: `meanSub (c • g) = c • meanSub g` |
| `laplacianOp_meanSub` | `L` ignores the mean-subtraction of its argument: `laplacianOp w (meanSub F) = laplacianOp w F` (mean-subtraction subtracts a constant; constants are in the kernel) |

**The well-posed core (§2)**:

| Declaration | Content |
|---|---|
| `lapEquiv` (def) | the restriction of `L` to the mean-zero subspace `LinearMap.ker chargeSum` as a **linear equivalence** of that subspace: `LinearEquiv.ofBijective (lapRestrict w hw)`, injectivity consumed whole from T2 §4 (`lapRestrict_injective`), surjectivity by T2 §5's own idiom (`injective_iff_surjective_of_finrank_eq_finrank`) |
| `lapEquiv_apply` | the equivalence applies as the Laplacian: `(lapEquiv w hw hw0 hpos F : V → ℝ) = laplacianOp w (F : V → ℝ)` |
| `lapEquiv_symm_apply` | the inverse undoes `L` on the subspace: `laplacianOp w ((lapEquiv w hw hw0 hpos).symm G : V → ℝ) = (G : V → ℝ)` |

**The Green operator (§3)** — all at `[Nonempty V]`, `hw` /
`hw0` / `hpos` on the face, exactly T2's hypotheses:

| Declaration | Content |
|---|---|
| `greenOp` (def) | the gauged inverse on all sources: project by `meanSub`, invert by `lapEquiv.symm`, read back as a plain (hence mean-zero) function |
| `laplacianOp_greenOp` | **headline 1, right-inverse in projected form:** `laplacianOp w (greenOp w hw hw0 hpos g) = meanSub g`. The unprojected form `= g` is false for `∑ g ≠ 0` and is not stated |
| `sum_greenOp` | **headline 3, the gauge:** `∑ i, greenOp w hw hw0 hpos g i = 0` |
| `eq_greenOp_of` | **the uniqueness characterization:** a mean-zero `u` with `laplacianOp w u = meanSub g` *is* `greenOp … g` — `greenOp` is the unique mean-zero potential for the projected source |
| `greenOp_laplacianOp` | **headline 2, left-inverse on the subspace:** for `∑ i, f i = 0`, `greenOp w hw hw0 hpos (laplacianOp w f) = f` |
| `greenOp_laplacianOp_meanSub` | off the subspace: `greenOp w hw hw0 hpos (laplacianOp w f) = meanSub f` — the gauge discards exactly the constant part |

**Linearity, the ceiling, agreement (§4)**:

| Declaration | Content |
|---|---|
| `greenOp_add` | `greenOp (g + h) = greenOp g + greenOp h` (via `eq_greenOp_of` + `meanSub_add`) |
| `greenOp_smul` | `greenOp (c • g) = c • greenOp g` |
| `greenOp_const` | **headline 5 — K-SR-4 at the operator:** a constant source inverts to the zero potential, `greenOp w hw hw0 hpos (fun _ => c) = 0` |
| `greenOp_meanSub` | **headline 6:** `greenOp (meanSub g) = greenOp g` — the operator factors through the projection, as a theorem about the operator |
| `greenOp_eq_zero_iff` | **headline 8 — the ceiling as an iff:** `greenOp w hw hw0 hpos g = 0 ↔ ∃ c, g = fun _ => c` — the operator's kernel is exactly the constants, the total-mass direction, nothing else |
| `greenOp_eq_meanSub_poissonPotential` | **headline 9 — agreement:** `greenOp w hw hw0 hpos g = meanSub (poissonPotential w hw hw0 hpos g)` — the new object is the landed canonical potential with its gauge fixed; downstream consumers can rewrite between them |
| `sum_mul_greenOp_comm` | **self-adjointness (the scoping's OPTIONAL STRETCH, landed):** for mean-zero `f g`, `∑ i, f i * greenOp w hw hw0 hpos g i = ∑ i, greenOp w hw hw0 hpos f i * g i`, via `laplacianOp_symm_form` |

**Uniqueness characterization, as registered:** existence
(`laplacianOp_greenOp`) + gauge (`sum_greenOp`) + uniqueness
(`eq_greenOp_of`, resting on T2 §4 injectivity) together say
`greenOp … g` is the *unique* mean-zero potential for
`meanSub g`. That triple is the whole content of the word
"well-posed" at this seat; stability needs no statement
(finite-dimensional, and a norm bound is a different brick,
per the scoping's exclusions).

## Kill dispositions

- **K-GREEN-1 (structural) — DID NOT FIRE.** The restriction's
  injectivity is consumed whole from landed T2 §4
  (`lapRestrict_injective` / `eq_zero_of_lapRestrict_eq_zero`);
  no mean-zero kernel element at a fully conducting seat was
  encountered — the equivalence formed on the first attempt.
  (Had it fired, it would have fired *upward* as a T2
  erratum, not as a failure of this brick.)
- **K-GREEN-2 (re-pin) — DID NOT FIRE.** No weaker
  connectivity API was needed or wanted: `hpos` — the seat's
  landed form of connectedness, every pair of vertices
  conducts — is carried verbatim on every headline, with
  `hw` / `hw0`, exactly as scoped.
- **K-GREEN-3 (honesty) — DID NOT FIRE.** No headline needs,
  or contains, gravitational vocabulary; no response law is
  stated anywhere in the module or this dossier. The fence
  above is the whole gravitational content of the brick:
  none.

## Deviations from the scoping note (each with its reason)

1. **The optional symmetry stretch LANDED** (`sum_mul_greenOp_comm`).
   The note priced it as a 5–10-line optional extra, droppable
   without prejudice; the sum manipulations did not resist
   (one `laplacianOp_symm_form` spend after the inverse laws),
   so it is in, inside the band.
2. **The uniqueness characterization landed as a theorem**
   (`eq_greenOp_of`), where the note offered it as optional
   header prose. It earned its line: every §4 headline is
   proved through it, in one or two rewrites each.
3. **Proof routing:** the note's risk-1 mitigation suggested
   routing function-level headlines through the
   `poissonPotential` characterization to dodge subtype
   friction. In the event, the equiv-side uniqueness lemma
   (`eq_greenOp_of`) made the subtype route the cheap one —
   the coercion friction did not materialize (`lapEquiv_apply`
   is a one-step `show` + T2's `lapRestrict_coe`) — and the
   `poissonPotential` tie still lands as headline 9. Headline
   statements are route-independent and match the note
   exactly; only the proof traffic differs.
4. **Count note, on the face:** the note's band arithmetic
   reads "2 defs + ~10–13 theorems … 12–20 strict". The
   landing is 17 theorems + 2 defs: above the note's
   theorem-count *estimate* (the §1 support lemmas, the
   off-subspace corollary, the uniqueness theorem, and the
   stretch all proved worth their lines), but **inside the
   registered band of 20 under both readings** (17
   theorems-only; 19 counting defs as strict units). No
   band-stop was triggered; the excess over the estimate is
   itemized here rather than absorbed silently.

## Not in this brick (per the scoping's exclusions)

A matrix/Green's-function kernel `G i j` with
`greenOp g i = ∑ j, G i j * g j` (formable afterwards from
basis potentials — a separate small brick if ever wanted);
positivity of `greenOp` (false in general for signed sources;
not stated); any norm/continuity statement; the empty seat
(the brick is stated at `[Nonempty V]` on its face, matching
T2 §4's own disposition); continuum anything. SR-4 stays
closed by K-SR-4; SR-1/SR-2/SR-6 stay FRONTIER and untouched;
this brick opens no route and closes none.

**Integration is the parent's:** copy byte-identical, rebuild,
recount, fence admissions with the module's import line in the
same commit (the standing sequencing lesson), ledger record
(draft at `whitepaper/green-operator-ledger-record-DRAFT.json`
in this lane), commit, push, CI verify. Projected census after
integration: 13,340 + 17 = **13,357 strict / 494 modules**,
fence 378 + 17 = **395/395** — projections for the parent to
re-derive, not landed numbers. **NO CLAIM; dials 0/4.**
