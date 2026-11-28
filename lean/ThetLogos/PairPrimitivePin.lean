import Mathlib.Tactic

/-!
# ThetLogos.PairPrimitivePin — the pair primitive, registered (T5 doctrine; finite shadow T1-or-kill)

Working label only — naming is Zero's hand. The root ruling,
verbatim, Zero 2026-11-26 19:36 EST: "Rule it — the pair is
the primitive." Guardrail, in Zero's words (2026-11-26
19:38 EST): "not one theorem, not one Lean name, not one
line of the census." Root statement of record:
`~/workspace/your_files/pair-primitive-root-statement-DRAFT-2026-11-26.md`.
Scope of record:
`~/workspace/your_files/pair-primitive-pin-scope-DRAFT-2026-11-26.md`.
Fired by Zero's word, 2026-11-26 19:40 EST ("fire it";
"build it and run the gauntlet") — this lane only.

TIER: the root ruling is T5 DOCTRINE. This pin tests the
ruling's FINITE SHADOW only, T1-or-kill like every pin: a
pass does not prove the doctrine, and a kill bounds the
root reading at the finite level and banks at proof rank.
NO CLAIM. No dial moves; dials 0/4 under every outcome.

## The official statement (pinned verbatim at this brick)

**The balance locus coincides with the identity locus:
∀ x : Ω, q x = 0 ↔ gen x = x.**

The finite shadow of the ruling: what is balanced is
exactly what stands; what stands is exactly what is
balanced. Registered below as `pairCoincidence`, in
statement form only. Nothing about it is claimed in this
brick: Brick 1 computes a small exhibit, Brick 2 proves
the coincidence on the registered seat class — or
K-PAIR-BALANCE fires.

## Registered seat class (fixed at the build commission, on the face)

The seat is the **pair seat**: a configuration is itself
an adjoint pair `p = (a, b)` over a base `α`; the
generation face is the **face-exchange**
`gen (a, b) = (b, a)`; the charge is the pair's imbalance
`q (a, b) = a − b`. Then the identity locus is the
diagonal {a = b} — the Tet seat, equality itself — and
the balance locus is {a − b = 0}.

Formalisation decisions, stated openly:

- **No wrapper type.** The seat is literally `α × α`, so
  the diagonal is literally `p.1 = p.2` and no unfolding
  layer stands between the registration and Brick 2's
  proof.
- **The reading, and why faithfulness is constitutive.**
  The base's elements carry integer values through a
  reading `v : α → ℤ`, and the registered charge is
  `q (a, b) = v a − v b` — the faces' OWN integer
  difference, as the scope fixes it. A difference
  `a − b` presupposes that the faces are their integer
  values, so the registered class is the pair seats over
  a **faithful** reading: `Function.Injective v`. The
  canonical instances are the Fin-lifted base
  (`v i = (i.val : ℤ)`) and any base embedded in ℤ. An
  unfaithful reading — two distinct faces with one
  integer value — is not a re-aiming this line permits:
  it changes `q` itself, and the scope forbids re-aiming
  `gen` or `q` mid-line. The pinned statement therefore
  carries faithfulness as its stated hypothesis, on the
  face, not as a silent narrowing: `pairCoincidence v`
  is the claim `Injective v → ∀ p, balanced ↔ identity`.
  Finiteness is NOT needed by the coincidence itself
  (Brick 2 proves it for every base and faithful
  reading); finiteness enters at Brick 1's exhibit,
  where the loci are listed.

## Kills pre-registered (armed by this registration, not fired by it)

- **K-PAIR-BALANCE** — if any configuration is balanced
  but moved by generation (q x = 0 with gen x ≠ x), or
  fixed but unbalanced (gen x = x with q x ≠ 0), the
  coincidence is DEAD at the finite level, and the kill
  banks at the same rank as a proof. No re-aiming `gen`
  or `q` mid-line without a new scope and Zero's word.

## Walls named on the face

- The pin tests a *shadow* of the ruling, not the ruling
  (L2/L3 discipline): a finite coincidence neither
  establishes the doctrine as physics nor a continuum
  claim.
- **S-1 does not govern here** — no centre is picked out.
  But if a later brick turns the identity locus into a
  picked-out object, S-1's jurisdiction attaches and the
  brick dies on it.

## Brick 0's charge

Definitions and the pinned statement ONLY: 0 strict by
design. Names frozen at this brick: `pairGen`,
`pairCharge`, `pairBalanced`, `pairIdentity`,
`pairCoincidence`.
-/

namespace ThetLogos

/-- **The generation face: face-exchange.** One step of
generation on the pair seat swaps the pair's two faces:
`gen (a, b) = (b, a)`. The pair in action, in the
registration's minimal form — the dynamic face of the
adjoint pair, with no further structure imposed. -/
def pairGen {α : Type*} (p : α × α) : α × α :=
  (p.2, p.1)

/-- **The charge: the pair's imbalance.** Through the
base's integer reading `v : α → ℤ`, the pair `(a, b)`
carries charge `v a − v b` — the faces' own integer
difference, exactly as the registered seat class fixes
it. Zero charge is balance: the two faces level. -/
def pairCharge {α : Type*} (v : α → ℤ) (p : α × α) : ℤ :=
  v p.1 - v p.2

/-- **The balance locus, as a predicate.** A pair is
balanced when its imbalance vanishes: `v a − v b = 0`.
Registered as a `Prop` so the pinned statement and
K-PAIR-BALANCE speak about the same set of
configurations. -/
def pairBalanced {α : Type*} (v : α → ℤ) (p : α × α) : Prop :=
  pairCharge v p = 0

/-- **The identity locus, as a predicate.** A pair stands
— is identical to itself under generation — when the
face-exchange fixes it: `gen p = p`. On the pair seat
this is the diagonal, the Tet seat: equality itself,
registered as a `Prop` in the same vocabulary as the
balance locus. -/
def pairIdentity {α : Type*} (p : α × α) : Prop :=
  pairGen p = p

/-- **THE OFFICIAL STATEMENT, pinned as the line's
target.** The balance locus coincides with the identity
locus: on a pair seat over a faithfully-read base
(`Function.Injective v` — the registered class, stated
on the face in the header), every configuration is
balanced if and only if it stands:
`∀ p, pairBalanced v p ↔ pairIdentity p`. Stated in
statement form only; nothing about it is claimed in this
brick. Brick 2's charge is the theorem — or
K-PAIR-BALANCE, each a landing at the same volume. -/
def pairCoincidence {α : Type*} (v : α → ℤ) : Prop :=
  Function.Injective v → ∀ p : α × α, pairBalanced v p ↔ pairIdentity p

/-!
## Brick 1 — the exhibit (appended at Brick 1's banking)

The smallest concrete seat, computed end to end. The base
is `Fin 3` under its canonical Fin-lifted reading
`i ↦ (i.val : ℤ)` — a faithful reading, an instance of
the registered class. The two loci are registered as
`Finset`s over the whole seat so they can be LISTED, not
just predicated: Brick 1 lists both and reads the
coincidence off the listings. The listings are computed
by kernel `decide` over `ℤ`/`Fin` arithmetic — the
house-proven route (kernel `decide` does not reduce on
`Rat` goals in this pin; nothing here is a `Rat` goal).
-/

/-- **The balance locus, as a listed set.** On a finite
seat, the balanced configurations collected as a
`Finset`: every pair whose imbalance vanishes. The
listing form of `pairBalanced`, so an exhibit can put
the locus on the page. -/
def pairBalanceLocus {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℤ) : Finset (α × α) :=
  Finset.univ.filter (fun p => pairCharge v p = 0)

/-- **The identity locus, as a listed set.** On a finite
seat, the standing configurations collected as a
`Finset`: every pair the face-exchange fixes. The
listing form of `pairIdentity` — the diagonal, listed. -/
def pairIdentityLocus {α : Type*} [Fintype α] [DecidableEq α] :
    Finset (α × α) :=
  Finset.univ.filter (fun p => pairGen p = p)

/-- **The exhibit seat's reading.** The canonical
Fin-lifted reading of `Fin 3`: `i ↦ (i.val : ℤ)`. It is
faithful (`Fin.val` is injective and the lift to `ℤ`
preserves that), so the exhibit seat is an instance of
the registered class. -/
def pairExhibitReading : Fin 3 → ℤ :=
  fun i => (i.val : ℤ)

/-- **The exhibit's balance locus, listed.** On the
`Fin 3` seat under its canonical reading, the balanced
pairs are exactly the three diagonal pairs — computed
by kernel `decide`, the whole seat enumerated. -/
theorem pairBalanceLocus_fin3 :
    pairBalanceLocus pairExhibitReading = {(0, 0), (1, 1), (2, 2)} := by
  decide

/-- **The exhibit's identity locus, listed.** On the
`Fin 3` seat, the pairs the face-exchange fixes are
exactly the same three diagonal pairs — computed by
kernel `decide`, the whole seat enumerated. -/
theorem pairIdentityLocus_fin3 :
    pairIdentityLocus (α := Fin 3) = {(0, 0), (1, 1), (2, 2)} := by
  decide

/-- **The exhibit's coincidence, read off the
listings.** The two listed loci of the `Fin 3` seat are
the same `Finset` — Brick 1's landing: on the exhibit
seat, what is balanced is exactly what stands, seen
element by element. (The general theorem is Brick 2's
charge; this is the exhibit, not the proof.) -/
theorem pairExhibit_coincide :
    pairBalanceLocus pairExhibitReading = pairIdentityLocus := by
  rw [pairBalanceLocus_fin3, pairIdentityLocus_fin3]

/-!
## Brick 2 — the verdict (appended at Brick 2's banking)

The coincidence, proved on the whole registered seat
class — every base `α`, every faithful reading `v`. The
proof walks the diagonal from both sides: the identity
locus IS the diagonal (`pairGen_eq_iff`), and under a
faithful reading the balance locus is the same diagonal
(`pairBalanced_iff` — imbalance `v a − v b = 0` iff
`v a = v b` iff, faithfulness, `a = b`). The two loci
meet at equality itself, which is the finite shadow's
whole content: the Tet seat is where balance and
identity are the same seat. K-PAIR-BALANCE does not
fire; no counterexample exists on the registered class,
because a balanced-but-moved pair would be a pair with
`v a = v b` and `a ≠ b` — exactly what faithfulness
excludes, and exactly the re-aiming of `q` the scope
forbids. The Fin-lifted seats (Brick 1's exhibit class)
are discharged as standing instances
(`pairFin_coincidence`).
-/

/-- **The identity locus is the diagonal.** A pair
stands under the face-exchange if and only if its two
faces are equal: `gen p = p ↔ p.1 = p.2`. The identity
face of the pair, characterised outright — no reading,
no hypothesis: face-exchange fixes exactly the pairs
that are already level. -/
theorem pairGen_eq_iff {α : Type*} (p : α × α) :
    pairIdentity p ↔ p.1 = p.2 := by
  constructor
  · intro h
    exact (Prod.ext_iff.mp h).2
  · intro h
    show pairGen p = p
    exact Prod.ext_iff.mpr ⟨h.symm, h⟩

/-- **The balance locus is the same diagonal, under a
faithful reading.** If `v` reads the base faithfully
into `ℤ`, a pair is balanced if and only if its faces
are equal: `v a − v b = 0 ↔ a = b`. The subtraction
vanishes exactly when the readings agree, and
faithfulness is exactly the agreement of the faces
themselves. This is the step where the registered
class's one hypothesis does its work — stated on the
face at Brick 0, discharged here. -/
theorem pairBalanced_iff {α : Type*} (v : α → ℤ) (hv : Function.Injective v)
    (p : α × α) : pairBalanced v p ↔ p.1 = p.2 := by
  show v p.1 - v p.2 = 0 ↔ p.1 = p.2
  rw [sub_eq_zero]
  exact hv.eq_iff

/-- **The Fin-lifted reading is faithful.** For every
`n`, the canonical reading `i ↦ (i.val : ℤ)` of `Fin n`
is injective — `Fin.val` is injective and the lift of a
natural to `ℤ` preserves that. So every Fin-lifted pair
seat, Brick 1's exhibit seat included, is an instance
of the registered class. -/
theorem pairFinReading_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => (i.val : ℤ)) :=
  Int.ofNat_injective.comp Fin.val_injective

/-- **THE VERDICT: the pinned statement, proved.**
`pairCoincidence` holds on the whole registered seat
class: for every base and every faithful reading, every
pair is balanced if and only if it stands. Both loci
are the diagonal (`pairBalanced_iff`,
`pairGen_eq_iff`), so they coincide — the finite
shadow of the root ruling, landed as a theorem.
K-PAIR-BALANCE does not fire. -/
theorem pairCoincidence_holds {α : Type*} (v : α → ℤ) : pairCoincidence v :=
  fun hv p => Iff.trans (pairBalanced_iff v hv p) (pairGen_eq_iff p).symm

/-- **The coincidence on every Fin-lifted seat, as a
standing instance.** For every `n` and every pair over
`Fin n` under the canonical reading, balanced ⟺
standing — the exhibit class of Brick 1 promoted from
a computed listing to a proved instance of the general
theorem. -/
theorem pairFin_coincidence (n : ℕ) :
    ∀ p : Fin n × Fin n,
      pairBalanced (fun i : Fin n => (i.val : ℤ)) p ↔ pairIdentity p :=
  pairCoincidence_holds _ (pairFinReading_injective n)

end ThetLogos
