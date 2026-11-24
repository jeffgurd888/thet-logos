/-
# TetPrimitivePin — the Tet re-primitivization line (working label)

**Commissioned by Zero, 2026-11-21 00:25 EST ("we need to go back to
Tet and reprimitive"); scope of record:
~/workspace/your_files/tet-reprimitivization-scope-2026-11-21.md.
Lane-grade pin. NO CLAIM. T5; dials 0/4 under every outcome.**

"Reprimitive" is Zero's coinage; this module uses his word and defines
it no further than the audit below supports. A Tet seat, if one is
built here, is a Register-A record construction — it derives nothing,
predicts nothing, and moves no dial. Public naming is Zero's hand;
`TetPrimitivePin` and the brick labels are working labels only.

STANDING LAW (outranks this module; where any brick and the ruling
conflict, the ruling wins and the brick dies):
- The Tet ruling is ABSOLUTE (2026-10-16; restored to its original
  form 2026-11-12, the "most generally" softening withdrawn,
  Tet-brace pin (3) closed): **Tet is the name of the equality, never
  the value.** No Tet-as-value exceptions window exists.
  K-TET-VALUE stands armed over every brick: any construction that
  forces Tet into a value/term/type position dies on contact.
- K-TETE-IDENTITY stands armed: the identity { ⋀ | Ω } = Tet is NOT
  stateable as a theorem; no proof here claims it, ever.
- K-TETE-AXIOM stands armed: the dropped draft's
  `teth_identity_axiom` was REFUTED in-kernel 2026-11-13; no axiom
  asserting a Tet bracket/core/identity may be re-introduced.
- K-T12-NAME stands: "Tet" is occupied in-tree by the Axiom Zero web
  model (`AxiomTet`), an unrelated object.
- Gurd Law (2026-10-02): "Before information can be processed or
  communicated, the boundary must first be drawn and contained";
  corollary (2026-10-06): "the boundary creates identity."

## Brick TET-R0 — the audit card (0 strict by design)

§1 of the scope, carded in-tree. This brick cards the AUDIT — the
base layer as found, Tet's four seats, the gap sentence. It does NOT
card the Tet string: the string stands in its own paper pin
(2026-11-12, pinned to axiom Tet by name, asserting no identity),
and keeping the two distinct on the face is this brick's K-TET-DUP
gate. The registration structure below supplies NO inhabitant: its
fields are labeled registrations of audit facts, in the
`CpecPillarPlanckAbsent` genre — the card asserts nothing.

THE AUDIT, in brief (full text: the scope, §1):
- The compiled primitive layer of the corpus is ONE module,
  `Axioms.lean`: the axioms `Void : Type`, `ThetPair` with
  `thetPair_exists`, the tripotent `N0` with `N0_tripotent`, and the
  definition `linL`. On it stand TRO, the ker-L family, Scaffold32
  (C³²), FiniteSpectralTriple, and everything else (700+ modules on
  Mathlib plus that chain).
- Tet sits NOWHERE in that layer. Its four seats: (i) a NAME
  COLLISION — `AxiomTet` (+ partners) is the Axiom Zero equality-first
  web model (AZ-1/2W/3/5), importing only Mathlib, disjoint from the
  base chain in both directions; (ii) a WITNESSED SHADOW —
  `TetWitnessPin` (9 decls, 3 strict, no axioms): the equation rides
  as a FIELD of `TethWitness`; its header states the fence itself:
  "It does not define Tet, seat Tet, or prove any identity";
  (iii) a NAMED STRING — the 2026-11-12 paper pin, by name, no
  identity asserted, not a Lean module; (iv) a WORKED INSTANCE —
  `tetRuling_reading` inside `ReadingRulePin`: the ruling compiled
  as a worked instance of the reading procedure; Tet is its example,
  not its subject. (Adjacent: the primordials are compiled as
  EXHIBITS — `PrimordialsExhibit`/`PrimordialAlignment` — never as
  base.)
- THE GAP, one sentence: Tet holds a primitive's grade in the record
  but only a witness's seat in the tree — witnessed and named, never
  compiled AS the primitive — and since the absolute ruling forbids
  Tet as value/term/type, the only honest compiled form is
  equality-shaped: a relation the stack stands on.

GRADING NOTE: the scope surfaced a tension in the record (its
Open Item 1): the 2026-11-12 "primitive" verdict was pronounced on
the IF/AND/OR reading rule, while Tet itself was seated that same
day (13:57) at the universal/primordial pole. Zero ruled on
2026-11-21 00:33 EST: RE-GRADE — Tet takes the primitive seat
(universal → primitive). That ruling is carded at Brick TET-R3 of
this module; this brick remains the audit as found.

STATUS: STATUS-TETPRIMITIVE.md.
-/

import Mathlib.Tactic
import ThetLogos.TetWitnessPin
import ThetLogos.Axioms
import ThetLogos.TRO

namespace ThetLogos

/-- **TET-R0 — the audit card.** A registration of the audit's facts,
in the `CpecPillarPlanckAbsent` genre: the fields are labeled
registrations, each opaque — the pin asserts no content for any of
them, and NO INHABITANT IS SUPPLIED. The card fixes the audit as a
record object so later bricks cite it instead of re-litigating it.
It cards the audit, not the Tet string (the string's own paper pin
stands separately, 2026-11-12). -/
structure TetAuditCard where
  /-- Opaque (labeled): the compiled primitive layer is
  `Axioms.lean` alone — `Void`, `ThetPair` + `thetPair_exists`,
  `N0` + `N0_tripotent`, `linL` — and the whole corpus stands on
  Mathlib plus that chain (TRO → ker-L family → Scaffold32 →
  FiniteSpectralTriple → the rest). -/
  baseLayerIsAxioms : Prop
  /-- Opaque (labeled): seat one — a name collision. `AxiomTet`
  (the Axiom Zero web model, AZ-1/2W/3/5) occupies the name "Tet"
  in-tree; it imports only Mathlib and is disjoint from the base
  chain in both directions (K-T12-NAME). -/
  seatNameCollision : Prop
  /-- Opaque (labeled): seat two — a witnessed shadow.
  `TetWitnessPin` cards the notation's formal shadow; the equation
  rides as a field of `TethWitness`, per-instance, never an axiom;
  the pin defines no Tet and proves no identity. -/
  seatWitnessedShadow : Prop
  /-- Opaque (labeled): seat three — a named string. The Tet string
  is pinned to axiom Tet on paper (2026-11-12), attached by name
  under the ruling, asserting no identity; not a Lean module. This
  card is distinct from that pin on its face (K-TET-DUP gate). -/
  seatNamedString : Prop
  /-- Opaque (labeled): seat four — a worked instance.
  `ReadingRulePin` compiles the IF/AND/OR reading rule and carries
  `tetRuling_reading`, the Tet ruling as a worked instance of the
  procedure; Tet is the example, not the subject. -/
  seatWorkedInstance : Prop
  /-- Opaque (labeled): the gap. Tet holds a primitive's grade in
  the record but only a witness's seat in the tree — witnessed and
  named, never compiled AS the primitive; under the absolute
  ruling the only honest compiled form is equality-shaped. -/
  gapWitnessNotPrimitive : Prop

/-- The witnessed seat, as a defined word over owned objects: a
type `Ω` is Tet-witnessed when a `TethWitness` exists at it — the
per-instance inhabitation question `TetWitnessPin` answers at the
Bool seat (yes) and under the empty interaction (no). This is seat
two of the audit, carded in code; it defines no Tet. -/
def TetWitnessedSeat (Ω : Type u) [ThetDomain Ω] : Prop :=
  Nonempty (TethWitness Ω)

/-! ## Brick TET-R1 — the base witness seat: `TetSeat`

The witness vocabulary of `TetWitnessPin`, seated at the BASE of
the chain: this module imports `Axioms` (the primitive layer), and
the seat it defines is the vocabulary the base's successors import.
The delta over `TetWitnessPin` is seating, plus one seat the side
pin does not have: the base's own tripotent (below). The equation
stays a FIELD — the moment it became an axiom or a definition of
Tet, this brick would die (K-TET-VALUE / K-TETE-AXIOM). TetSeat
names where the equality sits, not a thing: under the absolute
ruling, Tet is the name of the equality, never the value. -/

/-- **The Tet seat at the base.** A bracket, a core, and the
equation `meet left right = core_state` carried as a FIELD — data
supplied per instance, never an axiom, never a value. This is
`TethWitness`'s vocabulary seated under the base chain and named,
by Zero's delegation (2026-11-21), `TetSeat`. -/
structure TetSeat (Ω : Type u) [ThetDomain Ω] where
  /-- The bracket: two elements whose interaction holds. -/
  bracket : TethBracket Ω
  /-- The core: an element fixed by meeting itself. -/
  core : TethCore Ω
  /-- The equation, as a field: `meet left right = core_state`. -/
  equation : ThetDomain.meet bracket.left bracket.right = core.core_state

/-- The seat and the witness are one vocabulary: every seat is a
witness. (The conversion pair is the checkable content of the
re-seating — the base seat and the side witness are the same
vocabulary, not two.) -/
def TetSeat.toWitness {Ω : Type u} [ThetDomain Ω] (s : TetSeat Ω) :
    TethWitness Ω :=
  ⟨s.bracket, s.core, s.equation⟩

/-- Every witness seats at the base. -/
def TetSeat.ofWitness {Ω : Type u} [ThetDomain Ω] (w : TethWitness Ω) :
    TetSeat Ω :=
  ⟨w.bracket, w.core, w.equation⟩

/-- The honest pair, re-proved at the base seat (1): **a seat
exists at the named Bool seat** — carried from the witness pin's
Bool witness through the conversion. -/
theorem tetSeat_bool_inhabited : Nonempty (TetSeat Bool) :=
  ⟨TetSeat.ofWitness boolTethWitness⟩

/-- The honest pair, re-proved at the base seat (2): **no seat
exists where the interaction is empty** — no bracket can form, so
no seat can be supplied. Inhabitation stays a per-instance
question, never an axiom. -/
theorem tetSeat_empty_interaction {Ω : Type u} [ThetDomain Ω]
    (h : ∀ a b : Ω, ¬ ThetDomain.interaction a b) :
    ¬ Nonempty (TetSeat Ω) := by
  rintro ⟨s⟩
  exact h s.bracket.left s.bracket.right s.bracket.valid_interaction

/-- Any seat's core is idempotent — the projection of its
fixed-point field, stated for the seat's card. -/
theorem TetSeat.core_idempotent {Ω : Type u} [ThetDomain Ω]
    (s : TetSeat Ω) :
    ThetDomain.meet s.core.core_state s.core.core_state
      = s.core.core_state :=
  s.core.is_fixed_point

/-- The sandwich domain on the base's own matrix carrier (the
carrier of `N0`): meet is the sandwich product `X·Y·X`, and every
pair interacts. -/
instance : ThetDomain (Matrix (Fin 2) (Fin 2) ℝ) where
  meet := fun X Y => X * Y * X
  interaction := fun _ _ => True

/-- **The seat at the base's own tripotent.** `N0`, bracketed with
itself, is its own core: the seat's equation field and the core's
fixed-point field are both discharged by the base's tripotent
axiom `N0_tripotent` itself. The witness vocabulary, seated on the
primitive layer's own objects — the seat this brick exists to add.
(Axcheck note, on the face: this seat's proofs stand on the
corpus's declared T1 primitives `N0` / `N0_tripotent`, exactly as
every base-chain theorem does; the Bool pair above uses no axioms
beyond the standard three — in fact none, like the witness pin's.) -/
noncomputable def tetSeat_N0 : TetSeat (Matrix (Fin 2) (Fin 2) ℝ) where
  bracket := ⟨N0, N0, trivial⟩
  core := ⟨N0, N0_tripotent⟩
  equation := N0_tripotent

/-! ## Brick TET-R2 — one base consumer: the seat on the TRO carrier

The seat, asked to carry weight. The base chain's second link is
TRO: the ternary product `ternaryMat a b c = a * bᴴ * c` on complex
matrices, with associativity proved (`ternaryMat_assoc`,
`ternaryMat_assoc2`). This brick seats the witness vocabulary on
that carrier and reads the seat's equation in TRO's own
vocabulary:

- the TRO carrier gets a `ThetDomain` whose meet is the TRO
  sandwich `ternaryMat a b a` — the ternary product folded through
  its own outer argument, the base's native bracket shape;
- `TetSeat.equation_ternary` reads the seat's `equation` field
  in TRO's vocabulary — the identification step itself, as a
  theorem: the bracket sandwich IS the seat's core. This is the
  consumer content: a base-chain identification (a ternary
  product equal to a named core) supplied by the seat's field
  and by nothing else, with no new axioms;
- the seat is inhabited at the carrier's own unit
  (`tetSeat_tro_one`), and a seat's core is a ternary fixed
  point (`TetSeat.core_ternary_self`).

Nothing here states anything about Tet itself (K-TETE-IDENTITY):
the theorems are about matrices, brackets, and cores. Tet remains
the name of the equality the identification travels through —
never a value in any statement (K-TET-VALUE).

**Priced obstruction, disclosed at full rank (the transport
shortfall).** The brick as scoped also called for TRO
associativity restated at the seat with the identification
composed into it (`TetSeat.transport`). That composition is NOT
banked, because in this Mathlib pin it does not elaborate: every
route that transports the seat's equation under a `ternaryMat`
application over seat projections — `rw` (goal, hypothesis,
`conv`-focused, `simp only`), `congrArg` / `Eq.trans` chains,
destructured seats, guided `calc` steps — exceeds the
per-command heartbeat budget (200k) at `whnf` / `isDefEq`; at
unlimited heartbeats the nested conversion
`ThetDomain.meet L R ≡ ternaryMat L R L` over projections burned
>800 CPU-seconds and returned a type mismatch (bisected across
eleven probes, 2026-11-22). Even the bare associativity
restated at the seat's elements (`exact ternaryMat_assoc`)
proved context-unstable for the same defeq reason. What IS
banked is the identification itself (`equation_ternary`) — the
step that is the seat's own contribution; the associativity it
was to ride on remains TRO's, cited and un-re-proved
(K-TET-DUP discipline). Closing the transport is a
formulation/pin problem, priced here, not a content gap in the
seat. -/

/-- The TRO domain on the base's complex-matrix carrier: meet is
the TRO sandwich `ternaryMat a b a`, and every pair interacts.
This is the domain the seat must carry weight on — the base
chain's own ternary product, folded to a binary meet. -/
instance {n : ℕ} : ThetDomain (Matrix (Fin n) (Fin n) ℂ) where
  meet := fun a b => ternaryMat a b a
  interaction := fun _ _ => True

/-- The TRO domain's meet IS the TRO sandwich, stated once so the
seat's equation field can be read in TRO's own vocabulary. -/
theorem troDomain_meet {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) :
    ThetDomain.meet a b = ternaryMat a b a :=
  rfl

/-- **The identification step, in TRO's vocabulary.** The seat's
`equation` field, read through `troDomain_meet`: the bracket
sandwich IS the core. This is the step the whole brick travels
through — the base chain's identification of a ternary product
with a named core, supplied by the seat and by nothing else. -/
theorem TetSeat.equation_ternary {n : ℕ}
    (s : TetSeat (Matrix (Fin n) (Fin n) ℂ)) :
    ternaryMat s.bracket.left s.bracket.right s.bracket.left
      = s.core.core_state := by
  rw [← troDomain_meet]
  exact s.equation

/-- A seat's core, read in TRO's vocabulary, is a ternary fixed
point — the projection of its fixed-point field through the TRO
domain's meet. -/
theorem TetSeat.core_ternary_self {n : ℕ}
    (s : TetSeat (Matrix (Fin n) (Fin n) ℂ)) :
    ternaryMat s.core.core_state s.core.core_state s.core.core_state
      = s.core.core_state := by
  rw [← troDomain_meet]
  exact s.core.is_fixed_point

/-- The unit bracket at the TRO carrier: the identity matrix
bracketed with itself (every pair interacts in this domain). -/
def troBracketOne {n : ℕ} :
    TethBracket (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨1, 1, trivial⟩

/-- The unit core at the TRO carrier: the identity matrix, fixed
by the domain's meet — its ternary self-product is itself,
`ternaryMat 1 1 1 = 1`, read through `troDomain_meet`. -/
def troCoreOne {n : ℕ} :
    TethCore (Matrix (Fin n) (Fin n) ℂ) where
  core_state := 1
  is_fixed_point := by
    rw [troDomain_meet]
    simp [ternaryMat]

/-- **The seat at the TRO carrier's own unit.** The identity
matrix, bracketed with itself, is its own core: the seat's
equation field is the unit's ternary self-product
`ternaryMat 1 1 1 = 1`, read through `troDomain_meet`. The seat
is inhabited at the base chain's own objects, not only at the
Bool side seat. -/
def tetSeat_tro_one {n : ℕ} : TetSeat (Matrix (Fin n) (Fin n) ℂ) where
  bracket := troBracketOne
  core := troCoreOne
  equation := by
    rw [troDomain_meet]
    simp [ternaryMat, troBracketOne, troCoreOne]

/-! ## Brick TET-R3 — the grading card

Zero's ruling of 2026-11-21 00:33 EST, carded in-tree beside the
seat it grades: **RE-GRADE — Tet takes the PRIMITIVE seat
(universal → primitive), equality-shaped only.** Before that
ruling the record carried Tet at the opposite pole: the
2026-11-12 seating ("it is just universal Tet") placed Tet at
the universal/primordial seat — the ground the record stands
on, never compiled. The re-grade moves the seat, not the
ruling: Tet remains the name of the equality, never the value
(K-TET-VALUE); what changes is that the equality now has a
compiled seat in the base layer (Bricks R1–R2) instead of only
a witness at a side seat and a name on paper.

The grade, as a proposition: at a domain, Tet is graded
primitive when the seat is inhabited there — the equality the
domain's identifications travel through is supplied by a
compiled `TetSeat`, per instance, its equation a field. The
two holding theorems below exhibit the grade at the seats this
module has built: the named Bool seat (R1's honest pair) and
the base chain's TRO carrier (R2's consumer seat). The base's
own tripotent seat (`tetSeat_N0`, R1) carries the same grade
on its face; it is not re-exhibited by a theorem here because
its proofs stand on the corpus's declared T1 primitives `N0` /
`N0_tripotent`, as disclosed at R1 — this brick's theorems are
kept to the standard three axioms.

DISTINCTION (this brick's K-TET-DUP gate): `ReadingRulePin`'s
`tetRuling_reading` cards the Tet RULING as a worked instance
of the IF/AND/OR reading procedure — the ruling as procedure.
This brick cards the GRADE — the seat's rank in the record,
primitive in place of universal — and its holding is seat
inhabitation, a different claim about a different object. -/

/-- **The grade, as a proposition.** At a domain `Ω`, Tet is
graded primitive when the equality seat is inhabited there: a
compiled `TetSeat Ω` exists, its equation carried as a field,
supplied per instance. This is the 2026-11-21 re-grade
(universal → primitive) stated as the seat's inhabitation —
the grade attaches to the seat, never to a value: there is no
Tet term here to grade (K-TET-VALUE). -/
def TetGradedPrimitive (Ω : Type u) [ThetDomain Ω] : Prop :=
  Nonempty (TetSeat Ω)

/-- **The grade holds at the named Bool seat.** R1's honest
pair seated a witness at Bool; the grade attaches to that seat
as it stands. -/
theorem tetGradedPrimitive_bool : TetGradedPrimitive Bool :=
  tetSeat_bool_inhabited

/-- **The grade holds at the base chain's TRO carrier.** The
seat R2 built on the ternary product's own matrices carries
the grade: the base chain's identifications travel through a
compiled, graded seat. -/
theorem tetGradedPrimitive_tro {n : ℕ} :
    TetGradedPrimitive (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨tetSeat_tro_one⟩

end ThetLogos
