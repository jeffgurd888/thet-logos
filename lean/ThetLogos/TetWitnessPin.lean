/-
# TetWitnessPin — the Tet-brace notation, witnessed (Register-A record pin)

**Commissioned by Zero, 2026-11-13, reopening Tet-brace
pin (2) in its REPAIRED form (scope:
~/workspace/your_files/tet-witness-pin-scope-2026-11-13.md).
NO CLAIM. Dial-ineligible. Register-A record pin.**

THE FENCE (Zero's ruling, ABSOLUTE): Tet is the name
of the equality, never the value. This pin cards the
notation's formal shadow — a domain vocabulary (a
meet, an interaction predicate), a bracket, a core,
and a witness structure that carries the equation
`meet left right = core` as a FIELD. It does not
define Tet, seat Tet, or prove any identity. The
identity { ⋀ | Ω } = 𐤈 is NOT claimed and NOT
stateable as a theorem; K-TETE-IDENTITY stands armed.

NO AXIOM IS INTRODUCED. The dropped Gemini draft's
`teth_identity_axiom` — which asserted a bracket and
a core with the equation outright — is REFUTED
(kernel-checked, 2026-11-13: at the Unit instance
with the interaction identically False it derives
False) and is cited here only as the refuted form.
K-TETE-AXIOM stands armed against its re-introduction
in any form.

What the pin proves is the honest pair: a witness
EXISTS at one named finite seat (Bool, §2), and a
witness is IMPOSSIBLE at any seat whose interaction
is empty (§3) — inhabitation is a per-instance
question, never an axiom. A witness's core is
idempotent by projection (§3).

STATUS: STATUS-TETWITNESS.md.
-/

namespace ThetLogos

/-! ## §1 — the domain vocabulary (the dropped draft's, repaired) -/

/-- A thet-domain: a carrier with a meet operation and
an interaction predicate. (The draft's vocabulary,
adopted as Register-A design; the draft's axiom is
not adopted — see the header.) -/
class ThetDomain (Ω : Type u) where
  /-- The bracket operation (the draft's meet). -/
  meet : Ω → Ω → Ω
  /-- The interaction predicate (the draft's bar). -/
  interaction : Ω → Ω → Prop

/-- A bracket: two elements of the domain whose
interaction holds. -/
structure TethBracket (Ω : Type u) [ThetDomain Ω] where
  left : Ω
  right : Ω
  valid_interaction : ThetDomain.interaction left right

/-- A core: an element fixed by meeting itself. -/
structure TethCore (Ω : Type u) [ThetDomain Ω] where
  core_state : Ω
  is_fixed_point : ThetDomain.meet core_state core_state = core_state

/-- A witness: a bracket and a core, with the equation
`meet left right = core_state` carried as a FIELD —
data to be supplied per instance, never an axiom. -/
structure TethWitness (Ω : Type u) [ThetDomain Ω] where
  bracket : TethBracket Ω
  core : TethCore Ω
  equation : ThetDomain.meet bracket.left bracket.right = core.core_state

/-! ## §2 — the named finite seat: a witness exists -/

/-- The Bool seat: meet is `&&`, and every pair
interacts. -/
instance : ThetDomain Bool where
  meet := fun a b => a && b
  interaction := fun _ _ => True

/-- The explicit Bool witness: `false` brackets with
itself and is its own core (`false && false = false`
by computation). -/
def boolTethWitness : TethWitness Bool where
  bracket := ⟨false, false, trivial⟩
  core := ⟨false, rfl⟩
  equation := rfl

/-- **A witness is inhabited at the Bool seat.** -/
theorem tethWitness_bool_inhabited : Nonempty (TethWitness Bool) :=
  ⟨boolTethWitness⟩

/-! ## §3 — the other direction, and the core projection -/

/-- **No witness exists under the empty interaction:**
if no pair interacts, no bracket — hence no witness —
can be formed. -/
theorem tethWitness_empty_interaction {Ω : Type u} [ThetDomain Ω]
    (h : ∀ a b : Ω, ¬ ThetDomain.interaction a b) :
    ¬ Nonempty (TethWitness Ω) := by
  rintro ⟨w⟩
  exact h w.bracket.left w.bracket.right w.bracket.valid_interaction

/-- Any witness's core is idempotent — the projection
of its fixed-point field, stated for the card. -/
theorem TethWitness.core_idempotent {Ω : Type u} [ThetDomain Ω]
    (w : TethWitness Ω) :
    ThetDomain.meet w.core.core_state w.core.core_state
      = w.core.core_state :=
  w.core.is_fixed_point

end ThetLogos
