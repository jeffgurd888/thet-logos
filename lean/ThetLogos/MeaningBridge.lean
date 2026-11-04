import Mathlib.Tactic

/-!
# ThetLogos.MeaningBridge — pin N1, first formable core: the shape of a meaning kernel

HONESTY LEDGER (read before citing):

- COMMISSION. Jeff's seeing (2026-11-04, T5, filed verbatim in
  `~/memory/2026-11-04.md`): the primordials are mathematics,
  physics, and the correlations of letters and meanings; in
  language words are and do; symbols and glyphs also carry
  meaning; words sometimes have conflated meanings; translated
  words are even worse at precision of grammar; the unified
  language needs to contain every language. Jeff's commission
  chain: "build the bridge of the alignment" → "do all and see"
  (2026-11-04). This module is BRICK 1 of that commission: the
  meaning bridge — pin N1 of the primordials dossier
  (`whitepaper/primordials-exhibit-landing-2026-11-04.md`) at
  the shape Jeff accepted. Brick 2 (the three-primordial
  alignment exhibit) consumes this module's interface; the
  definition names below are FROZEN.
- WHAT THIS MODULE IS. The first formable core of a language,
  formally: a syntax set `S`, a meaning set `M`, and an
  ALIGNMENT relation between them (`MeaningAlign S M`). Jeff's
  observation has exact mathematical content at this shape: a
  "conflated meaning" (one glyph, several meanings — homonymy)
  is the alignment failing to be FUNCTIONAL; several glyphs
  carrying one meaning (synonymy) is the alignment failing to
  be INJECTIVE. The checkable content of the brick is the
  characterization: a unique denotation function — Jeff's
  "mathematical equivalent", a meaning-assignment that can be
  CHECKED — exists if and only if the alignment is functional
  and total (no conflation, no gaps). The conflation witness is
  a theorem shape: a glyph with two distinct aligned meanings
  exists if and only if the alignment is not functional. For a
  denotation function, "same meaning" is an equivalence
  relation on glyphs (the synonym classes), and its quotient
  is the function's range. A first containment seed for the
  "contains every language" constraint is here in its honest
  form: unions of alignments into a common meaning set exist,
  totality survives union, and functionality survives union
  under an exact cross-condition — the naive claim that a union
  of two functional alignments is functional is FALSE, killed
  below by an explicit counterexample (K-MB-1), never smoothed.
- GRADE OF EACH ITEM, ON ITS FACE. DEFINITIONAL items are the
  interface itself — they pin shapes and prove nothing.
  GENERIC items are general facts of the pinned type theory /
  Mathlib grade, true of every relation of this shape; they are
  labeled as such and no seat-specific content is claimed.
- WHAT THIS MODULE IS NOT. It is NOT a semantics for any
  natural language: no glyph in this file is a word, no meaning
  in this file is a meaning of anything in the world; `S` and
  `M` are bare types and the alignment is a bare relation. It
  is NOT a unified language. Pin N2 (meaning vs reference — two
  expressions with equal denotation and different meaning)
  remains OPEN and is untouched by this brick: nothing here
  distinguishes expressions beyond their aligned meanings, and
  the dossier says so again. Jeff's seeing stands at T5 as
  filed; this module is its first formable core and nothing
  more. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

variable {S M : Type*}

/-! ## §1. The interface: a language is syntax, meanings, and an alignment

An alignment is a bare relation. The four predicates name the
four ways Jeff's observations say a language can behave or
fail: conflation (not functional), gaps (not total), synonymy
(not injective), unnamed meanings (not surjective). All of §1
is DEFINITIONAL grade — it pins the shapes Brick 2 consumes. -/

/-- **A language, formally (DEFINITIONAL).** `MeaningAlign S M`
is an alignment between a syntax set `S` (glyphs, letters,
words) and a meaning set `M`: the relation "this glyph carries
this meaning". A transparent alias for a relation — nothing is
asserted by the shape itself. -/
abbrev MeaningAlign (S M : Type*) := S → M → Prop

/-- **No conflation (DEFINITIONAL).** An alignment is
functional when each glyph carries at most one meaning. Its
failure is exactly Jeff's "conflated meanings": one glyph,
several meanings. -/
def MeaningAlign.Functional (A : MeaningAlign S M) : Prop :=
  ∀ s m₁ m₂, A s m₁ → A s m₂ → m₁ = m₂

/-- **No gaps (DEFINITIONAL).** An alignment is total when
every glyph carries at least one meaning. -/
def MeaningAlign.Total (A : MeaningAlign S M) : Prop :=
  ∀ s, ∃ m, A s m

/-- **No synonymy (DEFINITIONAL).** An alignment is injective
when each meaning is carried by at most one glyph. -/
def MeaningAlign.InjectiveAlign (A : MeaningAlign S M) : Prop :=
  ∀ s₁ s₂ m, A s₁ m → A s₂ m → s₁ = s₂

/-- **No unnamed meanings (DEFINITIONAL).** An alignment is
surjective when every meaning is carried by at least one
glyph. -/
def MeaningAlign.SurjectiveAlign (A : MeaningAlign S M) : Prop :=
  ∀ m, ∃ s, A s m

/-! ## §2. The characterization: when a checkable denotation exists

Jeff's "mathematical equivalent" made literal: a denotation
function is a meaning-assignment that can be checked — feed it
a glyph, get THE meaning. This section proves the exact
conditions under which such a function exists: functional and
total, nothing more, nothing less. All GENERIC grade. -/

/-- **The denotation (DEFINITIONAL choice).** When an
alignment is total, `denotationOf` picks, for each glyph, one
of its aligned meanings. Under functionality (§2's theorems)
the pick is forced and is THE meaning; without functionality
the pick is arbitrary among the glyph's meanings — the choice
is in the construction, not hidden. -/
noncomputable def MeaningAlign.denotationOf (A : MeaningAlign S M)
    (hT : A.Total) : S → M :=
  fun s => Classical.choose (hT s)

/-- **The picked meaning is aligned (GENERIC).** Whatever
`denotationOf` picks for a glyph is one of that glyph's
aligned meanings. -/
theorem MeaningAlign.denotationOf_spec (A : MeaningAlign S M)
    (hT : A.Total) (s : S) : A s (A.denotationOf hT s) :=
  Classical.choose_spec (hT s)

/-- **Under no-conflation, aligned = denoted (GENERIC).** If
the alignment is functional and total, a meaning is aligned
to a glyph if and only if it IS the glyph's denotation: the
relation collapses to the graph of one checkable function. -/
theorem MeaningAlign.align_iff_denotation (A : MeaningAlign S M)
    (hF : A.Functional) (hT : A.Total) (s : S) (m : M) :
    A s m ↔ m = A.denotationOf hT s := by
  constructor
  · intro h
    exact hF s m (A.denotationOf hT s) h (A.denotationOf_spec hT s)
  · intro h
    rw [h]
    exact A.denotationOf_spec hT s

/-- **THE CHARACTERIZATION (GENERIC).** An alignment is
functional and total — no conflation, no gaps — if and only
if it is the graph of a denotation function: there is a
function `f` with `A s m ↔ m = f s` throughout. This is the
exact border between a language whose meanings float and one
whose meanings can be checked. -/
theorem MeaningAlign.functional_total_iff (A : MeaningAlign S M) :
    (A.Functional ∧ A.Total) ↔
      ∃ f : S → M, ∀ s m, A s m ↔ m = f s := by
  constructor
  · rintro ⟨hF, hT⟩
    exact ⟨A.denotationOf hT, fun s m => A.align_iff_denotation hF hT s m⟩
  · rintro ⟨f, hf⟩
    constructor
    · intro s m₁ m₂ h₁ h₂
      exact ((hf s m₁).1 h₁).trans ((hf s m₂).1 h₂).symm
    · intro s
      exact ⟨f s, (hf s (f s)).2 rfl⟩

/-- **The denotation is unique (GENERIC).** Under no
conflation and no gaps, the denotation function is not merely
there — it is the only one whose graph is the alignment.
Existence AND uniqueness: the mathematical equivalent, when
it exists, is pinned. -/
theorem MeaningAlign.exists_unique_denotation (A : MeaningAlign S M)
    (hF : A.Functional) (hT : A.Total) :
    ∃! f : S → M, ∀ s m, A s m ↔ m = f s := by
  refine ⟨A.denotationOf hT,
    fun s m => A.align_iff_denotation hF hT s m, ?_⟩
  intro g hg
  funext s
  have hgs : A s (g s) := (hg s (g s)).2 rfl
  exact (A.align_iff_denotation hF hT s (g s)).1 hgs

/-- **No synonymy, read on the denotation (GENERIC).** Under
no conflation and no gaps, the denotation function is
injective if and only if the alignment is injective: synonymy
in the relation and non-injectivity of the checkable function
are the same fact in the two roles. -/
theorem MeaningAlign.denotation_injective_iff (A : MeaningAlign S M)
    (hF : A.Functional) (hT : A.Total) :
    Function.Injective (A.denotationOf hT) ↔ A.InjectiveAlign := by
  constructor
  · intro hinj s₁ s₂ m h₁ h₂
    apply hinj
    exact ((A.align_iff_denotation hF hT s₁ m).1 h₁).symm.trans
      ((A.align_iff_denotation hF hT s₂ m).1 h₂)
  · intro hinj s₁ s₂ h
    exact hinj s₁ s₂ (A.denotationOf hT s₁) (A.denotationOf_spec hT s₁)
      (h ▸ A.denotationOf_spec hT s₂)

/-- **No unnamed meanings, read on the denotation
(GENERIC).** Under no conflation and no gaps, the denotation
function is surjective if and only if the alignment is
surjective. -/
theorem MeaningAlign.denotation_surjective_iff (A : MeaningAlign S M)
    (hF : A.Functional) (hT : A.Total) :
    Function.Surjective (A.denotationOf hT) ↔ A.SurjectiveAlign := by
  constructor
  · intro hsurj m
    obtain ⟨s, hs⟩ := hsurj m
    exact ⟨s, (A.align_iff_denotation hF hT s m).2 hs.symm⟩
  · intro hsurj m
    obtain ⟨s, hs⟩ := hsurj m
    exact ⟨s, ((A.align_iff_denotation hF hT s m).1 hs).symm⟩

/-- **CONFLATION IS EXACTLY NON-FUNCTIONALITY (GENERIC).**
Jeff's observation as a theorem shape: a glyph carrying two
distinct meanings exists if and only if the alignment is not
functional. Conflation is not a mood of a language; it is the
precise failure of one named condition, with a witness. -/
theorem MeaningAlign.conflation_iff_not_functional (A : MeaningAlign S M) :
    (∃ s m₁ m₂, m₁ ≠ m₂ ∧ A s m₁ ∧ A s m₂) ↔ ¬ A.Functional := by
  constructor
  · rintro ⟨s, m₁, m₂, hne, h₁, h₂⟩ hF
    exact hne (hF s m₁ m₂ h₁ h₂)
  · intro h
    by_contra hcon
    apply h
    intro s m₁ m₂ h₁ h₂
    by_contra hne
    exact hcon ⟨s, m₁, m₂, hne, h₁, h₂⟩

/-! ## §3. Synonym classes: "same meaning" is an equivalence

For a denotation function, glyphs fall into classes of equal
denotation — the synonym classes. The relation is an
equivalence, and the quotient (the set of classes) is exactly
the range of the denotation: the meanings that actually occur,
each counted once, with their glyphs collapsed. GENERIC
grade. -/

/-- **Same meaning (DEFINITIONAL).** Two glyphs have the same
meaning under `f` when their denotations agree. -/
def SameMeaning (f : S → M) (s₁ s₂ : S) : Prop := f s₁ = f s₂

/-- **Same-meaning is an equivalence (GENERIC).** Reflexive,
symmetric, transitive — inherited from equality of
denotations, stated in the bridge's vocabulary. -/
theorem SameMeaning.equivalence (f : S → M) :
    Equivalence (SameMeaning f) :=
  ⟨fun _ => rfl, fun h => Eq.symm h, fun h₁ h₂ => Eq.trans h₁ h₂⟩

/-- **The synonym-class setoid (DEFINITIONAL).** The setoid on
glyphs whose classes are the synonym classes of `f`. -/
def sameMeaningSetoid (f : S → M) : Setoid S :=
  ⟨SameMeaning f, SameMeaning.equivalence f⟩

/-- **The classes ARE the occurring meanings (GENERIC).** The
quotient of the syntax by same-meaning is equivalent to the
range of the denotation: collapse each synonym class to its
one meaning, and nothing is lost and nothing is added. -/
noncomputable def quotientSameMeaningEquivRange (f : S → M) :
    Quotient (sameMeaningSetoid f) ≃ Set.range f where
  toFun := Quotient.lift (fun s => ⟨f s, s, rfl⟩)
    (fun a b h => Subtype.ext h)
  invFun := fun x => Quotient.mk (sameMeaningSetoid f)
    (Classical.choose x.2)
  left_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro s
    show Quotient.mk (sameMeaningSetoid f)
        (Classical.choose (⟨f s, s, rfl⟩ : Set.range f).2) = _
    apply Quotient.sound
    exact Classical.choose_spec (⟨f s, s, rfl⟩ : Set.range f).2
  right_inv := by
    intro x
    apply Subtype.ext
    show f (Classical.choose x.2) = x.1
    exact Classical.choose_spec x.2

/-! ## §4. The are/do echo: functions ARE alignments, and meanings can be acted on

In the primordials exhibit, a number both is an object and
does an action. Here, at the bridge's own seat: every function
IS an alignment (its graph — conflation-free and gap-free by
construction), and an action on meanings composes through a
denotation to give another alignment. This section is
DEFINITIONAL grade with one rfl-checked fact each: it pins the
echo, it proves nothing the grammar didn't already say. -/

/-- **A function as an alignment (DEFINITIONAL).** The graph
of `f`: the glyph `s` carries exactly the meaning `f s`. -/
def graphAlign (f : S → M) : MeaningAlign S M :=
  fun s m => m = f s

/-- **Reading the graph (DEFINITIONAL).** A meaning is
graph-aligned to a glyph if and only if it is the glyph's
value under `f` — the definition, checked by `rfl`. -/
theorem graphAlign_apply (f : S → M) (s : S) (m : M) :
    graphAlign f s m ↔ m = f s := Iff.rfl

/-- **Functions never conflate and never gap
(DEFINITIONAL-grade fact).** The graph of any function is
functional and total: passing from a relation to a function
is exactly the step that kills conflation and gaps — §2's
characterization, read backwards. -/
theorem graphAlign_functional_total (f : S → M) :
    (graphAlign f).Functional ∧ (graphAlign f).Total :=
  ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂.symm, fun s => ⟨f s, rfl⟩⟩

/-- **Acting on meanings (DEFINITIONAL).** Given a denotation
`f` and an action `e` on meanings, `actAlign f e` is the
alignment of the composite doing: the glyph denotes, then the
action acts. A glyph both IS (it denotes) and, through the
action, DOES. -/
def actAlign (f : S → M) (e : M → M) : MeaningAlign S M :=
  graphAlign (e ∘ f)

/-- **Reading the acted alignment (DEFINITIONAL).** A meaning
is aligned under the composite if and only if it is the action
applied to the denotation — the definition, by `rfl`. -/
theorem actAlign_apply (f : S → M) (e : M → M) (s : S) (m : M) :
    actAlign f e s m ↔ m = e (f s) := Iff.rfl

/-! ## §5. The containment seed: unions of languages

Jeff's constraint: the unified language must CONTAIN every
language. The honest formable core of containment is union:
two alignments into a COMMON meaning set can always be
united, and the union still names everything either language
named. But containment has a price, and the price is a
theorem, not a hope: the union of two conflation-free
alignments need NOT be conflation-free — two languages that
disagree on a glyph's meaning conflate it in the union. The
exact condition under which functionality survives union is
stated and proved; the naive claim is killed by an explicit
counterexample (K-MB-1). GENERIC grade. -/

/-- **Union of alignments (DEFINITIONAL).** The glyph carries
the meaning if either alignment says so: the smallest
alignment containing both — containment, as a definition. -/
def unionAlign (A B : MeaningAlign S M) : MeaningAlign S M :=
  fun s m => A s m ∨ B s m

/-- **Reading the union (DEFINITIONAL).** Aligned in the union
if and only if aligned in one of the two — by `rfl`. -/
theorem unionAlign_apply (A B : MeaningAlign S M) (s : S) (m : M) :
    unionAlign A B s m ↔ A s m ∨ B s m := Iff.rfl

/-- **Containment keeps every word (GENERIC).** If either
language is total, the union is total: uniting languages
loses no glyph's meaning. -/
theorem unionAlign_total_of_left {A B : MeaningAlign S M}
    (hA : A.Total) : (unionAlign A B).Total := by
  intro s
  obtain ⟨m, hm⟩ := hA s
  exact ⟨m, Or.inl hm⟩

/-- **WHEN UNION PRESERVES NO-CONFLATION (GENERIC).** The
union is functional if and only if both alignments are
functional AND they agree across the seam: any meaning one
assigns to a glyph equals any meaning the other assigns it.
The cross-condition is the whole content — two languages can
each be internally conflation-free and still conflate a glyph
between them. -/
theorem unionAlign_functional_iff {A B : MeaningAlign S M} :
    (unionAlign A B).Functional ↔
      A.Functional ∧ B.Functional ∧
        (∀ s m₁ m₂, A s m₁ → B s m₂ → m₁ = m₂) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro s m₁ m₂ h₁ h₂
      exact h s m₁ m₂ (Or.inl h₁) (Or.inl h₂)
    · intro s m₁ m₂ h₁ h₂
      exact h s m₁ m₂ (Or.inr h₁) (Or.inr h₂)
    · intro s m₁ m₂ h₁ h₂
      exact h s m₁ m₂ (Or.inl h₁) (Or.inr h₂)
  · rintro ⟨hA, hB, hcross⟩ s m₁ m₂ h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact hA s m₁ m₂ h₁ h₂
    · exact hcross s m₁ m₂ h₁ h₂
    · exact (hcross s m₂ m₁ h₂ h₁).symm
    · exact hB s m₁ m₂ h₁ h₂

/-- **K-MB-1: THE NAIVE UNION CLAIM IS FALSE (GENERIC
counterexample).** There are two functional alignments of
`Bool` in `Bool` whose union is not functional: one sends
every glyph to `true`, the other to `false`; each is
conflation-free alone, and their union hands every glyph both
meanings. Stated and proved so the kill is on the record, not
smoothed into the cross-condition above. -/
theorem exists_functional_unionAlign_not_functional :
    ∃ A B : MeaningAlign Bool Bool, A.Functional ∧ B.Functional ∧
      ¬ (unionAlign A B).Functional := by
  refine ⟨fun _ m => m = true, fun _ m => m = false, ?_, ?_, ?_⟩
  · intro _ _ _ h₁ h₂
    exact h₁.trans h₂.symm
  · intro _ _ _ h₁ h₂
    exact h₁.trans h₂.symm
  · intro h
    have hcon := h false true false (Or.inl rfl) (Or.inr rfl)
    exact Bool.noConfusion hcon

end ThetLogos
