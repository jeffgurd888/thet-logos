import ThetLogos.NavierStokesClaimPin

namespace ThetLogos

/-!
# ThetLogos.NavierStokesClaimClassify — claim-tester classification (CT-1)

Board charter: **NO CLAIM.** Parts of the Clay Navier–Stokes
problem closed by this house: **0**. This module proves the
classification half of the claim-tester model whose interface is
frozen in `ThetLogos.NavierStokesClaimPin` (CT-0): **Q1** (which
alternative does a candidate claim purport to settle, and which
does it match) and **Q2** (in which shape — exact match with the
pin's shape, or which parameters mismatch), as theorems about the
descriptor, decided by computation on the finite descriptor
space. Q3 (the smuggled negation step) is CT-2's half, in
`ThetLogos.NavierStokesClaimSteps`.

The headline verdicts, all proved below:

- a candidate shape matches an alternative **iff** it equals the
  pin's shape for that alternative, field by field
  (`nsShapeMismatches_eq_nil_iff`, `nsMatchedAlt_eq_some_iff`,
  `nsClassify_eq_matchesPin_iff`);
- a shape whose viscosity regime is `fixedGlobal` — one fixed
  `ν > 0` shared by all alternatives, Fefferman's ambient
  reading — matches **NO** alternative as pinned, and `wrongNu`
  is always in its mismatch list (`nsFixedGlobal_ne_pinShape`,
  `nsClassify_fixedGlobal`). This is the mismatch half of the
  board's ν finding: the pin quantifies `ν` inside each
  alternative, so a claim stated at a single shared viscosity is
  not a claim of any alternative as pinned, whatever else it is;
- the worked exhibits (`nsClassify_septemberShape`,
  `nsClassify_forcingMismatchShape`) run the classifier on named
  shapes: a (C)-claim in the September-claim shape (ν ambient)
  classifies as `mismatch [wrongNu]`, and an (A)-claim over all
  admissible forcing classifies as `mismatch [wrongForcing]`.

Everything here is about claim SHAPES — finite descriptors —
not about Navier–Stokes. K-NS-1 discipline: no alternative is
asserted non-vacuous; nothing here is existence content.

Honesty tiers in this file:
- **T1 (proved):** the classification theorems — about the
  model's descriptors, not about Navier–Stokes.
- **NO CLAIM:** existence, smoothness, breakdown — untouched.
-/

/-- The pin's shape for an alternative purports that alternative:
the `alt` field of `nsPinShape a` is `a`. -/
theorem nsPinShape_alt (a : NSAlt) : (nsPinShape a).alt = a := by
  cases a <;> rfl

/-- The pin's shape for an alternative carries that alternative's
domain. -/
theorem nsPinShape_dom (a : NSAlt) : (nsPinShape a).dom = nsAltDom a := by
  cases a <;> rfl

/-- Every pin shape has `ν` quantified inside — the composition
choice of `NavierStokesStatement`, on which the mismatch verdict
for ambient-ν claims rests. -/
theorem nsPinShape_nu (a : NSAlt) : (nsPinShape a).nu = .quantifiedInside := by
  cases a <;> rfl

/-- The pin's own shape for an alternative has NO mismatches
against itself. -/
theorem nsShapeMismatches_pinShape (a : NSAlt) :
    nsShapeMismatches (nsPinShape a) = [] := by
  cases a <;> rfl

/-- The pin's own shape classifies as an exact match. -/
theorem nsClassify_pinShape (a : NSAlt) :
    nsClassify (nsPinShape a) = .matchesPin := by
  cases a <;> rfl

/-- **Q2, the iff:** a candidate shape's mismatch list is empty
iff the shape equals the pin's shape for its purported
alternative — field-by-field equality is exactly
no-mismatch. -/
theorem nsShapeMismatches_eq_nil_iff (s : NSClaimShape) :
    nsShapeMismatches s = [] ↔ s = nsPinShape s.alt := by
  obtain ⟨a, d, n, f, m⟩ := s
  cases a <;> cases d <;> cases n <;> cases f <;> cases m <;> decide

/-- **Q1+Q2, the iff:** a candidate shape classifies as an exact
match iff it equals the pin's shape for its purported
alternative. -/
theorem nsClassify_eq_matchesPin_iff (s : NSClaimShape) :
    nsClassify s = .matchesPin ↔ s = nsPinShape s.alt := by
  obtain ⟨a, d, n, f, m⟩ := s
  cases a <;> cases d <;> cases n <;> cases f <;> cases m <;> decide

/-- **Q1, the iff:** a candidate shape matches alternative `a`
iff it equals the pin's shape for `a` (in particular `a` is then
its purported alternative). -/
theorem nsMatchedAlt_eq_some_iff (s : NSClaimShape) (a : NSAlt) :
    nsMatchedAlt s = some a ↔ s = nsPinShape a := by
  obtain ⟨a', d, n, f, m⟩ := s
  cases a' <;> cases a <;> cases d <;> cases n <;> cases f <;> cases m <;> decide

/-- **The headline mismatch verdict:** a shape with viscosity
regime `fixedGlobal` equals NO pin shape — it matches no
alternative as pinned, whatever its other parameters say. -/
theorem nsFixedGlobal_ne_pinShape (s : NSClaimShape)
    (hs : s.nu = .fixedGlobal) (a : NSAlt) : s ≠ nsPinShape a := by
  intro h
  have hnu : s.nu = (nsPinShape a).nu := by rw [h]
  rw [nsPinShape_nu] at hnu
  rw [hs] at hnu
  exact NSNuRegime.noConfusion hnu

/-- **The headline mismatch verdict, classified:** a
`fixedGlobal` shape classifies as a mismatch, and `wrongNu` is
on its mismatch list. -/
theorem nsClassify_fixedGlobal (s : NSClaimShape)
    (hs : s.nu = .fixedGlobal) :
    ∃ ms, nsClassify s = .mismatch ms ∧ .wrongNu ∈ ms := by
  have hne : nsShapeMismatches s ≠ [] := by
    intro h
    rw [nsShapeMismatches_eq_nil_iff] at h
    exact nsFixedGlobal_ne_pinShape s hs s.alt h
  unfold nsClassify
  cases hm : nsShapeMismatches s with
  | nil => exact absurd hm hne
  | cons x xs =>
      refine ⟨x :: xs, rfl, ?_⟩
      have hmem : NSMismatch.wrongNu ∈ nsShapeMismatches s := by
        unfold nsShapeMismatches
        have hp : (nsPinShape s.alt).nu = .quantifiedInside := nsPinShape_nu s.alt
        rw [hs, hp]
        simp
      rw [hm] at hmem
      exact hmem

/-- **Exhibit — the September-claim shape:** a (C)-claim stated
at one ambient viscosity (domain, forcing regime, and mode all
as pinned for (C)) classifies as `mismatch [wrongNu]` — the ν
regime is its ONLY mismatch, and it is decisive: as pinned, the
claim matches no alternative. (Shape exhibit only: this is the
tester's verdict on a descriptor, not a verdict on any actual
claim's mathematics.) -/
theorem nsClassify_septemberShape :
    nsClassify ⟨.C, .r3, .fixedGlobal, .allAdmissible, .breakdown⟩
      = .mismatch [.wrongNu] := rfl

/-- **Exhibit — a forcing-regime mismatch:** an (A)-claim over
all admissible forcing ((A) as pinned fixes `f ≡ 0`) classifies
as `mismatch [wrongForcing]`. -/
theorem nsClassify_forcingMismatchShape :
    nsClassify ⟨.A, .r3, .quantifiedInside, .allAdmissible, .existence⟩
      = .mismatch [.wrongForcing] := rfl

/-- **Exhibit — a domain mismatch:** a (B)-claim stated on ℝ³
((B) as pinned lives on the torus) classifies as
`mismatch [wrongDomain]`. -/
theorem nsClassify_domainMismatchShape :
    nsClassify ⟨.B, .r3, .quantifiedInside, .zeroOnly, .existence⟩
      = .mismatch [.wrongDomain] := rfl

/-- **Exhibit — exact pins classify clean:** the pin's shape
for (C) classifies as `matchesPin`, and is matched to (C). -/
theorem nsMatchedAlt_pinShapeC :
    nsMatchedAlt (nsPinShape .C) = some .C := rfl

end ThetLogos
