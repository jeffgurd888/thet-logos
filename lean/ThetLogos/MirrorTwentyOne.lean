/-
# MIRROR-21 — the mirror involution on `Fin 21` (core brick)

Brick: MIRROR-21 core (Jeff's commission, 2026-11-02 20:09 EST:
"report it scope it build it run it"). Origin: a Lean+Python
sketch Jeff dropped the same evening (a "21-element involution
algebra" plus a heat-kernel engine). The parent audit of that
sketch returned HOLD: the Lean as dropped does not compile
(both of its lemmas fail at `ext`, because the plain `def`
alias `ManifoldIndex := Fin 21` hides `Fin`'s extensionality
lemma), its `CentralInvolutionAlgebra` class is a shell (no
multiplication anywhere; its two axioms are structure fields,
i.e. assumed, not derived; no instance exists), and the Python
inserts its zero-mode by hand. This module is the honest core
of the same idea, rebuilt and kernel-checked.

**What this module proves — and all it proves:** on the
21-element index set `Fin 21`, negation `Θ i = -i (mod 21)`
is an involution, the center `0` is fixed by `Θ`, and — a fact
the dropped sketch did not state — the center is the UNIQUE
fixed point of `Θ`, because 21 is odd: `Θ` pairs up the other
20 points into 10 mirror pairs and leaves exactly one point
unpaired. Elementary finite arithmetic; no algebra structure,
no operator, no spectrum is asserted here (the function
algebra is the companion brick `MirrorTwentyOneAlgebra`;
the honest numerics are `python/mirror21_heat.py`).

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4.
-/

import Mathlib.Data.Fin.Basic

namespace ThetLogos

/-- The 21-element index set (the cyclic seat, as `Fin 21`). -/
def ManifoldIndex := Fin 21

/-- The distinguished central element (the Tet center), index `0`. -/
def TethCenter : ManifoldIndex := ⟨0, by decide⟩

/-- The mirror involution `Θ : i ↦ -i (mod 21)`, in closed form. -/
def involution (i : ManifoldIndex) : ManifoldIndex :=
  ⟨(21 - i.val) % 21, Nat.mod_lt _ (by decide)⟩

/-- The value of `Θ i` is `(21 - i.val) % 21`, by definition. -/
theorem involution_val (i : ManifoldIndex) :
    (involution i).val = (21 - i.val) % 21 := rfl

/-- `Θ` is an involution: `Θ (Θ i) = i`. -/
theorem involution_involutive (i : ManifoldIndex) :
    involution (involution i) = i := by
  apply Fin.ext
  show (21 - ((21 - i.val) % 21)) % 21 = i.val
  have hi : i.val < 21 := i.isLt
  omega

/-- The center is fixed by `Θ`. -/
theorem involution_center_fixed : involution TethCenter = TethCenter := by
  apply Fin.ext
  rfl

/-- The center is the UNIQUE fixed point of `Θ` (21 is odd, so
`2i ≡ 0 (mod 21)` forces `i = 0`). Not in the dropped sketch. -/
theorem involution_fixed_unique (i : ManifoldIndex) (h : involution i = i) :
    i = TethCenter := by
  apply Fin.ext
  show i.val = 0
  have hi : i.val < 21 := i.isLt
  have hv : (21 - i.val) % 21 = i.val := congrArg Fin.val h
  omega

end ThetLogos
