# PNP-0 — P vs NP shelf + definition-debt audit (Millennium Lane 3)

Date: 2026-11-02. Audit only — no Lean files, no builds, no commits.
Registration: `whitepaper/next-rotation-scoping-2026-11-01.md` §3.3
(PNP-1, M–L, statement pin; K-PNP-1 armed). Pack:
`pack-pnp-0-audit.md`. Mathlib pin: v4.35.0-rc3, at
`~/workspace/thet-logos/lean/.lake/packages/mathlib/` (toolchain
`leanprover/lean4:v4.35.0-rc3`, lakefile rev confirmed).

> **NO CLAIM.** Parts of P vs NP closed by this audit: **0.**
> Nothing here is a theorem, a formalization, or progress on the
> problem. This memo prices the *statement pin only*. Jeff's T5
> identification (verification/construction asymmetry) is **not**
> pin content; it is excluded from every definition below and is
> mentioned only in this fence.

---

## 1. In-pin TM shelf — verdict: PARTIAL, better than expected on
##    functions, empty on classes

### 1.1 Machine models present (all three, with step/eval API)

- **TM0** (Post–Turing): `Mathlib/Computability/TuringMachine/PostTuringMachine.lean`
  — `namespace TM0` :106, `Stmt` inductive :118, `Machine Γ Λ :=
  Λ → Stmt Γ Λ` :135, `Cfg` :144, `step : Cfg → Option Cfg` :159,
  `eval : Machine → List Γ → Part (ListBlank Γ)` :173.
- **TM1** (single-tape with internal state σ): same file,
  `namespace TM1` :286, `Cfg` :326, `step` :349, `eval` :455.
- **TM2** (multi-stack): `Mathlib/Computability/TuringMachine/StackTuringMachine.lean`
  — `namespace TM2` :107, `Stmt` :127, `Cfg` :144, `step` :171,
  `eval` :289.
- Tapes: `TuringMachine/Tape.lean` (`ListBlank`, `Tape`, blank
  extension machinery, 605 lines).
- Simulations exist but carry **no time bounds**: `TM1to0`
  (PostTM :481), `TM1to1` (:629), `TM0to1` (:964), `TM2to1`
  (StackTM :289/:333), and `TuringMachine/ToPartrec.lean` (TM →
  partial recursive, 1282 lines). Halting API: `eval` lands in
  `Part`; there is no decidability/decider layer on any TM model.

### 1.2 Step-counting — present and honest

`Mathlib/Computability/StateTransition.lean`: `EvalsTo` :255,
`EvalsToInTime` :265 (`steps : ℕ`, `steps_le_m : steps ≤ m`).
Time = number of iterations of the `step` function, in ℕ.
`TuringMachine/Computable.lean` :23–28 (implementation notes)
states this is within a constant factor of fundamental steps.
This unit does **not** trivialize (see §4).

### 1.3 Polytime — EXISTS at function level (corrects the
###     near-zero expectation); classes — ZERO

Verbatim grep results over the whole pin (`Mathlib/` tree):

- `polytime` (case-insensitive): **exactly one file**,
  `Computability/TuringMachine/Computable.lean`, 12 hits.
- `PolynomialTime`: **0 files**. `PClass`: **0 files**.
  `NPClass`: **0 files**. `Complexity` in `Computability/`:
  **0 hits**.

What the one file supplies (`Computable.lean`):

- `FinTM2` :46 — bundled TM2 with finiteness (Fintype stacks,
  labels, states), `step` :103, `initList` :110, `haltList` :118.
- `TM2Outputs` :131, `TM2OutputsInTime` :135 (output in ≤ m steps).
- `TM2ComputableAux` :147 (machine + alphabet equivs to `Γ₀/Γ₁`).
- `TM2ComputableInTime` :166, **`TM2ComputableInPolyTime` :179** —
  a bundled machine + `time : Polynomial ℕ` + proof it outputs
  `f a` within `time.eval (ea a).length` steps, for a **function**
  `f : α → β` under encodings. Sanity inhabitant:
  `idComputableInPolyTime` :225.

What is absent: polytime for **languages/decision problems**
(no decider structure, no characteristic-function wrapper),
**P**, **NP**, any complexity class, any time/space hierarchy,
any reduction between classes (`Reduce.lean` has many-one
reducibility `≤₀` for *computability*, no polytime restriction).

### 1.4 Nondeterminism — finite automata only

`nondeterministic` in `Computability/`: 4 hits, all in
`NFA.lean` :12–14 and `EpsilonNFA.lean` :12–14 (finite automata).
**No nondeterministic Turing machine exists in the pin** — no
relational step, no guess/accept-by-path semantics. Oracles exist
only at the partial-recursive level (`RecursiveIn.lean`,
`ComputableIn`), not as oracle TMs.

### 1.5 Free parts the pin can reuse

- `Language α := Set (List α)` — `Computability/Language.lean` :65,
  with membership instance :71. Languages need **not** be owned.
- `Encoding` (`Computability/Encoding.lean`): `encodeBool` :163,
  `encodingList` :191.
- `Polynomial ℕ` + `eval` (`Algebra/Polynomial/Eval/Defs.lean`),
  already used by `TM2ComputableInPolyTime`.
- `Nat.Partrec.Code` is `Denumerable` (`PartrecCode.lean` :173)
  and `Computability/Halting.lean` :65 proves the halting problem
  for it — relevant to the K-test witness route (§4B).

**Shelf verdict:** the deterministic side of the pin stands on
real shelf (`FinTM2` + `TM2OutputsInTime` + `Polynomial ℕ`).
The debt is: (i) decider/language wrapper around the
function-level polytime, (ii) all of NP, (iii) the diagonal
witness decoding. No owned step-counting relation is needed —
the model's API *can* carry time bounds, via `EvalsToInTime`.

---

## 2. In-tree (corpus) — exactly zero

Own corpus = `lean/ThetLogos/` (444 `.lean` files; `.lake`
excluded):

- `Turing` (word search): 0 genuine hits (2 substring hits,
  "manufacturing", in `CpecBridgePost.lean` :140, :519).
- `Computable` / `ComputablePred` (word): **0**. `Language`
  (word): **0**. `polytime`, `PeqNP`, `nondetermin`: **0**.
- No file imports `Mathlib.Computability.*` or any TM module.

The corpus owns no computability vocabulary at all. PNP-1 starts
from the pin shelf alone. Millennium board state agrees:
`~/workspace/millennium-program/INDEX.md` :10 — "P versus NP …
OPENED — untouched by the corpus. NO CLAIM. First rung:
statement pin + barrier map."

---

## 3. Owned vocabulary for PNP-1 (draft shapes — NOT compiled,
##    definition shapes only, at audit grade)

Alphabet fixed to `Bool` (Cook-standard binary; any finite
alphabet reduces to it, and fixing one alphabet is what a
statement pin should do).

```lean
-- FREE from pin: Lang := Language Bool = Set (List Bool)
-- FREE from pin: Turing.FinTM2, Turing.TM2OutputsInTime,
--   Turing.TM2ComputableAux, Polynomial ℕ, Polynomial.eval

/-- D1 (owned): a bundled polytime decider for a language.
    Totality is inherited: `correct` demands a halting output
    bit for EVERY input, within the polynomial bound. -/
structure PolyDecider (L : Language Bool) where
  aux  : Turing.TM2ComputableAux Bool Bool
  time : Polynomial ℕ
  correct : ∀ x : List Bool,
    Turing.TM2OutputsInTime aux.tm
      (x.map aux.inputAlphabet.invFun)
      (some ((if x ∈ L then [true] else [false]).map
        aux.outputAlphabet.invFun))
      (time.eval x.length)

def InP (L : Language Bool) : Prop := Nonempty (PolyDecider L)
def PClass : Set (Language Bool) := {L | InP L}

/-- D2 (owned, ~5 lines): length-prefixed pairing of strings. -/
def pairStr (x w : List Bool) : List Bool :=
  (List.replicate x.length true ++ [false]) ++ x ++ w

/-- NP, VERIFIER FORM (the pin's definition; see §3.1).
    Certificate bounded by a polynomial in |x| alone; the
    verifier is a polytime decider of the pair language, so
    its time bound is a polynomial in |pairStr x w| = Θ(|x|+|w|).
    Both guards are load-bearing (§4A). -/
def InNP (L : Language Bool) : Prop :=
  ∃ (c : ℕ) (VL : Language Bool), InP VL ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool,
      w.length ≤ (x.length + 1) ^ c ∧ pairStr x w ∈ VL

def NPClass : Set (Language Bool) := {L | InNP L}

/-- The pin statement. Set equality: both directions, neither
    baked in (see §3.2). -/
def PeqNP : Prop := PClass = NPClass

/-- The substantive working direction, named separately. -/
def NPSubsetP : Prop := ∀ L : Language Bool, L ∈ NPClass → L ∈ PClass
```

### 3.1 NP form recommendation: VERIFIER form is the definition

- **Machine (NDTM) form: rejected for the pin.** The pin has no
  NDTM (§1.4). Owning one means an owned relational step
  semantics on TM2 configurations, accept-by-bounded-path, and
  its own API — priced at **+L alone** (§5), and the
  NDTM↔verifier equivalence is a real theorem (simulation both
  ways), **unpriceable at pin grade**.
- **Verifier form: taken as the definition.** It is a standard
  characterization in Cook's own framing and in Sipser
  (Thm 7.20: NP = languages decidable by polytime verifiers);
  the Clay statement is insensitive to which characterization
  *defines* the class, since they are provably the same class
  in the textbook theory.
- If a later brick wants the machine form, it enters as a new
  brick with the equivalence stated as a **named hypothesis**,
  never as a house theorem at pin grade.

### 3.2 `PeqNP` form: class equality, not the one-way inclusion

`PClass = NPClass` is the honest both-directions form: by
`Set.ext` it is `∀ L, L ∈ NP ↔ L ∈ P`; it asserts neither `=`
nor `≠`, and its negation is equally statable (`¬ PeqNP`).
The one-way form `∀ L, L ∈ NP → L ∈ P` silently presupposes
`P ⊆ NP` — true in the textbook theory (empty certificate),
but in this corpus it is an *unproved* inclusion; baking it
into the question's statement would hide a proof obligation
inside the pin. Equality carries both directions openly;
`NPSubsetP` is named alongside as the direction any future
attack actually works on.

---

## 4. K-PNP-1 audit test — designed against the §3 draft

Kill condition (registration): a pin whose polytime notion is
satisfiable by construction artifacts — every language polytime
by construction — is vacuous; kill and re-enter. Test in two
parts.

### Part A — unit/totality audit: **PASS (unconditional)**

1. **Time unit is genuine.** The bound is
   `time.eval x.length` against `TM2OutputsInTime`, i.e.
   `EvalsToInTime FinTM2.step` with `steps ≤ bound`
   (StateTransition :265). One step = one TM2 statement
   execution; the pin's own note (Computable :23–28) bounds the
   distortion by a constant factor. No rescaling of the unit
   makes a super-polynomial computation polynomial.
2. **Totality blocks the cheap artifact.** `PolyDecider.correct`
   quantifies over **all** `x` and demands the *correct* output
   bit within the bound. A construction artifact would have to
   actually decide `L`; there is no partiality, no "accepts if
   it halts", no promise restriction to hide in.
3. **Verifier-form guards are present.** Certificate length is
   bounded by a polynomial in `|x|` alone, and the verifier must
   itself be in `InP` (total, polytime in the pair length).
   Drop either guard and every RE language would satisfy the
   shape — the draft does not drop them.
4. **Controls are statable and separated in form:**
   `InP ∅`, `InP Set.univ` (expected cheaply provable later,
   not at pin grade) versus `∃ L, L ∉ PClass` — a well-formed
   Prop that the definitions do not make definitionally true
   or false.

### Part B — time-hierarchy witness statability:
### **CONDITIONAL PASS — debt item D5 is mandatory**

The witness must be *stated*, not proved outside P. Draft:

```lean
-- D5 (owned, priced in §5): a decoding of decider codes.
--   Route (i): normal-form FinTM2 codes — FinTM2 has
--     Type-valued fields (K, Γ, Λ, σ), so a total decode
--     List Bool → Option FinTM2 is NOT a routine Encodable
--     instance; it needs a fixed normal form first.
--   Route (ii) (cheaper, recommended): Nat.Partrec.Code,
--     Denumerable (PartrecCode :173), with an owned
--     step-bounded acceptance predicate over the code
--     step function (TuringMachine/Config.lean's Cfg/step).
def Ldiag : Language Bool :=
  {x | ∀ (M : <decider code type>) (p : Polynomial ℕ),
    decode x = some (M, p) →
      ¬ AcceptsWithin M x (p.eval x.length)}

def KPNP1Witness : Prop := Ldiag ∉ PClass   -- stated, NOT proved
```

With D5 in scope, `Ldiag` and `Ldiag ∉ PClass` are statable in
the §3 vocabulary: the diagonal language at each string `x`
runs the decoded decider on `x` itself under its own stated
bound and flips the answer — the exact shape whose (textbook)
non-membership in P is what makes the test meaningful.

**If PNP-1 skips D5, the witness cannot even be stated, K-PNP-1
is unarmed, and the pin must not fire.** This is the audit's one
hard condition. Route (ii) is recommended: `Code` is already
denumerable data, whereas route (i) first has to invent a
normal form for a bundled structure with Type-valued fields.

---

## 5. Revised price for PNP-1 (registration: M–L — CONFIRMED,
##    split as follows)

| Brick | Content | Band |
|---|---|---|
| **PNP-1a** Definitions | `PolyDecider`, `InP`, `PClass`, `pairStr`, `InNP`, `NPClass` (§3) | **M** |
| **PNP-1b** Statement | `PeqNP`, `NPSubsetP`, control statements (`InP ∅` etc. as statements), NO CLAIM header | **S** |
| **PNP-1c** K-test witness | D5 decode (route ii) + `Ldiag` + `KPNP1Witness` statement | **S–M** |
| **Total** | | **M–L** (as registered) |

Definition debt, itemized:

- **Owned (the debt):** D1 decider wrapper + alphabet-equiv
  plumbing around `TM2ComputableAux` (the pin's polytime is
  function-shaped; the language wrapper is ours); D2 `pairStr`;
  D3 the verifier-form `InNP` with both anti-vacuity guards;
  D5 the decider-code decoding for the witness (route ii).
- **Supplied by the pin (not debt):** TM2 model + `FinTM2`
  bundling, step function, `TM2OutputsInTime` step-counting,
  `Polynomial ℕ` time bounds, `Language Bool`, encodings.
- **Excluded, priced separately if ever wanted:** owned NDTM
  **+L**; NDTM↔verifier equivalence **unpriceable at pin
  grade** (a simulation theorem, not a definition); any
  `P ⊆ NP` or barrier content — PNP-2's territory, not this pin.

Price driver confirmed as registered: definition debt, not
proof effort — the pin contains no theorems beyond, at most,
definitional sanity checks.

---

## 6. Fences

- NO CLAIM: parts of P vs NP closed: **0**. `PeqNP` as drafted
  is a *statement shape*; this audit has not compiled it, and
  PNP-1's first act is to make it compile at exactly this shape
  or report the deviation.
- K-PNP-1 remains **armed** for PNP-1: Part A passed against
  this draft; Part B passes **only with D5 inside PNP-1c**.
  A PNP-1 that drops D5, weakens either verifier guard, or
  takes the one-way inclusion as `PeqNP` fails this audit's
  test and is killed and re-entered per the registration.
