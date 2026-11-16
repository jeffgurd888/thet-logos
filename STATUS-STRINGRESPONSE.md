# STATUS-STRINGRESPONSE — StringResponsePin, Brick 1

**Lane grade only. NO CLAIM. Dial-ineligible. Not integrated;
no census movement.**

- **Tree / branch:** `~/workspace/thet-logos-og0`, branch
  `stringresponse`, cut from `stringseat` tip `f01def3`.
- **Code commit:** `dc407eb` (module
  `lean/ThetLogos/StringResponsePin.lean`, 275 lines).
- **Declarations: 9 — 1 def + 8 theorems, sorry 0.**
  - `siteSum` (def) — the single-site sum over the tree's
    `bendCost`.
  - `siteSum_eq` — exact value `z(β) = 1 + k · e^{−β}`.
  - `siteSum_zero` — hot value `z(0) = k + 1`.
  - `partSum_bendEnergy_eq` — **factorization**
    `partSum bendEnergy β = siteSum k β ^ n` (induction on
    `n` via `Fin.consEquiv`).
  - `gibbsProb_straightConfig_siteSum` — **ground
    probability** `p₀(β) = (siteSum k β ^ n)⁻¹`.
  - `gibbsProb_straightConfig_zero` — hot value
    `p₀(0) = ((k + 1)^n)⁻¹`.
  - `one_le_siteSum` — `1 ≤ z` (holds at every `β`; see
    note below).
  - `siteSum_le_one_add` — `z ≤ 1 + k` for `β ≥ 0`.
  - `activity_le` — **activity bound**
    `1 − p₀(β) ≤ n · k · e^{−β}`.
- **Build:** targeted `lake build ThetLogos.StringResponsePin`
  — **PASS, EXIT=0**, complete run, log
  `~/workspace/thet-logos-og0/build-stringresponse-2026-11-15.log`.
  No fence marker was live at any build launch.
- **Axioms:** `#print axioms` on `partSum_bendEnergy_eq`,
  `gibbsProb_straightConfig_siteSum`, `activity_le` (and
  `siteSum_eq`) — each exactly
  `{propext, Classical.choice, Quot.sound}`. No `sorryAx`,
  no `native_decide`, no kernel `decide` on real goals.
- **Olean:** on disk, 258,232 bytes, sha256
  `d75b6ca7fa763662b215ed347c2333d612714422e7497cbf9aaa51f9dd708b30`.
- **Source hash check:** disk sha256 ==
  `git show stringresponse:lean/ThetLogos/StringResponsePin.lean`
  sha256 == `2ffba032d2b36bda2b7a9a874e19a921a992e046e6fe9c20aea4873d8f484ac0`
  — MATCH, verified mechanically in one command.

## THE ADAPTATION (read at full rank)

The commissioning brief's item 1 defined the single-site
sum as `z(β) := Σ j : Fin (k+1), Real.exp (−β * j)` — a
LEVEL-weighted energy. The tree's actual `bendCost`
(StringSeatPin §1) is `0/1`: a link is straight or bent,
and `bendEnergy` COUNTS bent links. With the brief's
`z`, its item 2 (factorization of the tree's `partSum`)
is FALSE. Per the brief's own governing discipline —
build ON the existing definitions, invent no parallel
energy — `siteSum` is the sum over the tree's `bendCost`,
and it evaluates EXACTLY:

    z(β) = 1 + k · e^{−β}

Consequences for the brief's item 5: (a) and (b) are
superseded by the exact identity; the landed corollaries
are `1 ≤ z` and `z ≤ 1 + k` (β ≥ 0). Item 5(c)'s activity
bound `1 − p₀ ≤ n · k · e^{−β}` landed exactly as
specified. The seat's response function is therefore

    R(β) = 1 − (1 + k · e^{−β})^{−n},

NOT the geometric-series form of the desk derivation.
Cold-end leading term: `n · k · e^{−β}` (first excited
level = one bent link: degeneracy `n · k`, gap `1`) —
the exponential freeze-out and the gap slope survive;
the prefactor and the exact `z` differ from the desk
note. Any outside-facing text quoting `z = Σⱼ e^{−βj}`
for this seat should be corrected before it is sent.

Two statements landed STRONGER than the brief's β ≥ 0
forms, found by the linter (unused `hβ`): `one_le_siteSum`
and `activity_le` hold at EVERY `β` — the activity bound
is the one-variable inequality `1 − (1 + x)^{−n} ≤ n·x`
at `x = k·e^{−β} ≥ 0`. Their docstrings say so; the cold
regime β ≥ 0 remains the physical reading.

## NOT BUILT (by the brick's bound)

- The crossover/threshold: existence of `β*` with
  `R(β*) = 1/2` by IVT — brick 2. (With the tree's `z`,
  the crossover sits where `k · e^{−β} ≈ ln 2 / n`.)
- The signed-bend / direction observable: bends carry
  no sign at this seat, so no directed current is
  defined. Not attempted.
- No integration, no posts, no census claims.
