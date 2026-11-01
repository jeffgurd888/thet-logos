# GR-GEO-0 — LANDED FULL: the cube-distance registration pin (`geoDist` owned as `SimpleGraph.dist`; the PoseObjF shadow predicate registered verbatim, prior on its face)

**Verdict: GR-GEO-0 FULL. The GR-GEO line's interface is frozen as its own verified commit: the cube graph built from the landed link head/tail data, `geoDist` as a citation-definition of Mathlib's graph distance, GEO-1's two targets registered, and the `PoseObjF` shadow predicate registered as an exact statement — statable from today, with its truth nobody's claim and its registered prior death at its seat. PROGRAM CEILING, on this dossier's face: vocabulary — it seats NO gravity object; Dial 2 = 0 under every outcome. NO CLAIM. Dials 0/4.**

## What the pin registers (`LayerCubeDistancePost.lean`, new module; working label — Jeff names)

- **`cubeGraph N : SimpleGraph (LayerSite N)`** — adjacency from the landed `linkTail`/`linkHead` (`MaxwellQuadPost`): `x ≠ y` and some link joins them in either direction; symmetric and loopless by the encoding's form (adjacency read-backs `cubeGraph_adj`, `cubeGraph_adj_of_link`).
- **`geoDist N x y : ℕ := (cubeGraph N).dist x y`** — a citation-definition only. On its face: Mathlib's `dist` returns 0 at unreachable pairs, so connectedness is load-bearing (it is GEO-1's first target); and **K-GR-SMUG instance (iv)**: the ℓ¹ formula is a theorem-to-be, never the definition — the metric content will come from graph-distance theory plus the connectedness proof, not from the definition (the K-GR-VAC fence likewise).
- **GEO-1's targets, registered:** `CubeGraphConnected N : Prop := (cubeGraph N).Connected`; `GeoDistL1Formula N : Prop := ∀ x y, geoDist N x y = ∑ i : Fin 4, cycDist N (x.1 i) (y.1 i)` with the one-coordinate auxiliary `cycDist N a b := min (a-b).val (b-a).val` registered so the formula states exactly.
- **Link separation:** `linkGeoDist N ℓ ℓ' := geoDist N (linkTail ℓ) (linkTail ℓ')` — the predicate quantifies over link pairs, separation measured between tails (registration choice on the face).
- **The shadow predicate, verbatim:** `PoseObjFShadow N K C : Prop` := `0 ≤ C ∧ ∀ ℓ ℓ' : LayerLink N, 1 ≤ linkGeoDist N ℓ ℓ' → |K ℓ ℓ'| ≤ C / (linkGeoDist N ℓ ℓ' : ℝ) ^ 2`. **The constant discipline is the fence:** `C` is a named constant supplied WITH a candidate as a parameter of the predicate, never existentially quantified inside it — on a finite pair set an existentially quantified constant is satisfiable by every kernel, which is K-GR-VAC, struck in advance on the face. Ceiling on the face: finite shadow only, statable ≠ true, **PRIOR = death by finite size at its seat**; intended instantiation named: `K := greenKernel m` of GR-GEO-2 (gated on MAX-2 + GR-GEO-1) at the smallest cube seats, `N = 2` first. Neither target nor the predicate is asserted anywhere in the pin.

## Fences on the face

Finite names only (the continuum nouns appear once, inside the FRONTIER fence sentence listing them as unspendable). The DIST ≠ GEO fence from this side: `geoDist` lives on sites, `connesDist` on states; neither sub-line cites the other as evidence. Kills on the face: K-GR-VAC, K-GR-SMUG (instance (iv) named), K-GR-LAUNDER, K-GR-STAB (instance (iii) named — an `N = 2` wrap failure of the ℓ¹ formula would be a finding, not a repair), K-GR-BUY. Noun audit: hits only in fence/governing contexts.

## Parent verification (from disk)

- Canonical counter: **strict=8, defs=7** (inside the S estimate 6–10); zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green, independently reproduced (3,668-job closure).
- Parent axiom check: `geoDist_unfold`, `poseObjFShadow_unfold` on exactly `[propext, Classical.choice, Quot.sound]` (the builder's sweep found some read-backs on subsets — `[propext, Quot.sound]` — reported as such, all within the standard three).

## Census

10,048 → **10,056 strict** / 10,126 → **10,133 attribute-inclusive** / 338 → **339 modules** (delta +8 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
