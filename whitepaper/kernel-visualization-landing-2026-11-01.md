# KERNEL VISUALIZATION v1 — BUILT AND LAUNCHED on the lab exhibits surface (working label)

**Verdict: the kernel-visualization page is built exactly as scoped and goes live with this landing at `exhibits/kernel-visualization/`. It replays the bench's own record — the event spine of landings, partials, and kills, with attempt-level zoom episodes where log series exist — under the memo's named projection, in Jeff's color law. It tests nothing, proves nothing, moves no dial. Its shipped sentence, verbatim on its face: "Recognition is cheap here and construction is expensive — that asymmetry, as one bench lived it, is all that is shown." P vs NP: NO CLAIM, parts 0. Dials 0/4.**

## What was built

- **The spine:** 259 pipeline-log entries extracted to **254 events** through the freeze point (the SKY-0 landing), each carrying its outcome class in the log's own vocabulary, census triple, strict/defs and job counts where the log states them (partial coverage is the disk truth — "not recorded is not zero" is printed on the panel; events without job counts plot on the baseline). An extraction report (`extraction-report.md` in the showroom part) lists every deviant entry — **nothing silently dropped**; the 5 post-freeze exclusions are named in it.
- **Zoom episodes:** SHELF-5 the flagship — 8 attempts (builds 2–3 are 0-byte, timestamp-only attempts, drawn as ticks; five trace-line durations preserved; builds 1–7 failed on preserved error lines, build 8 clean; the axiom verdict preserved verbatim). B4 (8 attempts), B4′ (3), Battery (18 artifacts). All attempt times are brackets [previous artifact mtime, log mtime], drawn as bars, never points.
- **A correction the disk forced, at full rank:** B4's `.exit` files on disk read 1,1,1,1,**0**,1,1,0 — an intermediate success the scoping memo's summary did not carry. Disk governs; the panel notes it. Likewise the timestamp normalization is stricter than the memo's sketch: most entries cite remote-batch hashes absent from the local git history, so a hash resolves only when its commit time is the closest to the label time within 36 h — result **6 git-exact, 248 label-grade**, each event's grade on its record, disclosed on the panel as part of the named transformation.
- **The projection:** P(θ) printed on the panel as a formula family; position = (bench time UTC, log₁₀(1 + search jobs) — the log scaling labeled a display choice); color-law channels X red = search, Y blue = check, Z green = yield, printed as a named design choice; check cost by glyph size; census as a step line (no smoothing, no interpolation); replay clock with gaps drawn as gaps; event inspector quoting the entry's own record with dossier links per the link rule. The renderer reuses the Synesthesia Exhibit v1's color-law components — one renderer across the program. Coordinates are episode-space only; ℝ⁴⁴⁸ is not imported (the only "448" strings on the page are inside verbatim log excerpts in the inspector).
- **The ring glyph** at check events is labeled **T5 metaphor** on the page; the literal shared-gap resonance panel is explicitly not built (gated on the RES line). The "no kernel interior exists" note is printed (K-KV-THEATRE's ground).
- **Forward-instrumentation SPEC** landed as a document (`whitepaper/bench-event-schema-spec-2026-11-01.md`), marked NOT BUILT on its face — the append-only JSONL bench event schema; its build remains a separate, unratified operations decision.

## Verification

Builder: sampled events byte-checked against log + git (QR-D1's census and 3,325 jobs and commit time exact; mid/late censuses exact); SHELF-5 attempt byte sizes match disk; every §2 transformation confirmed printed on the panel; kill checklist item by item (parent spot-checks concur: shipped sentence verbatim; kills named; "solving P vs NP" occurs only inside the K-KV-LAUNDER definition that forbids the drift; zero Feral content). A Node DOM/canvas-stub execution of the launch page caught one real bug (census step line reading cs[−1] on the first point) — fixed and rebuilt before this landing. A true in-browser visual check was not available to the builder or to this ceremony; the page follows the sibling exhibit's verified pattern and code path.

## Surfaces

Live with this commit: `exhibits/kernel-visualization/index.html` (self-contained). Showroom part built in house pattern at `~/workspace/ts-spaces/acmd-showroom-parts/kernel-visualization/` (index.html + events.json + episodes.json + extraction report + three named generators). Shell registration: same boundary as the sibling — not done by file edit, reported, not forced. Census-neutral landing (README stands at 10,224/345).

## Backers since last landing

No change to the backer roll since the last landing.
