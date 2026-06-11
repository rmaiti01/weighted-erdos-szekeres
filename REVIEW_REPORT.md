# Pre-publication review report — weighted-erdos-szekeres

Hostile-referee review against the pre-publication brief, 2026-06-11.
Verdicts: `PASS` / `FAIL` / `MANUAL` (needs human eyes) / `FIXED` (fixed during
review — what and why). **The repo must not go public while any blocking issue
is open.**

## Blocking issues

*(in progress — finalized at the end of the review)*

## Phase 0 — mechanical bar

- **0.1 clean clone:** PASS (with environment caveat) — `git clean -ndx`
  lists only `.lake/`, `.claude/`, and the untracked `sources/` captures;
  nothing the build needs is untracked. Caveat: the *local* working copy
  lives in iCloud-synced `~/Desktop`, and iCloud had evicted the entire
  Mathlib package, making every build/git operation hang silently at 0% CPU
  (atlas entry E1). All verification builds for this review were therefore
  run from a clone outside iCloud.
- **0.2 build, zero warnings:** FIXED (was FAIL — **the uploaded code did
  not compile cold**). A from-scratch build (`lake exe cache get && lake
  build` in a fresh clone) failed with four errors that in-editor sessions
  and the iCloud stalls had masked:
  1. `Defs.lean` (`sum_le_maxMonoSum`, `le_incSumTo`): `mem_image_of_mem _`
     left the image function as a metavariable → "typeclass instance problem
     is stuck (`DecidableEq ?m`)". Fixed by supplying the function
     explicitly; FAILURE_ATLAS A2 updated to record the complete two-stage
     fix (its previously recorded fix was insufficient on a cold build).
  2. `Squares.lean` (two sites): `Ne.lt_or_lt` does not exist at Mathlib
     v4.29.0 — renamed `Ne.lt_or_gt`. Fixed.
  3. `Area.lean` (`volume_square`): `rw […, sub_sub_cancel]` rewrites only
     the first occurrence; the second factor's `T - (T - w i)` was left
     unsolved. Fixed (`sub_sub_cancel` twice).
  Warnings check: rerun on the final green build (below).
- **0.3 no holes:** FIXED — `grep "sorry\|admit\|stop\b"` over the main
  development returned one false positive: the English word "admit" in a
  Main.lean docstring. Reworded the docstring so the advertised grep is
  literally clean. No actual `sorry`/`admit`/`stop` anywhere in
  `WeightedErdosSzekeres/`.
- **0.4 axiom audits:** FIXED — no `#guard_msgs` axiom-audit blocks existed.
  Added three at the bottom of `WeightedErdosSzekeres/Main.lean`
  (`sum_sq_le_sq_maxMonoSum`, `erdos1026`, `exists_monoSubseq_sq_card_ge`),
  each asserting exactly `propext, Classical.choice, Quot.sound`. Build
  verification in progress.
- **0.5 adversarial grep:** PASS — `axiom `, `unsafe `, `native_decide`,
  `partial def`, `@[implemented_by]`, `macro_rules`, `maxHeartbeats`: zero
  hits in `WeightedErdosSzekeres/`.
- **0.6 toolchain consistency:** PASS — `lean-toolchain` =
  `leanprover/lean4:v4.29.0`; `lakefile.toml` `rev = "v4.29.0"`;
  `lake-manifest.json` mathlib `inputRev = "v4.29.0"` (rev
  `8a178386ffc0`); README claims Lean `v4.29.0` / Mathlib `v4.29.0`. All agree.

## Phase 1 — statement faithfulness

Audited `WeightedES.erdos1026` clause-by-clause against Cambie's verbatim
statement in `sources/SOURCES.md`:

- **distinct reals → `Function.Injective x`:** PASS — hypothesis present, on
  `x` itself (the one map that serves as both order map and weights here).
- **positive → `∀ i, 0 < x i`:** PASS — strict `<`.
- **sum equals 1 → `∑ i, x i = 1`:** PASS — `∑ i, _` elaborates as the sum
  over `Finset.univ : Finset (Fin (k ^ 2))`, i.e. over *all* k² terms.
- **k² terms → `Fin (k ^ 2)`:** PASS — explicitly parenthesized, no
  `Fin k ^ 2` parse trap; README consistently says `k²`.
- **monotone subsequence → `∃ t, (StrictMonoOn x ↑t ∨ StrictAntiOn x ↑t) ∧ …`:**
  PASS — the `∨` is inside the `∃`, conjoined with the sum bound, so one `t`
  witnesses both monotonicity and the bound. Strictness is the right rendering
  given distinctness (documented in INFORMAL.md §1 table).
- **sum at least 1/k → `(1 : ℝ) / k ≤ ∑ i ∈ t, x i`:** PASS — inequality
  direction correct, `k` coerced to `ℝ`, bound on the same `t`.
- **1.1 `k = 0` / division by zero:** PASS — the theorem carries `hk : 0 < k`.
  At `k = 0` the remaining hypotheses are unsatisfiable anyway (`Fin 0` has
  empty sum `0 ≠ 1`), so `hk` excludes only a vacuous case and weakens nothing
  at any `k` where the conjecture has content; it makes the implicit "k a
  positive integer" of the informal statement explicit. `1/(0:ℝ) = 0` is never
  relied on.
- **1.2 satisfiability witness:** FIXED — none existed. Added to `Main.lean`:
  `k = 2` with `x = ![1/10, 2/10, 3/10, 4/10]` (distinct, positive, sum 1),
  discharging every hypothesis of `erdos1026` with explicit data. A vacuous
  theorem could not be instantiated this way.
- **1.3 nonemptiness of the witness `t`:** PASS — for `k ≥ 1`, `1/k > 0`,
  and the conclusion bounds `∑ i ∈ t, x i` from below by it on the *same*
  quantified `t`, so `t = ∅` (sum `0`) cannot witness the conclusion; no
  separate nonemptiness hypothesis is needed.
- **1.4 corollary vs classical Erdős–Szekeres:** FIXED (prose) — the Lean
  statement `n ≤ #t ^ 2` is the **symmetric** (`√n`) form (e.g. `n = r² + 1`
  gives a monotone subsequence of length `> r`). It is *not* the asymmetric
  `r`/`s` form, which does not follow from bounding both ending-at-`i`
  quantities by the same `maxMonoSum`. README said "it is classical
  Erdős–Szekeres" without qualification; README and the docstring now say
  "symmetric form" and the docstring explicitly disclaims the asymmetric
  form. The claim is now exactly what the code proves.
- **1.5 hypothesis minimality documentation:** PASS — INFORMAL.md §3 (B2) and
  the module docstring of `Squares.lean` both state that injectivity of `v`
  is used only for the `v i < v j ∨ v j < v i` dichotomy
  (`square_disjoint_of_lt` confirms: the only use is `hv.ne hij.ne`). The
  theorem deliberately keeps `Function.Injective v`; documentation and code
  agree. Not weakened, per the brief.

## Phase 2 — claims audit

- **2.1 referenced paths:** FIXED — `Benchmarks/` was referenced by README and
  FAILURE_ATLAS.md but **did not exist**. Created `Benchmarks/` with the two
  `[benchmark]`-tagged atlas entries as standalone eval files
  (`A1_StrictMonoOnEmptyCoe.lean`, `A2_LeMaxThroughDef.lean`), a `Benchmarks`
  lake target excluded from the default build (intentional `sorry`s), a CI
  step elaborating them, and an explicit README note that benchmark `sorry`s
  are intentional. All other referenced paths exist.
- **2.2 line-count claim:** PASS (vacuous) — the README makes no line-count
  claim about this development. Actual: 438 lines across the four
  `WeightedErdosSzekeres/*.lean` files (before review edits). The only counts
  claimed are about Aristotle's proof (3,658 lines — verified against the
  pinned file, which GitHub reports as 3,658 lines).
- **2.3 atlas ↔ benchmarks:** PASS (empirically re-verified) — both atlas
  claims were re-run against the pinned toolchain rather than trusted:
  - A1: `simp` on `StrictMonoOn v ↑(∅ : Finset (Fin n))` normalizes the
    coercion and then stalls on `StrictMonoOn v ∅`, exactly as the entry
    says; the recorded fix `fun a ha => by simp at ha` is verbatim what
    `empty_mem_monoSubseqs` does in `Defs.lean`.
  - A2: the term-mode `le_max'` attempt fails with precisely the quoted
    `?f t ≤ (image ?f _).max' ⋯` mismatch. The entry's *fix* was found
    incomplete on a cold build (see 0.2) and the entry now records the
    complete two-stage fix; the benchmark file states both data points.
  - Every `[benchmark]`-tagged entry has a standalone file in `Benchmarks/`
    stating its provenance, and each benchmark file names its atlas entry.
  - Bonus finding: INFORMAL.md §3 B5 claimed finding the Cauchy–Schwarz
    lemma's name "is a benchmark task in the failure atlas" — no such atlas
    entry existed, and the empirical test shows `exact?` *does* retrieve
    `Finset.sum_mul_sq_le_sq_mul_sq` once the goal is in the lemma's exact
    shape. Manufacturing a failure entry would have been dishonest; the
    prose was corrected to state the lemma name and the actual `exact?`
    behavior. FIXED.
- **2.4 external links:**
  - Tao post URL (`…/the-story-of-erdos-problem-126/` — the `126` slug is
    Tao's actual slug, not a typo): PASS, fetched, title "The story of Erdős
    problem #1026", dated 8 Dec 2025.
  - Aristotle file at pinned commit `9f90812f…`: PASS, fetched; 3,658 lines;
    repository declares no license (matches README/SOURCES claims).
  - arXiv:1608.04153 Tidor–Wang–Yang: PASS, fetched, title and authors match.
  - `erdosproblems.com/1026` and forum thread: MANUAL — the site returns
    HTTP 403 to non-browser fetchers; verify in a browser before going
    public. (The 2026-06-10 local raw captures are evidence both pages
    existed yesterday.)
- **2.5 quoted material licensing:** FIXED (blocking) — `sources/`
  **committed full-text dumps** of Tao's blog post and the forum thread
  (1,653 lines of unlicensed third-party content) — the same vendoring
  problem the README correctly avoids for Aristotle's proof. Untracked both
  files, added them to `.gitignore`, and amended the initial commit so they
  never appear in the published history. SOURCES.md and README provenance
  sections updated to say exactly what is and isn't vendored. The short
  attributed excerpts in SOURCES.md (author + timestamp + link) remain — they
  are quotation, not redistribution.

## Phase 3 — code quality

IN PROGRESS

## Phase 4 — reproducibility, CI, hygiene

- **4.1 CI workflow:** FIXED — the workflow built the project but ran no
  hole-check. Added: a `sorry|admit` grep gate over the main development and
  an explicit `lake build Benchmarks` step. The axiom audits are enforced by
  the existing build step since they live in `Main.lean` (in the default
  target). Toolchain is pinned via `lean-toolchain` (read by
  `leanprover/lean-action@v1`), cache via the same action. Badge added to
  README pointing at `rmaiti01/weighted-erdos-szekeres` (remote now exists).
- **4.2 .gitignore:** FIXED — added `.claude/` (local agent settings) and the
  two raw capture files; `.lake/` and the Aristotle file were already
  covered.
- **4.3 verify-in-10-minutes block:** FIXED — added at the top of README:
  build commands, hole grep, axiom-audit pointer, statement-faithfulness
  pointer to INFORMAL.md §1.
- **4.4 leakage:** PASS — `git grep` over tracked files for
  `/Users/|~/Desktop|key|token|secret`: no hits. History is two commits,
  both reviewed.
- **4.5 LICENSE:** PASS — stock Apache 2.0 full text (the `[yyyy]` appendix
  placeholder is part of the verbatim license text). File headers now
  reference it with the author's full name (see Phase 3 headers item).

## Phase 5 — final adversarial pass

NOT STARTED
