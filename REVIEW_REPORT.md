# Pre-publication review report — weighted-erdos-szekeres

Hostile-referee review against the pre-publication brief, 2026-06-11/12.
Verdicts: `PASS` / `FAIL` / `MANUAL` (needs human eyes) / `FIXED` (fixed during
review — what and why). **The repo must not go public while any blocking issue
is open.**

## Blocking issues

All blocking issues found during review are **resolved**; one MANUAL item
remains for human eyes before flipping the repo public:

1. **MANUAL:** `erdosproblems.com/1026` and the forum-thread URL return
   HTTP 403 to non-browser fetchers — verify both load in a browser and that
   the problem-page status line still reads as quoted in `sources/SOURCES.md`.

(A second MANUAL item — CI green on the final commit — was closed during the
review: the GitHub Actions run on the final commit completed `success`. The
run history itself corroborates the review: the pre-review code failed CI,
the intermediate commit failed on the sorry-gate-vs-docstring issue found by
the audit, and the post-review commits pass.)

Resolved during review (details in the phases below): the uploaded code did
not compile cold (four Lean errors, 0.2); unlicensed full-text source dumps
were committed (2.5); `Benchmarks/` was referenced but did not exist (2.1);
INFORMAL.md claimed a module that was never written (2.6); the CI sorry-gate
matched its own prose (4.1); several factual counts in the prose were wrong
(2.7, 2.8).

## Phase 0 — mechanical bar

- **0.1 clean clone:** PASS (with environment caveat) — `git clean -ndx`
  lists only `.lake/`, `.claude/`, and the untracked `sources/` captures;
  nothing the build needs is untracked. Caveat: the local working copy lives
  in iCloud-synced `~/Desktop`, and iCloud had evicted the entire Mathlib
  package, making builds and whole-tree git operations hang silently at 0%
  CPU (atlas entry E1). All verification builds for this review were run
  from clones outside iCloud.
- **0.2 build, zero warnings:** FIXED (was FAIL — **the uploaded code did
  not compile cold**). A from-scratch build (`lake exe cache get && lake
  build` in a fresh clone, pinned toolchain) failed with four errors that
  in-editor sessions and the iCloud stalls had masked:
  1. `Defs.lean` (`sum_le_maxMonoSum`, `le_incSumTo`): `mem_image_of_mem _`
     left the image function as a metavariable → "typeclass instance problem
     is stuck (`DecidableEq ?m`)". Fixed by supplying the function
     explicitly; FAILURE_ATLAS A2 updated to record the complete two-stage
     fix (its previously recorded fix was insufficient on a cold build).
  2. `Squares.lean` (two sites): `Ne.lt_or_lt` does not exist at Mathlib
     v4.29.0 — it is `Ne.lt_or_gt`. Fixed.
  3. `Area.lean` (`volume_square`): `rw […, sub_sub_cancel]` rewrites only
     the first occurrence; the second factor was left unsolved. Fixed.
  4. `Main.lean` (`erdos_1026`): the non-terminal `simp` in the
     Cauchy–Schwarz cast step closed the goal entirely under the pinned
     simp set, leaving `push_cast; ring` with no goals. Replaced by a
     squeezed `simp only […]; push_cast; ring`.
  After the fixes: `lake build` ends **Build completed successfully** with
  **zero warnings** (README's claim verified literally);
  `lake build Benchmarks` succeeds with exactly the two documented
  intentional-`sorry` warnings.
- **0.3 no holes:** FIXED — the grep over the main development returned only
  prose false positives (the English word "admit", later the literal
  "`sorry`" in the axiom-audit section header — see 4.1). Both reworded; the
  advertised grep now returns nothing. No actual `sorry`/`admit`/`stop` in
  `WeightedErdosSzekeres/`.
- **0.4 axiom audits:** FIXED — no `#guard_msgs` axiom-audit blocks existed.
  Added three at the bottom of `Main.lean` (`sum_sq_le_sq_maxMonoSum`,
  `erdos_1026`, `exists_monoSubseq_le_sq_card`), each asserting exactly
  `propext, Classical.choice, Quot.sound`. They are part of the default
  build target, so CI enforces them on every push; verified passing in the
  clean-clone build.
- **0.5 adversarial grep:** PASS — `axiom `, `unsafe `, `native_decide`,
  `partial def`, `@[implemented_by]`, `macro_rules`, `maxHeartbeats`: zero
  hits in `WeightedErdosSzekeres/`.
- **0.6 toolchain consistency:** PASS — `lean-toolchain`
  (`leanprover/lean4:v4.29.0`), `lakefile.toml` (`rev = "v4.29.0"`),
  `lake-manifest.json` (mathlib `inputRev = "v4.29.0"`, rev `8a178386ffc0`),
  and README all agree.

## Phase 1 — statement faithfulness

Audited `WeightedES.erdos_1026` clause-by-clause against Cambie's verbatim
statement in `sources/SOURCES.md`:

- **distinct reals → `Function.Injective x`:** PASS — hypothesis present, on
  `x` itself (the one map serving as both order map and weights here).
- **positive → `∀ i, 0 < x i`:** PASS — strict `<`.
- **sum equals 1 → `∑ i, x i = 1`:** PASS — the sum is over
  `Finset.univ : Finset (Fin (k ^ 2))`, i.e. over *all* k² terms.
- **k² terms → `Fin (k ^ 2)`:** PASS — explicitly parenthesized; no
  `Fin k ^ 2` parse trap; README consistently says `k²`.
- **monotone subsequence → `∃ t, (StrictMonoOn x ↑t ∨ StrictAntiOn x ↑t) ∧ …`:**
  PASS — the `∨` is inside the `∃`, conjoined with the sum bound, so one `t`
  witnesses both. Strictness is the right rendering given distinctness
  (documented in INFORMAL.md §1).
- **sum at least 1/k → `(1 : ℝ) / k ≤ ∑ i ∈ t, x i`:** PASS — direction
  correct, `k` coerced to `ℝ`, bound on the same quantified `t`.
- **1.1 `k = 0` / division by zero:** PASS — the theorem carries
  `hk : 0 < k`. At `k = 0` the remaining hypotheses are unsatisfiable anyway
  (`Fin 0` has empty sum `≠ 1`), so `hk` excludes only a vacuous case and
  weakens nothing where the conjecture has content; it makes the informal
  statement's implicit "k a positive integer" explicit. `1/(0:ℝ) = 0` is
  never relied on.
- **1.2 satisfiability witness:** FIXED — none existed. Added to
  `Main.lean`: `k = 2` with `x = ![1/10, 2/10, 3/10, 4/10]` (distinct,
  positive, sum 1), discharging every hypothesis of `erdos_1026` with
  explicit data. A vacuous theorem could not be instantiated this way.
- **1.3 nonemptiness of the witness `t`:** PASS — for `k ≥ 1`, `1/k > 0`
  and the conclusion bounds the sum over the *same* `t` from below, so
  `t = ∅` (sum `0`) cannot witness it; no separate hypothesis needed.
- **1.4 corollary vs classical Erdős–Szekeres:** FIXED (prose) — the Lean
  statement `n ≤ #t ^ 2` is the **symmetric** (`√n`) form. It is *not* the
  asymmetric `r`/`s` form, which would need the unexported product
  inequality `(maxᵢ Sᵢ)(maxᵢ Tᵢ) ≥ ∑ wᵢ²` rather than its symmetrized `S²`
  corollary. README, the theorem docstring, and INFORMAL.md §6.2 now all say
  "symmetric form" and the docstring explicitly disclaims the asymmetric
  form. (INFORMAL.md §6.2 additionally claimed subsumption "set x ≡ 1" —
  wrong twice over, since the order map must stay injective and only the
  symmetric form is recovered; corrected to "set w ≡ 1, order map still
  injective".)
- **1.5 hypothesis minimality documentation:** PASS — INFORMAL.md §3
  (B2a/B2b) and `Squares.lean` both state that injectivity of `v` is used
  only for the `v i < v j ∨ v j < v i` dichotomy (`square_disjoint_of_lt`
  confirms: the only use is `hv.ne`). The theorem deliberately keeps
  `Function.Injective v`; documentation and code agree. The §1 table cell
  that compressed this to "not actually needed!" was overstated (for the
  strict-monotone rendering the ℓ² bound is false with repeated values —
  e.g. two equal values of weight 1) and now states the precise claim.

## Phase 2 — claims audit

- **2.1 referenced paths:** FIXED — `Benchmarks/` was referenced by README
  and FAILURE_ATLAS.md but **did not exist**. Created: the two
  `[benchmark]`-tagged atlas entries as standalone eval files
  (`A1_StrictMonoOnEmptyCoe.lean`, `A2_LeMaxThroughDef.lean`), a
  `Benchmarks` lake target excluded from the default build (intentional
  `sorry`s), a CI step elaborating them, and a README note that the
  `sorry`s are intentional. All other referenced paths exist; every local
  Markdown link target verified.
- **2.2 line-count claim:** FIXED (added, was absent) — README previously
  made no line-count claim; it now states ~490 lines of documented Lean
  (≈230 lines of proof with comments stripped), matching `wc -l` (486 raw)
  so external documents can cite a number consistent with what `wc` reports.
- **2.3 atlas ↔ benchmarks:** PASS (empirically re-verified) — both atlas
  claims were re-run against the pinned toolchain rather than trusted:
  - A1: `simp` on `StrictMonoOn v ↑(∅ : Finset (Fin n))` normalizes the
    coercion and stalls on `StrictMonoOn v ∅`, exactly as the entry says;
    the recorded fix `fun a ha => by simp at ha` is verbatim what
    `empty_mem_monoSubseqs` does.
  - A2: the term-mode `le_max'` attempt fails with precisely the quoted
    `?f t ≤ (image ?f _).max' ⋯` mismatch. The entry's fix was found
    incomplete on a cold build (0.2) and now records the complete two-stage
    fix; the benchmark file states both data points.
- **2.4 external links:**
  - Tao post URL (the `…erdos-problem-126` slug is Tao's actual slug, not a
    typo): PASS — fetched; title "The story of Erdős problem #1026",
    8 Dec 2025.
  - Aristotle file at pinned commit `9f90812f…`: PASS — fetched; 3,658
    lines; repository declares no license (matches README/SOURCES claims).
  - arXiv:1608.04153 (Tidor–Wang–Yang): PASS — fetched; title/authors match.
  - `erdosproblems.com/1026` + forum thread: MANUAL (HTTP 403 to fetchers;
    the 2026-06-10 local captures are evidence of yesterday's state).
- **2.5 quoted material licensing:** FIXED (blocking) — `sources/` had
  **committed full-text dumps** of Tao's blog post and the forum thread
  (1,653 lines of unlicensed third-party content) — the same vendoring
  problem the README correctly avoids for Aristotle's proof. Untracked
  both, `.gitignore`d, and rewrote history so they never appear in the
  published repo (the rewritten history is what `origin/main` now serves).
  SOURCES.md/README provenance sections updated. The short attributed
  excerpts (author + timestamp + link) remain — quotation, not
  redistribution.
- **2.6 phantom stretch module:** FIXED (blocking) — INFORMAL.md §4/§6
  claimed the Erdős–Szekeres tightness construction was "formalized here as
  the stretch module". No such module exists. Both passages now state it is
  *not* formalized here and is the sharpest library gap surfaced (PR-able
  independently). Prose made true rather than silently weaker: the claim
  was deleted as false, not reworded to hide.
- **2.7 "four sentences":** FIXED — Chan's verbatim proof (quoted in
  SOURCES.md) is **six** sentences; README, SOURCES.md, and INFORMAL.md all
  said "four". All now say six sentences (INFORMAL.md: "six short
  sentences, quoted below in its four steps"). Any external document citing
  "four-sentence proof" should say "six-sentence" (or "four-step").
- **2.8 Cauchy–Schwarz "benchmark task":** FIXED — INFORMAL.md §3 B5
  claimed finding the lemma's name "is a benchmark task in the failure
  atlas"; no such entry existed, and the empirical test shows `exact?`
  *does* retrieve `Finset.sum_mul_sq_le_sq_mul_sq` once the goal is in the
  lemma's exact shape. Manufacturing a failure entry would have been
  dishonest; the prose now names the lemma and describes the actual
  `exact?` behavior.
- **2.9 Mathlib-context claims (ground-truthed against the checkout, since
  one named reviewer authored the file in question):** PASS —
  `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` is by
  Bhavik Mehta; its scaffolding (`incSequencesTo`, `maxIncSequencesTo`, …)
  is genuinely `private`; SOURCES.md's quoted `erdos_szekeres` statement
  matches the source verbatim; the file dualizes with `βᵒᵈ` as Defs.lean's
  design note says. One precision added: Mathlib *proper* does contain the
  **infinitary** Erdős–Szekeres (`exists_increasing_or_nonincreasing_subseq`),
  so README/SOURCES now say the *finite quantitative* theorem is
  Archive-only.
- **2.10 Steele attribution:** PASS (verified, with a footnote added) — the
  repo dates Steele's survey to 1995. Tao's post calls it a "1980 article"
  in an edit, but the zbMATH record Tao links (0832.60012) is the 1995
  survey (*Variations on the monotone subsequence theme of Erdős and
  Szekeres*, IMA Vol. 72, Springer 1995, pp. 111–131 — confirmed against
  the Springer record). SOURCES.md now carries the full citation and a
  footnote preempting the apparent discrepancy. Tao's account otherwise
  confirms the repo's narrative verbatim: Aristotle solved it autonomously
  on Dec 7, 2025 during Alexeev's sweep; "Within an hour, Koishi Chan gave
  an alternate proof"; Tidor–Wang–Yang 2016 was located afterwards.

## Phase 3 — code quality and Mathlib idiom

- **3.1 `import Mathlib`:** PASS (documented tradeoff) — kept deliberately;
  README now owns it ("standalone development, not a library; the pinned
  binary cache makes it a one-time download"). Single-file elaboration is
  ~4–5 min for `Defs.lean`, well under the 10-minute suspicion threshold.
  Import minimization was deprioritized in favor of statement/claims
  accuracy; revisit if the repo is ever PR'd into a library.
- **3.2 copyright headers:** FIXED — all four files (plus benchmark files)
  now read `Copyright (c) 2026 Rajarshi Maiti` / `Authors: Rajarshi Maiti`.
- **3.3 docstrings:** FIXED — `Area.lean`/`Main.lean` already met the bar;
  added docstrings to the two API-instantiation lemmas in `Defs.lean` that
  lacked them. Every public `def`/`theorem` now carries one.
- **3.4 naming (Mathlib conventions, reviewed adversarially):** FIXED —
  - `decSumTo_le_maxMonoSum` named a definition that does not exist →
    renamed `incSumTo_toDual_comp_le_maxMonoSum` (mirrors Mathlib's
    `strictMonoOn_toDual_comp_iff` naming for `toDual ∘ f` forms).
  - `strictAntiOn_iff_strictMonoOn_toDual` duplicated Mathlib's
    `strictMonoOn_toDual_comp_iff` (with inverted orientation) → deleted;
    the library lemma is used directly.
  - `exists_monoSubseq_sq_card_ge` said `ge` while the statement uses `≤` →
    renamed `exists_monoSubseq_le_sq_card`.
  - `erdos1026` → `erdos_1026` (snake_case, cf. `Theorems100.erdos_szekeres`).
  - `incSumTo_le_maxMonoSum_of` (bare trailing `_of`) → renamed
    `incSumTo_le_maxMonoSum_of_forall_isMonoSubseq`.
- **3.5 fragility scan:** FIXED —
  - The one non-terminal `simp` (Cauchy–Schwarz cast step) squeezed to
    `simp only […]` (it had in fact begun *closing* the goal under the
    pinned simp set, breaking the build — see 0.2.4).
  - `nlinarith [hsq, hSk]` at the end of the headline theorem replaced by
    the named lemma `(one_le_sq_iff₀ hSk).1 hsq` — no search-based tactic
    remains in the main proof path.
  - No `decide` on large goals, no `exact?`/`apply?` leftovers, no
    `maxHeartbeats` overrides.
- **3.6 dead code / defeq brittleness / linting:** PASS — the `Iff.rfl`
  bridge lemma was deleted outright in favor of Mathlib's own (which is
  `Iff.rfl` there); no unused hypotheses found. `#lint in
  WeightedErdosSzekeres` (Batteries linter, 16 linters over 28 declarations
  plus 10 auto-generated): **0 errors, all checks passed**.

## Phase 4 — reproducibility, CI, repo hygiene

- **4.1 CI workflow:** FIXED (twice) — the original workflow only built the
  project. Added: the `sorry|admit` grep gate and an explicit
  `lake build Benchmarks` step; the axiom audits are enforced by the
  existing build step (they live in the default target). **Second find:**
  the newly added axiom-audit section header itself contained the literal
  word `` `sorry` `` ("no `sorry`, no extra axioms"), which the new gate's
  `\bsorry\b` matches — CI would have gone red on every push, and the
  README's "no output = no holes" check would print output. Reworded to
  "no holes, no extra axioms"; gate grep verified clean locally. Badge
  added to README pointing at this repo's workflow.
- **4.2 `.gitignore`:** FIXED — added `.claude/` and the two raw-capture
  files; `.lake/` and the Aristotle file were already covered.
- **4.3 verify-in-10-minutes block:** FIXED — added at the very top of
  README: build commands, hole grep, axiom-audit pointer,
  statement-faithfulness pointer to INFORMAL.md §1.
- **4.4 leakage:** PASS — `git grep` over tracked files for
  `/Users/|~/Desktop|key|token|secret`: no hits; history reviewed (two
  commits, both authored during this review cycle).
- **4.5 LICENSE:** PASS — stock Apache 2.0 full text (the `[yyyy]` appendix
  placeholder is part of the verbatim license); file headers reference it
  with the author's full name.

## Phase 5 — final adversarial pass

- **5.1 fresh-clone build:** PASS — the entire verification cycle was run
  from fresh clones (first `/tmp`, then `~/wes-build`) with
  `lake exe cache get && lake build` from nothing: green, zero warnings,
  axiom audits passing, Benchmarks target green with exactly its two
  intentional sorries. CI on GitHub repeats this on every push (MANUAL item
  2: confirm the badge on the final commit).
- **5.2 wrong-theorem sanity check:** PASS (reasoning) — the satisfiability
  example instantiates every hypothesis with concrete rationals and is
  *applied* to the theorem, so the standard vacuity failure modes are
  caught mechanically: contradictory hypotheses (e.g. positivity reversed,
  or a sum normalization that the data can't meet) would make the example's
  side goals unprovable by `norm_num`, and an accidentally weakened
  conclusion (e.g. `≤` flipped) would still elaborate but the example pins
  the *statement* being exported, making the diff visible in review. The
  `#guard_msgs` audits separately pin the axioms, so a `sorry`'d or
  axiom-smuggling variant cannot pass CI.
- **5.3 Main.lean read as prose:** PASS — module docstring states both
  results and the two defense artifacts; each theorem's docstring states
  the informal content, the satisfiability witness explains *why it
  exists*; the symmetric-form disclaimer preempts the one place a
  mathematician would object. The proof of `erdos_1026` is commented at
  each of its three steps (Cauchy–Schwarz, ℓ² bound, square-root
  extraction).
- **5.4 audit method note:** the review used five independent adversarial
  reviewers (Mathlib idiom; external-source verification; Archive
  ground-truth; mathematical referee of INFORMAL.md; application-claims
  cross-check) plus empirical re-runs of every atlas claim. Findings from
  the mathematical referee additionally produced: the B2 split into
  B2a/B2b (the extension lemma and the disjointness inference are distinct
  hidden lemmas, and the formalization indeed proves them as separate
  declarations), the positivity-ledger correction (G1(iii) was spurious —
  unweighted ES is sign-blind; G6 is the only positivity use in Proof A),
  and the §6.2 subsumption fix recorded under 1.4.
