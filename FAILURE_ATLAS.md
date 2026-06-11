# Failure atlas

A log of every place automation or the library fell short while formalizing
this development, with root causes. Each entry records: the goal, what was
tried, why it failed, and what fixed it. Entries marked **[benchmark]** are
extracted as standalone files under `Benchmarks/`.

Format note: these are not complaints — they are the data a verification
pipeline needs. A tactic that fails *for an articulable reason* is a missing
lemma, a normal-form mismatch, or an API gap; naming which is the point.

---

## A1. `simp` cannot see that `StrictMonoOn v ∅` is vacuous through a `Finset` coercion **[benchmark]**

- **Goal:** `StrictMonoOn v ↑(∅ : Finset (Fin n))`
- **Tried:** `simp` — failed, leaving the goal untouched.
- **Root cause:** the goal mixes two normal forms. `simp` knows
  `Finset.coe_empty : ↑(∅ : Finset α) = (∅ : Set α)` and there is a vacuity
  lemma for `Set` (`Set.Subsingleton.strictMonoOn`), but no `@[simp]` lemma
  rewrites `StrictMonoOn f ∅` to `True`, so after normalizing the coercion the
  simp set has nowhere to go. A `strictMonoOn_empty` simp lemma in Mathlib
  would close this class of goals.
- **Fix:** unfold the binder by hand: `fun a ha => by simp at ha`
  (membership in `∅` is the contradiction `simp` *can* see).

## A2. Higher-order unification failure: `Finset.le_max'` in term mode **[benchmark]**

- **Goal:** `∑ i ∈ t, w i ≤ maxMonoSum v w` where
  `maxMonoSum v w := ((monoSubseqs v).image fun t => ∑ i ∈ t, w i).max' _`
- **Tried:** term-mode
  `le_max' _ _ (mem_image_of_mem _ (mem_monoSubseqs.2 ht))` — type mismatch:
  the elaborator reports `?f t ≤ (image ?f _).max' ⋯` does not match the
  goal.
- **Root cause:** elaborating `le_max'` requires solving
  `(image ?f s).max' ⋯ =?= maxMonoSum v w`, which means unfolding a `def`
  *and* solving for the function `?f` under an `image` — a higher-order
  unification problem the elaborator (correctly) refuses to guess.
- **Fix (two stages — the first recorded fix was incomplete):**
  `unfold maxMonoSum` first, so the goal-side unification is syntactic. On a
  cold `lake build` that is still not enough: with `mem_image_of_mem _ ht`
  the image *function* is a metavariable, so the elaborator parks
  `DecidableEq ?m` (the instance `Finset.image` needs) and reports
  "typeclass instance problem is stuck". The complete fix supplies the
  function explicitly: `mem_image_of_mem (fun t => ∑ i ∈ t, w i) ht`.
  Caught during pre-publication review when the first verified-clean cold
  build was run — the original in-editor session had accepted the
  underdetermined form. General lesson: definitions wrapping
  `Finset.max'`/`image` should ship their own `le_*` API lemma immediately,
  precisely so no caller ever faces this unification problem — which is what
  `Defs.lean` does.

---

## E1. Lake/Lean/git block indefinitely on iCloud-evicted (`dataless`) trees **[environment]**

- **Symptom:** `lake build` sat at 0% CPU for 15+ minutes with no `lean`
  workers; independently, `git status`/`git diff HEAD` inside
  `.lake/packages/mathlib` hung the same way. An earlier full build appeared
  to "hang ~50 minutes in elaboration".
- **Diagnosis:** `sample` showed Lake parked in `Lake_PackageEntry_materialize`
  waiting on a spawned `git diff HEAD`; `lsof` showed that git blocked reading
  a workflow file; `ls -lO` showed the *entire* Mathlib package carries the
  macOS `dataless` flag. The repository lives under `~/Desktop`, which iCloud
  "Desktop & Documents" sync had evicted wholesale. Any `read`/`stat` of an
  evicted file traps into the file provider and blocks until iCloud
  rematerializes it — for Mathlib that is hundreds of thousands of files, so
  builds and whole-tree git operations stall at 0% CPU with no error message.
- **Root cause:** not Lean, Lake, or Mathlib — the build directory is inside
  an iCloud-synced path. The failure mode is invisible (kernel-level block,
  no timeout, no log line), which is what makes it atlas-worthy: it
  masquerades as "slow elaboration".
- **Fix:** keep Lean checkouts outside iCloud-synced paths (or
  `brctl download <dir>` / `brctl evict`-exempt them). For this review the
  canonical verification build was done from a fresh clone under `/tmp`.

---

*(in progress — entries are appended as the formalization proceeds)*
