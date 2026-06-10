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
- **Fix:** `unfold maxMonoSum` first, so `?f` is determined syntactically,
  then the same `exact` succeeds. General lesson: definitions wrapping
  `Finset.max'`/`image` should ship their own `le_*` API lemma immediately,
  precisely so no caller ever faces this unification problem — which is what
  `Defs.lean` does.

---

*(in progress — entries are appended as the formalization proceeds)*
