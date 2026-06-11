/-
Copyright (c) 2026 Rajarshi Maiti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Maiti
-/
import Mathlib

/-!
# Benchmark A2 — `Finset.le_max'` through a definition, in term mode

**Provenance:** `FAILURE_ATLAS.md`, entry A2 (hit while proving
`WeightedES.sum_le_maxMonoSum` in `WeightedErdosSzekeres/Defs.lean`).

`maxSum` below mirrors the shape of `WeightedES.maxMonoSum`: a `Finset.max'`
of an `image`, wrapped in a `def`.

**Task for the tactic/prover under evaluation:** replace the `sorry` below.

Known data points (Lean `v4.29.0`, Mathlib `v4.29.0`):
* term-mode `le_max' _ _ (mem_image_of_mem _ ht)` fails: elaboration must
  solve `(image ?f _).max' ⋯ =?= maxSum F hF w`, i.e. unfold a `def` *and*
  solve for `?f` under `image` — a higher-order unification problem the
  elaborator refuses to guess;
* after `unfold maxSum`, the same term *still* fails on a cold build:
  with `?f` a metavariable the instance `DecidableEq ?m` needed by
  `Finset.image` is stuck ("typeclass instance problem is stuck");
* the human fix is `unfold maxSum`, then
  `exact le_max' _ _ (mem_image_of_mem (fun t => ∑ i ∈ t, w i) ht)` —
  the image function supplied explicitly.
-/

open Finset

/-- The largest value of `∑ i ∈ t, w i` over `t ∈ F` (mirrors
`WeightedES.maxMonoSum`). -/
noncomputable def maxSum {n : ℕ} (F : Finset (Finset (Fin n))) (hF : F.Nonempty)
    (w : Fin n → ℝ) : ℝ :=
  (F.image fun t => ∑ i ∈ t, w i).max' (hF.image _)

example {n : ℕ} (F : Finset (Finset (Fin n))) (hF : F.Nonempty) (w : Fin n → ℝ)
    {t : Finset (Fin n)} (ht : t ∈ F) :
    ∑ i ∈ t, w i ≤ maxSum F hF w := by
  sorry
