/-
Copyright (c) 2026 Rajarshi Maiti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Maiti
-/
import WeightedErdosSzekeres.Squares

/-!
# The area argument

The informal proof disposes of this step in one word ("Hence"): disjoint
squares inside a rectangle have total area at most the rectangle's area. In
Lean that single word becomes the entire content of this file — assembled
from 2-dimensional Lebesgue measure: `volume` of a product of intervals,
additivity over a pairwise-disjoint finite union, and monotonicity. The
inequality is then transported from `ℝ≥0∞` back to `ℝ`.

* `WeightedES.sum_sq_le_sq_maxMonoSum` — the ℓ² form of weighted
  Erdős–Szekeres: for injective `v` and positive weights `w`,
  `∑ i, w i ^ 2 ≤ (maxMonoSum v w) ^ 2`.
-/

open Finset MeasureTheory OrderDual Set

namespace WeightedES

variable {n : ℕ} {β : Type*} [LinearOrder β]

/-- The square over `i` has area `w i · w i`. -/
lemma volume_square (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) :
    volume (square v w i) = ENNReal.ofReal (w i) * ENNReal.ofReal (w i) := by
  rw [square, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc,
    Real.volume_Ioc, sub_sub_cancel, sub_sub_cancel]

/-- **Weighted Erdős–Szekeres, ℓ² form.** For an injective order map `v` and
positive weights `w`, the best monotone subsequence weight `S = maxMonoSum v w`
satisfies `∑ i, w i ^ 2 ≤ S ^ 2`.

Proof: the `n` disjoint squares of areas `w i ^ 2` all fit inside the
`S × S` rectangle. -/
theorem sum_sq_le_sq_maxMonoSum (v : Fin n → β) (w : Fin n → ℝ)
    (hv : Function.Injective v) (hw : ∀ i, 0 < w i) :
    ∑ i, w i ^ 2 ≤ maxMonoSum v w ^ 2 := by
  set S := maxMonoSum v w with hS
  have hS0 : 0 ≤ S := maxMonoSum_nonneg v w
  have key : ENNReal.ofReal (∑ i, w i ^ 2) ≤ ENNReal.ofReal (S ^ 2) := by
    calc ENNReal.ofReal (∑ i, w i ^ 2)
        = ∑ i, ENNReal.ofReal (w i ^ 2) :=
          ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _
      _ = ∑ i, volume (square v w i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [volume_square, pow_two, ENNReal.ofReal_mul (hw i).le]
      _ = volume (⋃ i ∈ (univ : Finset (Fin n)), square v w i) :=
          (measure_biUnion_finset (pairwiseDisjoint_square v w hv)
            fun i _ => measurableSet_square v w i).symm
      _ ≤ volume (Ioc (0 : ℝ) S ×ˢ Ioc (0 : ℝ) S) :=
          measure_mono (Set.iUnion₂_subset fun i _ => square_subset v w i)
      _ = ENNReal.ofReal S * ENNReal.ofReal S := by
          rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (S ^ 2) := by rw [pow_two, ENNReal.ofReal_mul hS0]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end WeightedES
