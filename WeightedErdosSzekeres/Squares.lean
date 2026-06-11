/-
Copyright (c) 2026 Rajarshi Maiti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Maiti
-/
import WeightedErdosSzekeres.Defs

/-!
# The packed squares

Over each index `i` we erect the half-open square

`square v w i = Ioc (Sᵢ - wᵢ) Sᵢ ×ˢ Ioc (Tᵢ - wᵢ) Tᵢ`,

where `Sᵢ = incSumTo v w i` and `Tᵢ = incSumTo (⇑toDual ∘ v) w i` are the best
increasing/decreasing weights ending at `i`. This file proves the two facts
the informal proof states in eight words ("these are disjoint and contained in
the rectangle"):

* `WeightedES.pairwiseDisjoint_square` — distinct indices give disjoint
  squares. For `i < j` either `v i < v j` (then the growth inequality
  `incSumTo_add_le` separates the *first* coordinates) or `v j < v i` (then
  its order-dual instance separates the *second* coordinates). This dichotomy
  is the only place injectivity of `v` is used.
* `WeightedES.square_subset` — every square lies in
  `Ioc 0 (maxMonoSum v w) ×ˢ Ioc 0 (maxMonoSum v w)`.

Half-open intervals are chosen so that "the squares tile without overlap"
needs no boundary bookkeeping: adjacent squares share only a measure-zero
edge, and with `Ioc` not even that.
-/

open Finset OrderDual Set

namespace WeightedES

variable {n : ℕ} {β : Type*} [LinearOrder β]

/-- The half-open square erected over index `i`: horizontally it spans the
last `w i` of the best increasing weight ending at `i`, vertically the last
`w i` of the best decreasing weight ending at `i`. -/
noncomputable def square (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) : Set (ℝ × ℝ) :=
  Ioc (incSumTo v w i - w i) (incSumTo v w i) ×ˢ
    Ioc (incSumTo (⇑toDual ∘ v) w i - w i) (incSumTo (⇑toDual ∘ v) w i)

lemma measurableSet_square (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) :
    MeasurableSet (square v w i) :=
  measurableSet_Ioc.prod measurableSet_Ioc

/-- Core dichotomy, stated for `i < j`: whichever way `v i` and `v j`
compare, one coordinate's intervals separate. A point in both squares
yields a linear contradiction with the growth inequality. -/
private lemma square_disjoint_of_lt {v : Fin n → β} {w : Fin n → ℝ} {i j : Fin n}
    (hv : Function.Injective v) (hij : i < j) :
    Disjoint (square v w i) (square v w j) := by
  rw [Set.disjoint_left]
  rintro ⟨p₁, p₂⟩ hp hq
  simp only [square, Set.mem_prod, Set.mem_Ioc] at hp hq
  rcases (hv.ne hij.ne).lt_or_gt with hvij | hvji
  · -- `v i < v j`: the first coordinates cannot coexist.
    have h := incSumTo_add_le w hij hvij
    linarith [hp.1.2, hq.1.1]
  · -- `v j < v i`: dually, the second coordinates cannot coexist.
    have h := incSumTo_add_le (v := ⇑toDual ∘ v) w hij (by simpa using hvji)
    linarith [hp.2.2, hq.2.1]

/-- Distinct indices erect disjoint squares. -/
lemma pairwiseDisjoint_square (v : Fin n → β) (w : Fin n → ℝ)
    (hv : Function.Injective v) :
    Set.PairwiseDisjoint (↑(univ : Finset (Fin n))) (square v w) := by
  intro i _ j _ hne
  rcases hne.lt_or_gt with hij | hji
  · exact square_disjoint_of_lt hv hij
  · exact (square_disjoint_of_lt hv hji).symm

/-- Every square lies in the rectangle `Ioc 0 S ×ˢ Ioc 0 S`,
`S = maxMonoSum v w`: lower-left corners are nonnegative because the
singleton subsequence is always available, and upper-right corners are at
most `S` because increasing/decreasing-ending-at-`i` subsequences are in
particular monotone. -/
lemma square_subset (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) :
    square v w i ⊆
      Ioc 0 (maxMonoSum v w) ×ˢ Ioc 0 (maxMonoSum v w) := by
  apply Set.prod_mono <;> apply Set.Ioc_subset_Ioc
  · linarith [self_le_incSumTo v w i]
  · exact incSumTo_le_maxMonoSum v w i
  · linarith [self_le_incSumTo (⇑toDual ∘ v) w i]
  · exact decSumTo_le_maxMonoSum v w i

end WeightedES
