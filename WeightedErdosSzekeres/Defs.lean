/-
Copyright (c) 2026 Rajarshi Maiti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Maiti
-/
import Mathlib

/-!
# Weighted Erdős–Szekeres: definitions and basic API

Given an *order-carrying* map `v : Fin n → β` and a *weight* `w : Fin n → ℝ`, we
define the maximum weight of a monotone subsequence,

* `WeightedES.maxMonoSum v w` — the largest value of `∑ i ∈ t, w i` over index
  sets `t : Finset (Fin n)` on which `v` is strictly monotone (increasing or
  decreasing); the empty set qualifies vacuously, so the maximum always exists;

together with the Seidenberg-style "ending at `i`" quantities driving the
rectangle-packing proof:

* `WeightedES.incSetsTo v i` — index sets on which `v` is strictly increasing
  and whose greatest element is `i`;
* `WeightedES.incSumTo v w i` — the largest `w`-sum over `incSetsTo v i`.

There are no decreasing-side definitions: decreasing quantities for `v` are
increasing quantities for `⇑OrderDual.toDual ∘ v`, with the same weights.

## Design notes

The order map and the weight map are deliberately *decoupled*:

1. Decreasing-subsequence quantities are increasing-subsequence quantities for
   `⇑OrderDual.toDual ∘ v` with the *same* weights, so every lemma about
   `incSumTo` dualizes for free. (Mathlib's `Archive` proof of Erdős–Szekeres
   dualizes with `βᵒᵈ` because `Finset.card` ignores values; for weighted sums
   that trick only survives if the weights do not pass through the dual.)
2. The main theorem `sum_sq_le_sq_maxMonoSum` becomes strictly stronger than
   its motivating problem: `w ≡ 1` recovers the classical Erdős–Szekeres
   bound, while `v = w = x` is Erdős problem #1026.

This file mirrors the idioms of
`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` (subsequences
are `Finset`s of indices, monotonicity is `StrictMonoOn`/`StrictAntiOn` on the
coerced set).
-/

open Finset OrderDual

namespace WeightedES

variable {n : ℕ} {β : Type*} [LinearOrder β]

/-! ### Monotone index sets and the maximum monotone weight -/

/-- `t` is a *monotone subsequence* for the order map `v` if `v` is strictly
increasing or strictly decreasing on `t`. The empty set (and every singleton)
qualifies vacuously. -/
def IsMonoSubseq (v : Fin n → β) (t : Finset (Fin n)) : Prop :=
  StrictMonoOn v ↑t ∨ StrictAntiOn v ↑t

/-- Strict antitonicity on `s` is strict monotonicity into the dual order;
this is the bridge along which every decreasing-side fact is obtained from its
increasing-side sibling. -/
lemma strictAntiOn_iff_strictMonoOn_toDual {v : Fin n → β} {s : Set (Fin n)} :
    StrictAntiOn v s ↔ StrictMonoOn (⇑toDual ∘ v) s :=
  Iff.rfl

/-- The (finite, nonempty) family of monotone index sets. -/
noncomputable def monoSubseqs (v : Fin n → β) : Finset (Finset (Fin n)) :=
  open Classical in {t : Finset (Fin n) | IsMonoSubseq v t}

@[simp]
lemma mem_monoSubseqs {v : Fin n → β} {t : Finset (Fin n)} :
    t ∈ monoSubseqs v ↔ IsMonoSubseq v t := by
  classical
  simp [monoSubseqs]

lemma empty_mem_monoSubseqs (v : Fin n → β) : ∅ ∈ monoSubseqs v :=
  mem_monoSubseqs.2 <| Or.inl fun a ha => by simp at ha

/-- The largest weight of a monotone subsequence. Well-defined because the
empty set is vacuously monotone. -/
noncomputable def maxMonoSum (v : Fin n → β) (w : Fin n → ℝ) : ℝ :=
  ((monoSubseqs v).image fun t => ∑ i ∈ t, w i).max'
    (Finset.Nonempty.image ⟨∅, empty_mem_monoSubseqs v⟩ _)

/-- Every monotone subsequence weighs at most `maxMonoSum`. -/
lemma sum_le_maxMonoSum {v : Fin n → β} {w : Fin n → ℝ} {t : Finset (Fin n)}
    (ht : IsMonoSubseq v t) :
    ∑ i ∈ t, w i ≤ maxMonoSum v w := by
  unfold maxMonoSum
  exact le_max' _ _ <| mem_image_of_mem (fun t => ∑ i ∈ t, w i) <| mem_monoSubseqs.2 ht

/-- The maximum is attained. -/
lemma exists_maxMonoSum (v : Fin n → β) (w : Fin n → ℝ) :
    ∃ t : Finset (Fin n), IsMonoSubseq v t ∧ ∑ i ∈ t, w i = maxMonoSum v w := by
  obtain ⟨t, ht, hsum⟩ := mem_image.1 <| max'_mem
    ((monoSubseqs v).image fun t => ∑ i ∈ t, w i)
    (Finset.Nonempty.image ⟨∅, empty_mem_monoSubseqs v⟩ _)
  exact ⟨t, mem_monoSubseqs.1 ht, hsum⟩

/-- `maxMonoSum` is nonnegative, because the empty subsequence weighs `0`.
(For positive weights it is in fact positive, but nonnegativity is all the
main proof needs.) -/
lemma maxMonoSum_nonneg (v : Fin n → β) (w : Fin n → ℝ) : 0 ≤ maxMonoSum v w := by
  have h : (∑ i ∈ (∅ : Finset (Fin n)), w i) ≤ maxMonoSum v w :=
    sum_le_maxMonoSum (mem_monoSubseqs.1 (empty_mem_monoSubseqs v))
  simpa using h

/-! ### Increasing subsequences ending at a given index -/

/-- Index sets on which `v` is strictly increasing and whose greatest element
is `i`. Decreasing-side sets are `incSetsTo (⇑toDual ∘ v) i`. -/
noncomputable def incSetsTo (v : Fin n → β) (i : Fin n) : Finset (Finset (Fin n)) :=
  open Classical in {t : Finset (Fin n) | IsGreatest (↑t) i ∧ StrictMonoOn v ↑t}

@[simp]
lemma mem_incSetsTo {v : Fin n → β} {i : Fin n} {t : Finset (Fin n)} :
    t ∈ incSetsTo v i ↔ IsGreatest (↑t) i ∧ StrictMonoOn v ↑t := by
  classical
  simp [incSetsTo]

lemma singleton_mem_incSetsTo (v : Fin n → β) (i : Fin n) : {i} ∈ incSetsTo v i :=
  mem_incSetsTo.2 ⟨by simp [IsGreatest], by simp⟩

/-- The largest weight of an increasing subsequence ending at `i`; the
weighted analogue of `maxIncSequencesTo` from the `Archive` proof of
Erdős–Szekeres. -/
noncomputable def incSumTo (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ((incSetsTo v i).image fun t => ∑ j ∈ t, w j).max'
    (Finset.Nonempty.image ⟨{i}, singleton_mem_incSetsTo v i⟩ _)

lemma le_incSumTo {v : Fin n → β} (w : Fin n → ℝ) {i : Fin n} {t : Finset (Fin n)}
    (ht : t ∈ incSetsTo v i) :
    ∑ j ∈ t, w j ≤ incSumTo v w i := by
  unfold incSumTo
  exact le_max' _ _ <| mem_image_of_mem (fun t => ∑ j ∈ t, w j) ht

lemma exists_incSumTo (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) :
    ∃ t ∈ incSetsTo v i, ∑ j ∈ t, w j = incSumTo v w i := by
  obtain ⟨t, ht, hsum⟩ := mem_image.1 <| max'_mem
    ((incSetsTo v i).image fun t => ∑ j ∈ t, w j)
    (Finset.Nonempty.image ⟨{i}, singleton_mem_incSetsTo v i⟩ _)
  exact ⟨t, ht, hsum⟩

/-- The singleton `{i}` witnesses `w i ≤ incSumTo v w i`; geometrically, the
square erected over index `i` has its lower-left corner at a nonnegative
coordinate. -/
lemma self_le_incSumTo (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) :
    w i ≤ incSumTo v w i := by
  simpa using le_incSumTo w (singleton_mem_incSetsTo v i)

/-- Adjoining a later, `v`-larger index to an increasing subsequence keeps it
increasing. The one-line informal step "any increasing subsequence ending at
`i` extends by `j`" — here it earns its keep as an `insert` with order
side-conditions. -/
lemma insert_mem_incSetsTo {v : Fin n → β} {i j : Fin n} {t : Finset (Fin n)}
    (ht : t ∈ incSetsTo v i) (hij : i < j) (hvij : v i < v j) :
    insert j t ∈ incSetsTo v j := by
  obtain ⟨⟨hit, hmax⟩, hmono⟩ := mem_incSetsTo.1 ht
  have hlt : ∀ a ∈ (↑t : Set (Fin n)), a < j := fun a ha => lt_of_le_of_lt (hmax ha) hij
  have hvlt : ∀ a ∈ (↑t : Set (Fin n)), v a < v j := by
    intro a ha
    rcases eq_or_lt_of_le (hmax ha) with rfl | hai
    · exact hvij
    · exact (hmono ha hit hai).trans hvij
  refine mem_incSetsTo.2 ⟨⟨by simp, ?_⟩, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.1 (by exact_mod_cast ha) with rfl | hat
    · exact le_rfl
    · exact (hlt a hat).le
  · push_cast
    intro a ha b hb hab
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd hab (lt_irrefl _)
    · exact absurd hab (not_lt.2 (hlt b hb).le)
    · exact hvlt a ha
    · exact hmono ha hb hab

/-- The key Seidenberg-style growth inequality: if `j` comes later than `i`
positionally and is `v`-larger, then the best increasing subsequence ending at
`j` beats the best one ending at `i` by at least `w j`. This is what makes
consecutive squares' first coordinates disjoint. -/
lemma incSumTo_add_le {v : Fin n → β} (w : Fin n → ℝ) {i j : Fin n}
    (hij : i < j) (hvij : v i < v j) :
    incSumTo v w i + w j ≤ incSumTo v w j := by
  obtain ⟨t, ht, hsum⟩ := exists_incSumTo v w i
  have hjt : j ∉ t := fun hjt =>
    absurd ((mem_incSetsTo.1 ht).1.2 hjt) (not_le.2 hij)
  calc incSumTo v w i + w j = ∑ a ∈ insert j t, w a := by
        rw [sum_insert hjt, ← hsum]; ring
    _ ≤ incSumTo v w j := le_incSumTo w (insert_mem_incSetsTo ht hij hvij)

/-! ### Increasing-ending-at-`i` subsequences are monotone subsequences -/

/-- Generic comparison: if every member of `incSetsTo u i` is a monotone
subsequence for `v`, then `incSumTo u w i ≤ maxMonoSum v w`. Instantiated
twice below (`u = v` and `u = ⇑toDual ∘ v`). -/
lemma incSumTo_le_maxMonoSum_of {u : Fin n → β} {γ : Type*} [LinearOrder γ]
    {v : Fin n → γ} (w : Fin n → ℝ) {i : Fin n}
    (h : ∀ t ∈ incSetsTo u i, IsMonoSubseq v t) :
    incSumTo u w i ≤ maxMonoSum v w := by
  obtain ⟨t, ht, hsum⟩ := exists_incSumTo u w i
  exact hsum ▸ sum_le_maxMonoSum (h t ht)

/-- The best increasing weight ending at `i` is at most the best monotone
weight overall. -/
lemma incSumTo_le_maxMonoSum (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) :
    incSumTo v w i ≤ maxMonoSum v w :=
  incSumTo_le_maxMonoSum_of w fun _ ht => Or.inl (mem_incSetsTo.1 ht).2

/-- The best *decreasing* weight ending at `i` — spelled, as everywhere in
this development, as the increasing weight for `⇑toDual ∘ v` (there is no
separate `decSumTo` definition) — is at most the best monotone weight for
`v` itself. -/
lemma decSumTo_le_maxMonoSum (v : Fin n → β) (w : Fin n → ℝ) (i : Fin n) :
    incSumTo (⇑toDual ∘ v) w i ≤ maxMonoSum v w :=
  incSumTo_le_maxMonoSum_of w fun _ ht =>
    Or.inr (strictAntiOn_iff_strictMonoOn_toDual.2 (mem_incSetsTo.1 ht).2)

end WeightedES
