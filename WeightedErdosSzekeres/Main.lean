/-
Copyright (c) 2026 Rajarshi Maiti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Maiti
-/
import WeightedErdosSzekeres.Area

/-!
# Main results

* `WeightedES.erdos_1026` — **Erdős problem #1026** in Cambie's form: among
  distinct positive reals `x₁, …, x_{k²}` summing to `1` some monotone
  subsequence has sum at least `1/k`. Cauchy–Schwarz applied to the ℓ² form.
* `WeightedES.exists_monoSubseq_le_sq_card` — the symmetric form of classical
  Erdős–Szekeres, recovered from the same ℓ² form by taking unit weights:
  among `n` distinct values some monotone subsequence `t` has `n ≤ #t ^ 2`.

The file ends with a satisfiability witness (the hypotheses of `erdos_1026`
are jointly realizable, so the theorem is not vacuous) and `#guard_msgs`
axiom audits pinning every headline result to the three standard axioms.
-/

open Finset

namespace WeightedES

variable {n : ℕ} {β : Type*} [LinearOrder β]

/-- **Erdős problem #1026** (Cambie's form; weighted Erdős–Szekeres).
If `x₁, …, x_{k²}` are distinct positive reals with `∑ xᵢ = 1`, then some
monotone subsequence has sum at least `1/k`. -/
theorem erdos_1026 {k : ℕ} (hk : 0 < k) (x : Fin (k ^ 2) → ℝ)
    (hinj : Function.Injective x) (hpos : ∀ i, 0 < x i)
    (hsum : ∑ i, x i = 1) :
    ∃ t : Finset (Fin (k ^ 2)),
      (StrictMonoOn x ↑t ∨ StrictAntiOn x ↑t) ∧ (1 : ℝ) / k ≤ ∑ i ∈ t, x i := by
  obtain ⟨t, ht, hts⟩ := exists_maxMonoSum x x
  refine ⟨t, ht, hts ▸ ?_⟩
  set S := maxMonoSum x x with hS
  have hS0 : 0 ≤ S := maxMonoSum_nonneg x x
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  -- Cauchy–Schwarz: 1 = (∑ xᵢ)² ≤ k² · ∑ xᵢ².
  have hcs : (1 : ℝ) ≤ (k : ℝ) ^ 2 * ∑ i, x i ^ 2 := by
    calc (1 : ℝ) = (∑ i, x i * 1) ^ 2 := by simp [hsum]
      _ ≤ (∑ i, x i ^ 2) * ∑ _i : Fin (k ^ 2), (1 : ℝ) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq univ x fun _ => (1 : ℝ)
      _ = (k : ℝ) ^ 2 * ∑ i, x i ^ 2 := by
          simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
          push_cast
          ring
  -- The ℓ² bound: ∑ xᵢ² ≤ S².
  have hl2 : ∑ i, x i ^ 2 ≤ S ^ 2 := sum_sq_le_sq_maxMonoSum x x hinj hpos
  -- Hence (S·k)² ≥ 1 with S·k ≥ 0, so S·k ≥ 1.
  rw [div_le_iff₀ hk']
  have hSk : 0 ≤ S * k := mul_nonneg hS0 hk'.le
  have hsq : 1 ≤ (S * k) ^ 2 := by
    calc (1 : ℝ) ≤ (k : ℝ) ^ 2 * ∑ i, x i ^ 2 := hcs
      _ ≤ (k : ℝ) ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_left hl2 (sq_nonneg _)
      _ = (S * k) ^ 2 := by ring
  exact (one_le_sq_iff₀ hSk).1 hsq

/-- Classical **Erdős–Szekeres** (symmetric form), recovered from the
weighted theorem with unit weights: among `n` distinct values, some monotone
subsequence `t` has `n ≤ #t ^ 2` — i.e. a monotone subsequence of length at
least `√n`. (The asymmetric `r`/`s` form is *not* claimed here: bounding both
ending-at-`i` quantities by `maxMonoSum` symmetrizes the rectangle.) -/
theorem exists_monoSubseq_le_sq_card (v : Fin n → β) (hv : Function.Injective v) :
    ∃ t : Finset (Fin n), (StrictMonoOn v ↑t ∨ StrictAntiOn v ↑t) ∧ n ≤ #t ^ 2 := by
  obtain ⟨t, ht, hts⟩ := exists_maxMonoSum v fun _ => (1 : ℝ)
  refine ⟨t, ht, ?_⟩
  have hl2 := sum_sq_le_sq_maxMonoSum v (fun _ => (1 : ℝ)) hv fun _ => one_pos
  rw [← hts] at hl2
  have : (n : ℝ) ≤ (#t : ℝ) ^ 2 := by simpa using hl2
  exact_mod_cast this

/-! ### Satisfiability witness

A vacuously true theorem would survive `lake build`; this example is the
defense. It instantiates every hypothesis of `erdos_1026` at `k = 2` with four
explicit distinct positive reals summing to `1`, so the hypotheses are jointly
realizable and the theorem has nonvacuous content. -/

example :
    ∃ t : Finset (Fin (2 ^ 2)),
      (StrictMonoOn ![(1 : ℝ)/10, 2/10, 3/10, 4/10] ↑t ∨
        StrictAntiOn ![(1 : ℝ)/10, 2/10, 3/10, 4/10] ↑t) ∧
      (1 : ℝ) / 2 ≤ ∑ i ∈ t, ![(1 : ℝ)/10, 2/10, 3/10, 4/10] i :=
  erdos_1026 two_pos ![(1 : ℝ)/10, 2/10, 3/10, 4/10]
    (by intro i j hij; fin_cases i <;> fin_cases j <;> revert hij <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by show (∑ i : Fin 4, _) = 1
        rw [Fin.sum_univ_four]
        show (1 : ℝ)/10 + 2/10 + 3/10 + 4/10 = 1
        norm_num)

/-! ### Axiom audits

Each headline result depends on exactly the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no holes, no extra axioms.
CI rebuilds this file, so these `#guard_msgs` checks are enforced on every
push. -/

/-- info: 'WeightedES.sum_sq_le_sq_maxMonoSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_sq_le_sq_maxMonoSum

/-- info: 'WeightedES.erdos_1026' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erdos_1026

/-- info: 'WeightedES.exists_monoSubseq_le_sq_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_monoSubseq_le_sq_card

end WeightedES
