/-
Copyright (c) 2026 Rajarshi Maiti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Maiti
-/
import Mathlib

/-!
# Benchmark A1 — vacuous `StrictMonoOn` through a `Finset` coercion

**Provenance:** `FAILURE_ATLAS.md`, entry A1 (hit while proving
`WeightedES.empty_mem_monoSubseqs` in `WeightedErdosSzekeres/Defs.lean`).

**Task for the tactic/prover under evaluation:** replace the `sorry` below.

Known data points (Lean `v4.29.0`, Mathlib `v4.29.0`):
* `simp` alone fails — after normalizing `↑(∅ : Finset _)` to `(∅ : Set _)`
  there is no `@[simp]` lemma rewriting `StrictMonoOn f ∅`;
* the human fix unfolds the binder by hand: `fun a ha => by simp at ha`.
-/

example {n : ℕ} (v : Fin n → ℝ) : StrictMonoOn v ↑(∅ : Finset (Fin n)) := by
  sorry
