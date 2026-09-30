# Tactic and build failures

This note records two tactic/elaboration failures encountered in the formalisation and one local filesystem issue. The tactic observations concern Lean and Mathlib `v4.29.0`. They do not establish failure rates for an automated prover.

## A1. Empty-set monotonicity

**Goal:**

```lean
StrictMonoOn v ↑(∅ : Finset (Fin n))
```

**Attempt:** `simp`.

**Observed result:** the coercion is normalised to the empty `Set`, but the monotonicity goal remains. The simplifier does not close it with the available simp lemmas in this context.

**Fix:** introduce the membership hypothesis, then simplify that contradiction:

```lean
fun a ha => by simp at ha
```

This term is used in `empty_mem_monoSubseqs`. The extracted exercise is [A1_StrictMonoOnEmptyCoe.lean](Benchmarks/A1_StrictMonoOnEmptyCoe.lean).

## A2. Maximum through an image definition

**Goal:**

```lean
∑ i ∈ t, w i ≤ maxMonoSum v w
```

Here `maxMonoSum` wraps `Finset.max'` over an image of weighted sums.

**Attempt:**

```lean
le_max' _ _ (mem_image_of_mem _ (mem_monoSubseqs.2 ht))
```

**Observed result:** the inferred image function remains underdetermined, and the term does not match the goal. Unfolding `maxMonoSum` alone left a stuck `DecidableEq` instance in the recorded clean build.

**Fix:** unfold the wrapper and provide the image function explicitly:

```lean
unfold maxMonoSum
exact le_max' _ _ <|
  mem_image_of_mem (fun t => ∑ i ∈ t, w i) <| mem_monoSubseqs.2 ht
```

This is the implementation of `sum_le_maxMonoSum`; `le_incSumTo` uses the same pattern. The extracted exercise is [A2_LeMaxThroughDef.lean](Benchmarks/A2_LeMaxThroughDef.lean).

## E1. iCloud-evicted checkout

The original local build stalled with no Lean workers. A process sample showed Lake waiting on `git diff`; file inspection showed that the Mathlib checkout carried macOS `dataless` flags. Reads were waiting for iCloud to restore evicted files.

The verification build was moved to a fresh checkout outside the synced directory. This was a filesystem issue, not evidence of slow theorem elaboration.

## Benchmark status

The two exercises contain intentional `sorry` placeholders and are excluded from the default build. `lake build Benchmarks` checks that they elaborate against the pinned toolchain; it does not prove their targets or reproduce the failed attempts automatically.
