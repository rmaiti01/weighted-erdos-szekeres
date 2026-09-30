# Weighted Erdős-Szekeres in Lean 4

[![CI](https://github.com/rmaiti01/weighted-erdos-szekeres/actions/workflows/ci.yml/badge.svg)](https://github.com/rmaiti01/weighted-erdos-szekeres/actions/workflows/ci.yml)

A Lean 4 formalisation of Cambie's formulation of [Erdős problem #1026](https://www.erdosproblems.com/1026), using the published square-packing argument. Author: Rajarshi Maiti.

For a positive integer $k$, any sequence of $k^2$ distinct positive reals summing to $1$ has a monotone subsequence whose sum is at least $1/k$.

The development proves a more general weighted inequality, then derives this result and the symmetric unweighted Erdős-Szekeres bound. It also includes an analysis of two informal proofs, a statement review, and two tactic benchmark exercises.

## Build

Install [Lean through elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/rmaiti01/weighted-erdos-szekeres.git
cd weighted-erdos-szekeres
lake exe cache get
lake build
```

The project pins Lean and Mathlib to `v4.29.0`. The default target is `WeightedErdosSzekeres`. The benchmark exercises are separate:

```bash
lake build Benchmarks
```

**Both benchmark files contain intentional `sorry` placeholders.** They are exercises for evaluating tactics, not completed proofs, and are excluded from the default target.

## Main results

Let `v : Fin n → β` be injective, with `β` linearly ordered, and let `w : Fin n → ℝ` be positive weights. `maxMonoSum v w` is the largest sum of weights over an index set on which `v` is strictly increasing or strictly decreasing.

```lean
theorem sum_sq_le_sq_maxMonoSum (v : Fin n → β) (w : Fin n → ℝ)
    (hv : Function.Injective v) (hw : ∀ i, 0 < w i) :
    ∑ i, w i ^ 2 ≤ maxMonoSum v w ^ 2
```

All declarations below are in the `WeightedES` namespace.

| Declaration | Result |
| --- | --- |
| `sum_sq_le_sq_maxMonoSum` | The weighted inequality above. |
| `erdos_1026` | Set `v = w = x` and apply Cauchy-Schwarz to obtain the normalised $k^2$ result. |
| `exists_monoSubseq_le_sq_card` | Set `w ≡ 1` to obtain a monotone subsequence `t` with `n ≤ #t ^ 2`. |

The last result is the symmetric unweighted bound. The asymmetric bounds for separate increasing and decreasing lengths are not formalised here.

## Proof structure

| File | Contents |
| --- | --- |
| [Defs.lean](WeightedErdosSzekeres/Defs.lean) | Monotone index sets, maximum weights, maximiser existence, and the subsequence extension inequality. |
| [Squares.lean](WeightedErdosSzekeres/Squares.lean) | Half-open squares defined by the best increasing and decreasing weights ending at each index; pairwise disjointness and containment. |
| [Area.lean](WeightedErdosSzekeres/Area.lean) | Square volumes, finite additivity, and the weighted inequality via two-dimensional Lebesgue measure. |
| [Main.lean](WeightedErdosSzekeres/Main.lean) | Both corollaries, a concrete instance of the hypotheses, and guarded axiom checks. |

The order map and weights are separate. Increasing-subsequence lemmas apply to decreasing subsequences through `OrderDual`, without changing the weights.

## Checks and scope

CI builds the main target, checks its source for `sorry` and `admit`, and elaborates the two benchmark exercises. `Main.lean` uses `#guard_msgs` with `#print axioms` to check that the three main results depend on exactly `propext`, `Classical.choice`, and `Quot.sound`.

The explicit instance at `k = 2` uses `1/10, 2/10, 3/10, 4/10`. It establishes that the hypotheses are jointly satisfiable for this instance. It does not establish that the Lean statement matches the source problem; that requires the mathematical review in [REVIEW_REPORT.md](REVIEW_REPORT.md).

This repository formalises Cambie's finite formulation. It does not formalise the exact extremal constants for general sequence lengths. The referenced Aristotle development proves additional results, so its total line count is not a like-for-like comparison.

## Supporting documents

- [INFORMAL.md](INFORMAL.md): obligations in the blow-up and square-packing arguments, with links to the implemented lemmas.
- [FAILURE_ATLAS.md](FAILURE_ATLAS.md): two tactic/elaboration failures and one local filesystem issue.
- [REVIEW_REPORT.md](REVIEW_REPORT.md): statement correspondence, axiom checks, and recorded build corrections.
- [WORK_SAMPLE.md](WORK_SAMPLE.md): a short description of the implemented work.
- [sources/SOURCES.md](sources/SOURCES.md): mathematical sources and attribution.

## Attribution and licence

The mathematical argument follows the square-packing proof explained by llllvvuu from Aristotle's output, using Seidenberg-style endpoint maxima. The alternative blow-up argument is due to Koishi Chan; the source notes give its earlier literature references.

The Lean implementation is a separate development. AI coding tools assisted development and review, as recorded in the commit history.

Original code is distributed under [Apache 2.0](LICENSE). Third-party proofs and articles are linked in the source notes rather than included as full-text copies.
