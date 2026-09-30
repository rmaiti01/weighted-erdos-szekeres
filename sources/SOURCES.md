# Mathematical sources

This repository formalises Cambie's normalised finite formulation of Erdős #1026. The argument is existing mathematics; the Lean implementation is a separate development. Sources below were identified in the original June 2026 review.

## Problem and discussion

- [Erdős problem #1026](https://www.erdosproblems.com/1026): the problem page and references.
- [Forum thread](https://www.erdosproblems.com/forum/thread/1026): Stijn Cambie's formulation, Koishi Chan's blow-up proof, llllvvuu's explanation of the square-packing argument, and the counterexample to the length-$k$ strengthening.
- [Terence Tao, The story of Erdős problem #1026](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/), 8 December 2025: an account of the automated proof, the subsequent discussion, and the earlier literature. The URL's `126` slug is the published URL.

Cambie's formulation asks whether $k^2$ distinct positive reals summing to $1$ have a monotone subsequence of sum at least $1/k$. That is the statement exported as `WeightedES.erdos_1026`.

## Proof attribution

- **Square packing:** llllvvuu's forum explanation of Aristotle's proof, using Seidenberg-style maxima for increasing and decreasing subsequences ending at each index. This is the argument implemented here.
- **Blow-up argument:** Koishi Chan's forum post. It replaces each value with a small extremal cluster and applies the unweighted theorem before passing to a limit. It is analysed in `INFORMAL.md` but not implemented.
- **Earlier literature:** Jonathan Tidor, Victor Wang, and Ben Yang, [1-color-avoiding paths, special tournaments, and incidence geometry](https://arxiv.org/abs/1608.04153), 2016, Section 3. The source discussion connects the blow-up argument to this paper and its attribution to A. Z. Wagner.
- **Survey:** J. M. Steele, Variations on the monotone subsequence theme of Erdős and Szekeres, in Discrete Probability and Algorithms, IMA Vol. 72, Springer, 1995, pp. 111-131.

The normalised result predates the December 2025 forum discussion. This repository makes no claim to have discovered it.

## Other Lean development

[Aristotle's generated proof](https://github.com/plby/lean-proofs/blob/9f90812fc849fa4b6eb6f6c93ed3aa74a0856321/src/v4.24.0/ErdosProblems/Erdos1026.lean) is linked at a fixed commit. It includes exact-constant results beyond this repository's normalised theorem. Total file sizes therefore do not give a like-for-like measure of proof compression.

## Mathlib context

The project pins Mathlib to `v4.29.0`, commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`.

- [`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`](https://github.com/leanprover-community/mathlib4/blob/8a178386ffc0f5fef0b77738bb5449d50efeea95/Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean), by Bhavik Mehta: the finite quantitative Erdős-Szekeres theorem and private endpoint scaffolding.
- `Mathlib/Order/OrderIsoNat.lean`: an infinitary subsequence result.
- The implemented area argument uses the existing product-volume, interval-volume, finite-additivity, and measure-monotonicity APIs. The original review did not identify a reusable finite tightness construction for the alternative blow-up proof.

## Redistribution

The repository links to third-party articles, forum posts, and generated code. It does not distribute full-text captures of those sources. The Apache 2.0 licence applies to the original code in this repository.
