# Lean 4 work sample

Author: Rajarshi Maiti. Repository: [weighted-erdos-szekeres](https://github.com/rmaiti01/weighted-erdos-szekeres).

## Implemented work

Formalised Cambie's formulation of Erdős #1026 using the published square-packing argument. The main theorem bounds the sum of squared positive weights by the square of the maximum monotone subsequence weight, for an injective order map into any linearly ordered type.

- Defined monotone subsequences as `Finset` index sets and proved existence of maximisers.
- Proved that an increasing subsequence ending at `i` can be extended by a later index `j` with larger order value. Derived `incSumTo v w i + w j ≤ incSumTo v w j`.
- Used `OrderDual` for the decreasing case while keeping the weights unchanged.
- Defined half-open squares and proved pairwise disjointness and containment.
- Used Mathlib's product measure API and finite additivity to obtain the weighted inequality.
- Applied Cauchy-Schwarz to obtain #1026 and unit weights to obtain the symmetric unweighted bound.

## Review and reproducibility

The default target includes guarded axiom checks for all three main results and an explicit instance of the hypotheses. CI builds the development and checks its source for proof placeholders.

[INFORMAL.md](INFORMAL.md) records the obligations in two informal proofs. [REVIEW_REPORT.md](REVIEW_REPORT.md) maps the source statement to its Lean rendering and records build corrections. [FAILURE_ATLAS.md](FAILURE_ATLAS.md) describes two failed tactic/elaboration attempts and their fixes. The corresponding [benchmark exercises](Benchmarks/) contain intentional `sorry` placeholders and are built separately.

## Scope

This is a formalisation of an existing mathematical argument. The blow-up proof, its tightness construction, and the exact extremal constants for general sequence lengths are not implemented. AI coding tools assisted development and review. The [README](README.md#build) gives build commands and the [source notes](sources/SOURCES.md) give attribution.

Contact: [rmaiti7@gmail.com](mailto:rmaiti7@gmail.com).
