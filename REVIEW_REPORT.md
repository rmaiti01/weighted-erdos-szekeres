# Statement and verification review

The original review was recorded on 11-12 June 2026. This document summarises its findings and distinguishes what the checks establish. The current workflow and results are available in [GitHub Actions](https://github.com/rmaiti01/weighted-erdos-szekeres/actions).

## Statement correspondence

The implemented theorem is Cambie's normalised finite formulation of Erdős #1026. It does not state the general exact extremal constants.

| Source condition | `WeightedES.erdos_1026` |
| --- | --- |
| Positive integer $k$ | `hk : 0 < k` |
| $k^2$ distinct real values | `x : Fin (k ^ 2) → ℝ`, `Function.Injective x` |
| Positive values | `∀ i, 0 < x i` |
| Sum $1$ | `∑ i, x i = 1` |
| One monotone subsequence | One existential `t`, with increasing or decreasing monotonicity on its index set |
| Weight at least $1/k$ | `(1 : ℝ) / k ≤ ∑ i ∈ t, x i`, for that same `t` |

Distinctness makes strict monotonicity the appropriate rendering. The lower bound excludes the empty subsequence when `k > 0`.

The weighted core uses an injective order map and separate positive weights. The unit-weight corollary gives `n ≤ #t ^ 2`, the symmetric unweighted bound. It does not give separate increasing and decreasing thresholds.

## Mechanical checks

| Check | What it establishes |
| --- | --- |
| `lake build` | Lean accepts the default development against the pinned dependencies. |
| Source scan for `sorry` and `admit` | These placeholders are absent from the main source paths. The guarded axiom checks provide the stronger dependency check for the exported results. |
| `#guard_msgs` around `#print axioms` | Each of the three main results has exactly `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies. |
| Explicit `k = 2` instance | The theorem's hypotheses are jointly satisfiable for `1/10, 2/10, 3/10, 4/10`. |
| `lake build Benchmarks` | The two benchmark exercises elaborate, with intentional proof-placeholder warnings. |

Compilation and axiom checks do not establish correspondence with the informal problem. The explicit instance rules out contradictory hypotheses for that instance; it does not by itself detect a weakened conclusion or prove statement faithfulness.

## Corrections recorded in the original review

- In `sum_le_maxMonoSum` and `le_incSumTo`, the image function was supplied explicitly to resolve underdetermined elaboration and stuck typeclass instances.
- In the square disjointness proof, the available inequality dichotomy was corrected to `Ne.lt_or_gt`.
- In the volume calculation, both subtraction terms were explicitly rewritten.
- In the Cauchy-Schwarz calculation, `simp only` replaced a nonterminal `simp` that could close the goal before subsequent tactics.
- Guarded axiom checks and a concrete instance were added to `Main.lean`.
- The two benchmark files and their separate Lake target were added. The placeholder scan excludes them.
- Documentation was corrected to describe only the symmetric unweighted corollary and to state that the tightness construction is not implemented.
- Full-text third-party captures were removed from tracked files; the source notes retain references.

The original report records successful clean builds and benchmark elaboration after these corrections. That is a historical result, not a claim that every future commit has passed CI.

## Presentation corrections

The documentation revision removes quantitative formalisation-cost estimates because the blow-up proof was not implemented. It also removes the total-line-count comparison with Aristotle: that development proves additional exact-constant results, so the totals do not compare equivalent scopes.

The source notes identify earlier literature, and the commit history records AI-assisted development and review.
