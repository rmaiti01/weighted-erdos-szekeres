# Informal proofs of the weighted Erdős-Szekeres bound

This note records the formalisation obligations in two published arguments. The square-packing argument is implemented in this repository. The blow-up argument is analysed but not implemented. Sources are listed in [sources/SOURCES.md](sources/SOURCES.md).

## 1. The statement

For a positive integer $k$, let $x_1,\ldots,x_{k^2}$ be distinct positive reals with sum $1$. Cambie's formulation of Erdős #1026 asks for a monotone subsequence with sum at least $1/k$.

Both arguments establish the weighted core: if $S$ is the maximum sum over monotone subsequences of distinct positive reals $x_1,\ldots,x_n$, then

$$\sum_{i=1}^n x_i^2 \le S^2.$$

Cauchy-Schwarz gives $1\le k^2\sum_i x_i^2\le k^2S^2$, hence $S\ge 1/k$.

| Source condition | Lean rendering |
| --- | --- |
| $k$ is a positive integer | `k : ℕ`, `hk : 0 < k` |
| $k^2$ terms | `x : Fin (k ^ 2) → ℝ` |
| Distinct terms | `Function.Injective x` |
| Positive terms | `∀ i, 0 < x i` |
| Sum $1$ | `∑ i, x i = 1` |
| A monotone subsequence | `t : Finset (Fin (k ^ 2))`, with `StrictMonoOn x ↑t ∨ StrictAntiOn x ↑t` |
| Subsequence sum at least $1/k$ | `(1 : ℝ) / k ≤ ∑ i ∈ t, x i` |

The order on the index set is inherited from `Fin`. Strict monotonicity agrees with weak monotonicity when the values are distinct. The empty set is allowed in the maximum, ensuring a nonempty candidate family and a nonnegative maximum. It cannot witness the normalised conclusion because $1/k>0$.

The implemented weighted theorem separates `v`, the order map, from `w`, the weight map. This supports an arbitrary linearly ordered codomain and recovers the unweighted bound by setting `w ≡ 1` while keeping `v` injective.

## 2. Blow-up argument

Koishi Chan's argument replaces each $x_i$ by $m_i=\lfloor N^2x_i^2\rfloor$ nearby values. Each cluster is arranged to have no monotone subsequence longer than $a_i=\lceil Nx_i\rceil$. A monotone subsequence in the expanded sequence has length at most $NS+n$. The unweighted Erdős-Szekeres bound then gives

$$\sum_i\lfloor N^2x_i^2\rfloor\le (NS+n)^2.$$

Divide by $N^2$ and let $N\to\infty$.

The following obligations would be needed for a formalisation.

| ID | Obligation |
| --- | --- |
| G1 | Construct globally distinct perturbations in separated intervals around the original values. For two or more values, a positive minimum pairwise gap supplies the separation; smaller sequences need separate treatment. |
| G2 | Construct a sequence of $m_i\le a_i^2$ values whose increasing and decreasing subsequences both have length at most $a_i$. An $a_i$ by $a_i$ extremal arrangement, followed by restriction and rescaling, supplies this. |
| G3 | Prove that the cluster indices visited by a monotone subsequence form a monotone subsequence of the original sequence. Sum the within-cluster bounds to obtain $L\le\sum_{i\text{ visited}}\lceil Nx_i\rceil\le NS+n$. |
| G4 | Convert the finite quantitative Erdős-Szekeres theorem to the inequality $m\le L^2$, where $L$ is the longest monotone subsequence length. |
| G5 | Bound floor and ceiling errors uniformly in $N$, then pass to the limit. |
| G6 | Track signs when using ceilings, squaring inequalities, and extracting the final lower bound. Positivity of the original values supports the construction; nonnegativity of $S$ also follows from allowing the empty subsequence. |
| G7 | Prove that the maximum $S$ is attained and use its index set as the witness. |

The tightness construction in G2 is not implemented here. The original project review did not find a reusable version in the pinned Mathlib checkout; this is a statement about that checkout, not later versions of Mathlib.

## 3. Square-packing argument

Let $S_i$ and $T_i$ be the maximum increasing and decreasing weights ending at index $i$. Associate to $i$ the half-open square

$$Q_i=(S_i-w_i,S_i]\times(T_i-w_i,T_i].$$

Each square has area $w_i^2$. The squares are pairwise disjoint and lie in $(0,S]\times(0,S]$, where $S$ is the maximum monotone weight. Finite additivity and containment give $\sum_iw_i^2\le S^2$.

| ID | Obligation | Implemented declarations |
| --- | --- | --- |
| B1 | Endpoint candidate families are nonempty because each contains its singleton; their maxima are attained. | `singleton_mem_incSetsTo`, `exists_incSumTo` |
| B2a | If `i < j` and `v i < v j`, insert `j` into an increasing subsequence ending at `i`. Prove the greatest-element and monotonicity conditions, then the growth inequality. | `insert_mem_incSetsTo`, `incSumTo_add_le` |
| B2b | For distinct indices, injectivity makes the order values unequal. Depending on their comparison, the growth inequality separates either the horizontal or vertical intervals. | `square_disjoint_of_lt`, `pairwiseDisjoint_square` |
| B3 | Singleton weights bound the lower endpoints below by zero; endpoint maxima are at most the global monotone maximum. | `self_le_incSumTo`, `incSumTo_le_maxMonoSum`, `incSumTo_toDual_comp_le_maxMonoSum`, `square_subset` |
| B4 | Compute product volumes, add them over a finite disjoint union, use containment, and transfer the inequality from `ℝ≥0∞` to `ℝ`. | `volume_square`, `sum_sq_le_sq_maxMonoSum` |
| B5 | Choose a maximiser and apply Cauchy-Schwarz for the normalised statement. | `exists_maxMonoSum`, `erdos_1026` |

Injectivity is used in the disjointness proof. It is necessary for this strict-monotonicity statement: two equal order values with unit weights would have maximum strict-monotone weight $1$, contradicting $2\le1^2$.

Containment does not require positivity. In the implemented area argument, positivity permits `ENNReal.ofReal (w i) * ENNReal.ofReal (w i)` to be rewritten as `ENNReal.ofReal (w i ^ 2)`. The theorem retains strictly positive weights; no weakening is claimed here.

Half-open intervals make adjacent boundaries disjoint as sets, avoiding a separate almost-everywhere disjointness argument. The area proof uses `Measure.prod_prod`, `Real.volume_Ioc`, `measure_biUnion_finset`, and `measure_mono`. The Cauchy-Schwarz lemma is `Finset.sum_mul_sq_le_sq_mul_sq`.

## 4. Choice of argument

| Requirement | Blow-up argument | Square-packing argument |
| --- | --- | --- |
| New constructions | Extremal clusters, perturbations, concatenation | Endpoint maxima and half-open squares |
| Analytic step | Limit with floor and ceiling errors | Finite product-measure calculation |
| Main supporting result | Finite Erdős-Szekeres plus its tightness construction | Mathlib measure and finite-sum APIs |
| Status in this repository | Analysed only | Implemented |

The square-packing argument was chosen because its remaining obligations could be assembled from the pinned library APIs without the cluster construction or limiting argument. No measured cost ratio is available: the blow-up proof was not implemented.

## 5. A false strengthening

The source discussion also asks whether the subsequence can have length $k$. For $n=k^2$ and $k\ge3$, normalise the sequence

$$k\binom n2,\ 1,\ 2,\ldots,n-1$$

by $(k+1)\binom n2$. A subsequence avoiding the first term has sum at most $1/(k+1)<1/k$. A monotone subsequence containing the first term has length at most $2$. Thus the length requirement fails. This counterexample is discussed here but not formalised.

## 6. Library observations

The original review recorded the following observations against Mathlib `v4.29.0`:

- The finite quantitative Erdős-Szekeres theorem is in `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`, with private endpoint scaffolding. Mathlib also contains an infinitary subsequence result.
- No reusable finite tightness construction was identified for G2.
- The square area bound was assembled from existing product-measure, finite-additivity, and monotonicity lemmas.

The implemented corollary is the symmetric bound `n ≤ #t ^ 2`. Separate increasing and decreasing thresholds would require an additional result retaining the product of the two endpoint maxima.
