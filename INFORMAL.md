# Erdős #1026: two informal proofs, read the way a formalizer reads them

This document is the first layer of the artifact: the informal mathematics, annotated
with every gap, hidden assumption, and unstated lemma that a Lean formalization must
pay for. The two proofs analyzed here are quoted verbatim in
[sources/SOURCES.md](sources/SOURCES.md); both were posted to the
erdosproblems.com forum within ~18 hours of each other in December 2025 — one found
by an AI prover (Aristotle), one by a human (Koishi Chan) an hour later.

The punchline of the analysis: **the two proofs are "morally the same" (Alexeev's
words), but their formalization costs differ by roughly an order of magnitude, and
the expensive steps of each are precisely the ones the informal text spends the
fewest words on.** Section 4 makes this assessment precise and justifies which proof
the Lean development follows.

## 1. The statement

**Theorem (weighted Erdős–Szekeres; Cambie's form of Erdős #1026).**
Let $x_1, \dots, x_{k^2}$ be distinct positive reals with $\sum_i x_i = 1$. Then
some monotonic subsequence has sum at least $1/k$.

Both proofs actually establish the cleaner, normalization-free core, valid for every
$n$, from which the theorem follows by Cauchy–Schwarz:

**Theorem (ℓ² form).** For distinct positive reals $x_1, \dots, x_n$, writing
$S = S(x)$ for the maximum of $\sum_{r} x_{i_r}$ over monotonic subsequences
$i_1 < i_2 < \cdots$,
$$S^2 \;\ge\; \sum_{i=1}^n x_i^2 .$$

### Formal rendering choices (decisions the informal statement leaves open)

| Informal phrase | Decision in this development | Why |
|---|---|---|
| "sequence $x_1,\dots,x_n$" | `x : Fin n → ℝ` with `Function.Injective x` | matches Mathlib's Erdős–Szekeres idiom (`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`), which quantifies over `Finset` index sets |
| "monotonic subsequence" | `t : Finset (Fin n)` with `StrictMonoOn x ↑t ∨ StrictAntiOn x ↑t` | a subsequence is an index *set* (order inherited from `Fin n`); strictness is free since values are distinct |
| "max over all monotonic subsequences" | `Finset.max'` over the (nonempty) filtered powerset | the empty set is vacuously monotone, so the family is nonempty without case analysis; under positivity it never attains the max, so including it is harmless and kills a side condition |
| "distinct" | `Function.Injective x` | the standing hypothesis both proofs silently rely on (Proof A: ES needs injectivity; Proof B: needed only for the *strict*-monotone rendering used here — rephrased with weak monotonicity the argument needs no distinctness at all, see §3 B2b; with strict monotonicity and repeated values the ℓ² bound is simply false) |
| "positive" | `∀ i, 0 < x i` | see G6/B3: both proofs use positivity in steps that never mention it |

## 2. Proof A — Chan's blow-up argument, annotated

The entire informal proof is six short sentences, quoted below in its four steps; each step is billed.

> **(A1)** "Set $n = k^2$. Take large $N$, and replace each $x_i$ with
> $\lfloor N^2 x_i^2 \rfloor$ perturbations of $x_i$, …"

- **G1 (unspecified construction — perturbations).** *Which* perturbations? Three
  constraints are implicit: (i) all $\sum_i \lfloor N^2x_i^2\rfloor$ new values must
  be globally distinct (else Erdős–Szekeres, applied in (A3), does not apply);
  (ii) each cluster must stay so close to $x_i$ that inter-cluster order relations
  are exactly the order relations of the original values — this needs
  $\delta < \tfrac12 \min_{i\ne j}|x_i - x_j|$, and the minimum gap is positive
  only because finitely many distinct reals have one (a compactness-flavored fact
  that is a real lemma in Lean); (iii) positivity of the perturbed values is *not* actually needed — unweighted
  Erdős–Szekeres is sign-blind — though preserving it costs nothing; the
  original values' positivity enters Proof A only at G6.

> **(A1, continued)** "… with no monotonic subsequence of size
> $\lceil N x_i \rceil + 1$."

- **G2 (hidden theorem — Erdős–Szekeres is tight).** The clause asserts that
  $\lfloor N^2x_i^2\rfloor$ distinct values *can be arranged inside an arbitrarily
  small interval* with longest monotone subsequence at most $\lceil Nx_i\rceil$.
  This is the **tightness construction** for Erdős–Szekeres (an $a \times b$ grid:
  $b$ descending blocks, each an ascending run of $a$ values — longest increasing
  subsequence $a$, longest decreasing $b$), plus the arithmetic
  $\lfloor N^2x_i^2\rfloor \le \lceil Nx_i\rceil^2$. **Mathlib has no such
  construction** (the Archive file proves only the existence direction). One word
  of the informal proof — "with" — is an entire missing library file.

> **(A2)** "As $N \to \infty$, this new sequence's largest monotone subsequence has
> size $NS + O(1)$, where $S$ is the largest sum of the monotonic subsequences of
> the original sequence."

- **G3 (unstated decomposition lemma).** Only the *upper* bound
  $L' \le NS + O(1)$ is used (the lower bound comes from ES in (A3)), and it hides
  a genuine lemma: a monotone subsequence of the blow-up (a) visits clusters in a
  weakly monotone itinerary; (b) uses at most $\lceil Nx_i\rceil$ elements inside
  cluster $i$ — *by the G2 arrangement, and for both directions of monotonicity
  simultaneously*; (c) the set of visited clusters is a monotone subsequence of the
  *original* — by the G1 scale separation; whence
  $L' \le \sum_{\text{visited } i}\lceil Nx_i\rceil \le N\!\!\sum_{\text{visited } i}\!\!x_i + n \le NS + n$,
  where the middle step costs $\lceil y\rceil < y + 1$ summed $n$ times, and the
  last step is the definition of $S$ applied to the itinerary. The constant in
  $O(1)$ is $n$ — fine here, but the informal notation conceals that it must not
  depend on $N$.

> **(A3)** "By Erdos-Szekeres, we have
> $(NS + O(1))^2 \ge \sum_i \lfloor N^2 x_i^2 \rfloor$."

- **G4 (quantitative reshaping of the library lemma).** Mathlib's statement is
  existential: `r * s < card → (increasing > r) ∨ (decreasing > s)`. The proof
  needs its contrapositive with $r = s = L'$: *the square of the longest monotone
  subsequence length is at least the number of elements*. Routine, but it is the
  difference between the lemma the library exports and the inequality the paper
  uses — a reshaping step automation must bridge.

> **(A4)** "So taking $N \to \infty$ we obtain $S^2 \ge \sum_i x_i^2$. Now
> Cauchy-Schwarz gives $S \ge n^{-1/2} = k^{-1}$."

- **G5 (limit bookkeeping).** From $(NS+n)^2 \ge \sum_i (N^2x_i^2 - 1)$:
  divide by $N^2$, send $N\to\infty$ along naturals. In Lean this is either a
  `Filter.Tendsto` argument or an explicit $\forall \varepsilon$ computation; both
  drag in real analysis to finish a combinatorial theorem.
- **G6 (silent positivity and sign).** $S \ge 0$ (needed for
  $S^2 \ge 1/n \Rightarrow S \ge 1/\sqrt n$) holds because monotone subsequences of
  positive values have positive sums — this is the *only* use of positivity in
  Proof A, yet the word "positive" never appears in the proof.
- **G7 (existence of a maximizer).** The conclusion is "there is a monotone
  subsequence with sum ≥ 1/k", but the argument bounds the *supremum* $S$. One
  needs that the max is attained — finitely many subsequences, nonempty family —
  which is exactly the API a formal definition of $S$ must provide.

## 3. Proof B — Aristotle's rectangle packing (per llllvvuu), annotated

> **(B-text)** "Let $S_i$ be the maximal sum over all increasing subsequences
> ending in $x_i$, and $T_i$ the same for decreasing. Consider the squares
> $(S_i - x_i, T_i - x_i) \to (S_i, T_i)$. These are disjoint and contained in the
> rectangle $(0,0) \to (\max_i S_i, \max_i T_i)$. Hence
> $(\max_i S_i)(\max_i T_i) \ge \sum_i x_i^2 \ge 1/k^2$."

- **B1 (well-definedness).** Each $S_i$ is a max over a finite *nonempty* family —
  nonempty because the singleton $\{i\}$ qualifies. This mirrors, weight-for-length,
  the `incSequencesTo`/`maxIncSequencesTo` scaffolding of Mathlib's Archive proof
  of Erdős–Szekeres: **replace `Finset.card` by `∑ x` and Seidenberg's proof
  becomes Aristotle's.** Recognizing this is what makes the formalization short.
- **B2a ("these are disjoint", part one — an unstated extension lemma).** For
  $i \ne j$ (say $i < j$ positionally) with $x_i < x_j$: any increasing
  subsequence ending at $i$ extends by $j$, so $S_j \ge S_i + x_j$. Formal cost:
  the one-line "extends by $j$" is an `insert` into a `Finset` with proofs that
  `IsGreatest` and `StrictMonoOn` survive the insertion — in the development this
  is its own lemma (`insert_mem_incSetsTo`), feeding the growth inequality
  (`incSumTo_add_le`).
- **B2b ("these are disjoint", part two — the dichotomy and the disjointness
  inference).** The growth inequality separates the *first* coordinates' intervals
  $(S_i - x_i, S_i]$ and $(S_j - x_j, S_j]$; if instead $x_j < x_i$, the
  symmetric argument for $T$ separates the second coordinates
  (`square_disjoint_of_lt`). The dichotomy ($x_i < x_j$ or $x_j < x_i$) is **the
  only place Proof B uses distinctness** — and had the proof been phrased with
  *weakly* monotone subsequences, it would need no distinctness at all: the weak
  dichotomy $x_i \le x_j \lor x_j \le x_i$ is unconditional, and the weak
  extension lemma still pushes $S_j - x_j \ge S_i$, so the intervals stay
  disjoint even under ties. (For the *strict*-monotone rendering used here the
  hypothesis is genuinely needed: with $n = 2$ equal values of weight $1$ the ℓ²
  bound fails.) The informal text inherits distinctness from the problem
  statement without noticing the proof barely needs it.
- **B3 (containment + nondegeneracy).** $S_i - x_i \ge 0$ because the singleton is
  a candidate; the square is *nonempty* because $x_i > 0$ — the only use of
  positivity, again unannounced.
- **B4 (the geometrically obvious step is the formally expensive one).**
  "Disjoint squares in a rectangle, hence the areas sum up" has no elementary
  one-liner in Lean: it is 2-dimensional Lebesgue measure — measurability of
  `Ioc ×ˢ Ioc`, `volume_prod`, additivity over a pairwise-disjoint `Finset`-indexed
  union, monotonicity, and `ENNReal ↔ ℝ` coercion management. This single
  informal "Hence" is the bulk of the formal proof — and the inverse is true of
  every other step. *Where the informal proof is short, the formal proof is long,
  and vice versa.*
- **B5 (finish).** $\max_i S_i \le S$ and $\max_i T_i \le T \le S$ (every
  increasing-ending-at-$i$ subsequence is monotone), so
  $S^2 \ge (\max_i S_i)(\max_i T_i) \ge \sum_i x_i^2$ — the ℓ² form; then
  Cauchy–Schwarz $(\sum x_i)^2 \le n \sum x_i^2$ (the Mathlib lemma is
  `Finset.sum_mul_sq_le_sq_mul_sq` — no "Cauchy" or "Schwarz" in the name;
  `exact?` does retrieve it, but only once the goal is already massaged into
  the lemma's exact `(∑ f·g)² ≤ (∑ f²)(∑ g²)` shape) and G7's maximizer API
  as in Proof A.

## 4. Formalizability assessment

| Cost driver | A (blow-up) | B (rectangle) |
|---|---|---|
| New definitions beyond $S(x)$ | blown-up sequence, per-cluster grids | $S_i$, $T_i$ (mirrors Archive scaffolding) |
| Missing library material | **ES tightness construction** (new file) | none (assembled from measure theory) |
| Analysis content | limit $N\to\infty$, floor/ceiling error terms | none — fully finite |
| Library dependencies | Archive's `erdos_szekeres` (import friction: it lives outside Mathlib proper) | `MeasureTheory.volume` on $\mathbb{R}^2$ |
| Delicate constructions | perturbation scheme with three simultaneous constraints (G1) | none |
| Estimated size | ~3–4× Proof B | baseline |

**Decision: formalize Proof B as the main development.** Proof A's costliest
hidden substructure — the tightness construction (G2) — is *not* formalized
here; it is recorded in §6 as the sharpest library gap this analysis surfaced,
and is the natural standalone follow-up (PR-able to Mathlib independently of
this development). Proof B is finite, construction-free, and its only expensive step
(B4) is expensive in a *library-supported* way. Proof A is the better story but the
worse engineering: three of its four steps each conceal a lemma, and one
conceals a missing library file.

For calibration: Aristotle's machine-generated Lean proof of the same
rectangle-packing argument is **3,658 lines** (it also proves the harder exact
constant $c(k^2+2a+1) = k/(k^2+a)$, but its lower-bound core alone is far larger
than this entire development). The aim here is the same mathematics at
human-readable scale.

## 5. Sidebar: a false strengthening, and why gap-hunting matters

Within two hours of Cambie's conjecture being posted, a natural strengthening was
proposed (Kovač): *the monotone subsequence can be taken to have length $k$ as
well.* Cambie refuted it within three hours: normalize
$k\binom{n}{2}, 1, 2, \dots, n-1$ (dividing by $(k+1)\binom n2$, $n = k^2$,
$k \ge 3$); any subsequence avoiding the huge first term has sum $< 1/k$, while any
monotone subsequence containing it has length $\le 2$. The lesson is the same one
G1–G7 teach: plausible-sounding strengthenings and "obvious" steps are exactly
where informal arguments fail, and a formalizer's first job is to find out which
kind of sentence they are reading.

## 6. Library gaps surfaced by this analysis

1. **Erdős–Szekeres tightness** is absent from Mathlib (G2). Not formalized
   here (this development follows Proof B, which does not need it); it is the
   sharpest gap on this list and PR-able to Mathlib independently.
2. **Erdős–Szekeres lives in `Archive/`**, not Mathlib proper, with `private`
   scaffolding (`incSequencesTo` etc.) that cannot be reused downstream even
   though Proof B is its weighted shadow (B1). The weighted generalization
   formalized here subsumes the *symmetric form* of the unweighted statement
   (set the weights $w \equiv 1$, keeping the order map injective); the
   asymmetric $r$/$s$ form would need the unexported product inequality
   $(\max_i S_i)(\max_i T_i) \ge \sum_i w_i^2$ rather than its symmetrized
   $S^2$ corollary.
3. **No "disjoint boxes have summable area" convenience lemma** (B4): the fact is
   assembled from product-measure primitives each time it is needed.
