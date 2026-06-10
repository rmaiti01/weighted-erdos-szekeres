# Weighted Erdős–Szekeres, by hand
### Erdős problem #1026, formalized the way a human would write it — with a referee's report on the informal proofs and a failure atlas for the automation

In December 2025, [Erdős problem #1026](https://www.erdosproblems.com/1026)
([Tao's account](https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/))
was resolved twice in one hour: first autonomously in Lean by the AI prover
Aristotle ([3,658 machine-generated lines](https://github.com/plby/lean-proofs/blob/9f90812fc849fa4b6eb6f6c93ed3aa74a0856321/src/v4.24.0/ErdosProblems/Erdos1026.lean)),
then by Koishi Chan, a human, in four sentences on a forum. The mathematical
core is **Cambie's conjecture**, open since it was raised in Steele's 1995
Erdős–Szekeres survey:

> If `x₁, …, x_{k²}` are distinct positive reals with `∑ xᵢ = 1`, some
> monotonic subsequence has sum at least `1/k`.

This repository is **not** primarily a formalization of that theorem — it is a
demonstration of the work *around* a formalization, the part that doesn't
survive into a clean final proof script:

1. **[INFORMAL.md](INFORMAL.md)** — the two informal proofs (Chan's blow-up;
   Aristotle's rectangle packing, as explained by llllvvuu), quoted verbatim
   and read the way a formalizer must read them: every gap, hidden assumption,
   and unstated lemma is flagged and priced. The punchline: the proofs are
   "morally the same," yet one costs ~3–4× the other to formalize, and in each
   proof *the step the informal text spends the fewest words on is the most
   expensive one*. The document ends with a formalizability assessment
   justifying which proof to formalize — the assessment is the deliverable; the
   Lean is its receipt.
2. **[WeightedErdosSzekeres/](WeightedErdosSzekeres/)** — the rectangle-packing
   proof, formalized at human scale and structured for reading:
   - [Defs.lean](WeightedErdosSzekeres/Defs.lean) — `maxMonoSum`, Seidenberg's
     ending-at-`i` quantities, and their API. The order-carrying map is
     deliberately decoupled from the weight map, which (a) makes
     order-dualization free and (b) makes the main theorem strictly stronger
     than the problem it came from;
   - [Squares.lean](WeightedErdosSzekeres/Squares.lean) — "these are disjoint
     and contained in the rectangle": eight informal words, two real lemmas;
   - [Area.lean](WeightedErdosSzekeres/Area.lean) — the informal proof's
     single word "Hence," which in Lean is the entire 2-D measure argument;
   - [Main.lean](WeightedErdosSzekeres/Main.lean) — `erdos1026`, plus
     classical Erdős–Szekeres recovered as the unit-weight corollary of the
     same ℓ² theorem.
3. **[FAILURE_ATLAS.md](FAILURE_ATLAS.md)** — every place automation or the
   library fell short, with root causes: simp-normal-form mismatches,
   higher-order unification failures, missing lemmas (Mathlib has no
   Erdős–Szekeres tightness construction; its Erdős–Szekeres lives in
   `Archive/` with `private` scaffolding that cannot be reused). Hard subgoals
   are extracted to [Benchmarks/](Benchmarks/) as a standalone mini eval set
   for tactics and provers.

## The headline theorem

```lean
/-- Weighted Erdős–Szekeres, ℓ² form: for an injective order map `v` and
positive weights `w`, the best monotone subsequence weight satisfies
`∑ i, w i ^ 2 ≤ (maxMonoSum v w) ^ 2`. -/
theorem sum_sq_le_sq_maxMonoSum (v : Fin n → β) (w : Fin n → ℝ)
    (hv : Function.Injective v) (hw : ∀ i, 0 < w i) :
    ∑ i, w i ^ 2 ≤ maxMonoSum v w ^ 2
```

With `v = w = x` this is Erdős #1026 (`WeightedES.erdos1026`); with `w ≡ 1`
it is classical Erdős–Szekeres (`WeightedES.exists_monoSubseq_sq_card_ge`) —
one geometric argument, both theorems.

## Reproducing

```
lake exe cache get   # Mathlib binary cache
lake build           # zero sorries, zero warnings
```

Pinned: Lean `v4.29.0`, Mathlib `v4.29.0`. CI builds every push.

## Provenance

All informal sources are quoted and linked in
[sources/SOURCES.md](sources/SOURCES.md). Aristotle's machine proof is
referenced by pinned URL (its repository declares no license, so the file is
not vendored). This development is independent of it: same theorem, same
geometric idea, different codebase — that is what makes the line-count
comparison meaningful.
