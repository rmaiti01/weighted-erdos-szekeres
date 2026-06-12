# Source dossier — Erdős Problem #1026

All quotations below are verbatim from public sources, retrieved 2026-06-10.

## The problem

**Erdős [Er71, p.107]:** *"Let x₁,…,xₙ be a sequence of distinct real numbers. Determine max(Σ x_{i_r}), where the maximum is taken over all monotonic subsequences."*

- Problem page: https://www.erdosproblems.com/1026 (status: SOLVED (LEAN); "Formalised statement? No" as of 2026-06-10)
- Forum thread (primary source for both proofs below): https://www.erdosproblems.com/forum/thread/1026
- T. Tao, *The story of Erdős problem #1026* (Dec 8, 2025): https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/

**The finite core (Stijn Cambie, forum comment, 08:08 on 13 Sep 2025):**

> "the elegant question is the following. Let x₁, x₂, …, x_{k²} be k² distinct positive reals with sum 1. Then one can always find a monotonic subsequence with sum at least 1/k."

This is the statement everything here formalizes. It was posed as an open question in J. M. Steele's survey on Erdős–Szekeres (*Variations on the monotone subsequence theme of Erdős and Szekeres*, Discrete Probability and Algorithms, IMA Vol. 72, Springer, 1995, pp. 111–131; Zbl 0832.60012), first proved by Tidor–Wang–Yang (2016), and resolved publicly in December 2025 as described below. (Tao's post calls the Steele reference a "1980 article" in an edit, but the zbMATH record it links, 0832.60012, is the 1995 survey.)

## Timeline of the December 2025 resolution

1. **Dec 7, 2025** — Boris Alexeev, sweeping Erdős problems with the AI prover **Aristotle** (Harmonic), obtains an autonomous Lean proof via a rectangle-packing reformulation.
   File (3,658 lines, machine-generated): https://github.com/plby/lean-proofs/blob/9f90812fc849fa4b6eb6f6c93ed3aa74a0856321/src/v4.24.0/ErdosProblems/Erdos1026.lean
   (No license is declared on that repository, so the file is not vendored here; a local reference copy is kept untracked under `sources/`.)
2. **Dec 8, 2025, 00:23** — ~1 hour later, **Koishi Chan** posts a six-sentence elementary proof on the forum (quoted in full below).
3. **Dec 8, 2025** — llllvvuu explains Aristotle's argument informally (quoted in full below); Alexeev locates the prior human proof in Tidor–Wang–Yang.

## Proof A — Chan's blow-up argument (verbatim, KoishiChan, 00:23 on 08 Dec 2025)

> "Genuinely impressed!
> In retrospect, I think there is another solution that uses a "blowup" argument and Erdos-Szekeres. Set n = k². Take large N, and replace each xᵢ with ⌊N²xᵢ²⌋ pertubations of xᵢ, with no monotonic subsequence of size ⌈Nxᵢ⌉ + 1. As N → ∞, this new sequence's largest monotonic subsequence has size NS + O(1), where S is the largest sum of the monotonic subsequences of the original sequence. By Erdos-Szekeres, we have
> (NS + O(1))² ≥ Σᵢ₌₁ⁿ ⌊N²xᵢ²⌋.
> So taking N → ∞ we obtain
> S² ≥ Σᵢ₌₁ⁿ xᵢ².
> Now Cauchy-Schwarz gives S ≥ n^(−1/2) = k^(−1)."

Per Alexeev's follow-up comment, this argument appears in Section 3 of Tidor–Wang–Yang, *1-color-avoiding paths, special tournaments, and incidence geometry* (2016), https://arxiv.org/abs/1608.04153, there credited as implicit in A. Z. Wagner, *Large subgraphs in rainbow-triangle free colorings*.

## Proof B — Aristotle's rectangle-packing argument (verbatim, llllvvuu, 17:40 on 08 Dec 2025)

> "Aristotle's square-packing argument in a bit more detail:
> We follow the approach of Seidenberg (1959) in proving Erdős-Szekeres. Let Sᵢ be the maximal sum over all increasing subsequences ending in xᵢ, and Tᵢ be the maximal sum over all decreasing subsequences ending in xᵢ. Now consider the squares (Sᵢ − xᵢ, Tᵢ − xᵢ), (Sᵢ, Tᵢ). These are disjoint and contained in the rectangle (0, 0), (maxᵢ Sᵢ, maxᵢ Tᵢ). Hence, (maxᵢ Sᵢ)(maxᵢ Tᵢ) ≥ Σᵢ xᵢ² ≥ 1/k² as desired."

## The false strengthening (sidebar material)

**Vjeko Kovač (10:32 on 13 Sep 2025):** *"An even bolder conjecture would be that one can always find a monotonic subsequence of length k with sum at least 1/k."*

**Refuted by Cambie (13:16 on 13 Sep 2025):**

> "Let n = k², where k ≥ 3, and let the sequence be the normalised version of k·C(n,2), 1, 2, …, n−1 (i.e., all terms divided by (k+1)·C(n,2)). Now no subset has sum above 1/k if the first term is not there, but every monotonic subsequence containing the first element contains at most two elements (and thus not k)."

## Lean/Mathlib context

- Mathlib's Erdős–Szekeres lives in the **Archive**, not Mathlib proper:
  `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` (author: Bhavik Mehta), main statement:
  `theorem Theorems100.erdos_szekeres {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α) (hf : Injective f) : (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨ ∃ t : Finset α, s < #t ∧ StrictAntiOn f t`
- Mathlib has **no weighted Erdős–Szekeres** and **no tightness construction** (a sequence of r·s distinct values with no increasing subsequence longer than r nor decreasing longer than s).
- Mathlib *proper* contains only the **infinitary** Erdős–Szekeres
  (`exists_increasing_or_nonincreasing_subseq`, `Mathlib/Order/OrderIsoNat.lean`);
  the finite quantitative theorem is Archive-only, as above.

## Raw captures (untracked)

Full-text captures are kept as **untracked local working copies only** — none
of the three carries a license permitting redistribution, so none is vendored
in this repository (see `.gitignore`). What the repo distributes is this
dossier: short, attributed verbatim excerpts plus the links above.

- `forum_thread_raw.txt` — text dump of the forum thread (retrieved 2026-06-10)
- `tao_post_raw.txt` — text dump of Tao's blog post (retrieved 2026-06-10)
- `aristotle_erdos1026.lean` — local copy of Aristotle's proof (pinned URL above)
