# Audit work sample — diagnosing AI-generated formal mathematics

*One page on what this repository demonstrates as a deliverable, for teams that
train, evaluate, or ship automated provers. The repository itself is the
evidence; every claim below is checkable from a clean clone in ~10 minutes
([README](README.md#verify-in-10-minutes)).*

## The deliverable class

In December 2025, an AI prover resolved [Erdős problem #1026](https://www.erdosproblems.com/1026)
in **3,658 machine-generated Lean lines**. A human then proved it in six
short sentences on a forum. This repository is the third object in that triangle: the
same theorem at **485 readable lines**, produced *as an audit* — with the
referee report, the failure data, and the extracted benchmarks that the clean
final proof script normally swallows.

That audit layer — not the formalization — is the product:

| Artifact | File | What a lab gets from it |
|---|---|---|
| Gap-priced referee report of both informal proofs | [INFORMAL.md](INFORMAL.md) | 13 annotated gaps (G1–G7; B1–B5 with B2 split into B2a/B2b): every hidden assumption and unstated lemma, each priced in formalization cost. The punchline generalizes: *the step the informal text spends the fewest words on is the most expensive one.* |
| Formalizability assessment | [INFORMAL.md §4](INFORMAL.md#4-formalizability-assessment) | A cost model that predicted one proof at ~3–4× the other **before** writing Lean — the decision document a formalization effort needs on day zero. |
| Root-caused failure atlas | [FAILURE_ATLAS.md](FAILURE_ATLAS.md) | Each automation failure classified to an articulable cause: simp-normal-form mismatch, higher-order unification limit, missing library lemma. Failure *with a root cause* is training signal; failure without one is noise. |
| Extracted benchmarks | [Benchmarks/](Benchmarks/) | Hard subgoals as standalone eval targets with intentional `sorry`s — a mini eval set for tactics and provers, derived from real failures rather than synthesized. |
| Library-gap report | [INFORMAL.md §6](INFORMAL.md#6-library-gaps-surfaced-by-this-analysis) | 3 concrete Mathlib gaps surfaced, one PR-able independently (Erdős–Szekeres tightness). This is where autoformalization pipelines stall; knowing the gaps in advance is cheaper than hitting them. |
| Statement-faithfulness audit | [REVIEW_REPORT.md](REVIEW_REPORT.md) | Clause-by-clause check that the Lean statement says what the conjecture says — the one property no machine can certify. Includes axiom audits (`propext, Classical.choice, Quot.sound` only) and a satisfiability witness against vacuous truth. |
| Hostile-referee review | [REVIEW_REPORT.md](REVIEW_REPORT.md) | The pre-publication pass caught **4 cold-build errors that in-editor sessions had masked** — the same class of error that inflates AI-proof acceptance rates when review is editor-only. |

## Why this matters if you build or evaluate provers

1. **Eval data with provenance.** The benchmarks are subgoals a current prover
   ecosystem actually failed on, each with its root cause documented — not
   problems invented to be hard.
2. **A failure taxonomy you can act on.** "The tactic failed" is not data.
   "The tactic failed because no `@[simp]` lemma rewrites `StrictMonoOn f ∅`,
   and here is the missing lemma" is a Mathlib PR, a training example, and an
   eval item at once.
3. **The 7.5× compression is an argument about readability, not golf.**
   485 lines vs 3,658 on the same geometric idea quantifies what
   human-structured formalization buys: auditability. The line-count
   comparison is meaningful because the developments are independent
   (different codebase, same theorem — see [Provenance](README.md#provenance)).
4. **Statement faithfulness is the bottleneck nobody automates.** A prover
   that proves the wrong rendering of a conjecture proves nothing. The
   clause-by-clause audit here is the template for that check at scale.

## What an engagement looks like

The same audit, applied to your artifacts: an AI-generated proof corpus, a
benchmark under construction, or a formalization effort choosing what to
formalize next.

- **Proof audit** — faithfulness check, axiom audit, vacuity check, readable
  re-derivation where compression is informative. Fixed price per proof.
- **Failure atlas** — root-caused classification of your prover's failures on
  a problem set, with extracted benchmark files and the Mathlib gaps that
  explain the systematic misses.
- **Referee report** — gap-priced reading of informal mathematics *before*
  you spend formalization or training budget on it.

— Rajarshi Maiti · MSc Mathematics (number theory), University of Bonn /
Hausdorff Center · Mathlib community member · [rmaiti01.github.io](https://rmaiti01.github.io) ·
rmaiti7@gmail.com · [linkedin.com/in/1729](https://www.linkedin.com/in/1729)
