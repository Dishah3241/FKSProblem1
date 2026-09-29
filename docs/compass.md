# Compass list

These are the declarations whose meaning decides whether the frozen statement says what FKS Problem 1 asks: for
`d > 3`, does every graph of maximum degree `d`, except `K_{d+1}`, have spherical dimension at most `d`? (Frankl,
Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, JCTA 171 (2020) 105146, §5, Problem 1,
`main.tex` l. 433.) The exception is read componentwise (finding A40), as explained in row 2.

This list is the owner's whole review surface, and **its sign-off is the statement freeze** (ROADMAP P10, phase 1).
Everything else, including every later proof and the GraphDimension library, is checked by the kernel and the gates.

**The frozen text** is statement A: `FKSProblem1/Standalone/Mathlib/StatementA.lean`, namespace
`FKSProblem1.StatementA`, at FKSProblem1 `6aaca0c`.

**Owner sign-off: confirmed on 2026-09-28 for rows 1–15.** (2026-09-29: row 2's source citation made precise after the release review; the row's meaning is unchanged.) In the open-question manager's session, the owner answered "Freeze" to the request to sign this list, as committed at `d84e9ec`. The sign-off freezes the statement: statement A at `6aaca0c`, blob `6310931b942b7a7e9fa28e68a9fe469dd869c1ca`. Any change to a row cancels it.

## How the statement was made

- **The owner's choices, 2026-09-28:** freeze the whole question as a `Prop`, so the work can end in a proof or a
  disproof; take as the first target the question restricted to graphs on at most `2d` vertices, for every `d ≥ 4`.
- **Authored, not inherited.** No `formal-conjectures` statement exists. Stage 1 wrote it twice, blind:
  statement A by pi, run `20260928-160844-5facc645`; statement B by codex (gpt-6-astra), run
  `20260928-160845-a4c81237`. The two authors made the same reading decisions independently.
- **Equivalence, proved in Lean with no `sorry`** (codex gpt-6-astra, run `20260928-191529-00988344`,
  `FKSProblem1/Stage1/Equivalence.lean`, `daa0eb0`): `Problem1At d ↔ QuestionAt d` for every `d`; `Problem1 ↔
  Question`; `Problem1At4 ↔ QuestionFour`; `Problem1BoundedAt d ↔ QuestionAtMostTwoMulAt d`; `Problem1Bounded ↔
  FirstTarget`. The encodings differ (maximum degree against neighbour-set cardinalities; a reachability class against
  a component isomorphic to `K_{d+1}`; `‖f v‖` against `dist (f v) 0`; `n ≤ 2d` against `Fin (2d + 1)`), and the
  proofs bridge each.
- **A defect caught before this list (finding A56).** The design run found that statement A's two separating
  companions (rows 10 and 11) asserted a counterexample to the target: their bodies said *no* complete component
  where their docstrings, correctly, describe a graph that *has* one. Fixed in `6aaca0c`. The rows below are read
  from the bodies, not the docstrings.

## The rows

| # | Declaration | Must mean | Check |
|---|---|---|---|
| 1 | `HasSphericalDimAtMost d G` | there is an **injective** map from the vertices of `G : SimpleGraph (Fin n)` into `ℝᵈ` with every vertex at norm exactly `1/√2` and every **edge** at distance exactly 1 | Non-edges are unconstrained (Erdős–Harary–Tutte, as in P9). On this sphere, distance 1 is orthogonality. FKS's `Sph^{d-1}` has radius `1/√2` (l. 57). |
| 2 | `HasCompleteComponent d G` | some connected component of `G` is `K_{d+1}`: a vertex whose reachability class has exactly `d + 1` vertices, any two distinct ones adjacent | The **corrected** exception (A40). Read literally, "except `K_{d+1}`" is false: `K_{d+1} ⊔ K₁` has maximum degree `d`, is not `K_{d+1}`, and needs `d + 1` dimensions. FKS's `d = 3` theorem says "contains `K_{3,3}`" (l. 72); the paper restates it before Problem 1 as "has `K_{3,3}` as a component" (l. 431), and under the degree bound the two agree. |
| 3 | `Problem1At d` | for every `n` and every `G` on `Fin n` with `G.maxDegree ≤ d` and no `K_{d+1}` component, `HasSphericalDimAtMost d G` | "Maximum degree `d`" is read as **at most** `d`. FKS's Proposition (l. 77) already gives maximum degree `d − 1`, so the two readings have the same truth value. |
| 4 | `Problem1` | `Problem1At d` for every `d > 3` | **The frozen open question.** It is not claimed proved. |
| 5 | `Problem1At4` | `Problem1At 4` | Open; the smallest undecided instance. Not a target of phase 1. |
| 6 | `Problem1BoundedAt d` | `Problem1At d` restricted to graphs on `n ≤ 2d` vertices | `n = 0` through `2d` inclusive. |
| 7 | `Problem1Bounded` | `Problem1BoundedAt d` for every `d > 3` | **The first target, phase 1.** The planned proof: pad to `2d` vertices; a perfect matching in the complement gives the cross-polytope placement; otherwise Tutte's theorem leaves only `K_{d+1}` (excluded) and `K_{d,d}` (two orthogonal circles). |
| 8 | `HasSphericalDimAtMost.separating` | (a) `K₂` has an injective placement in `ℝ¹` with its edge at distance 1, yet no spherical one; (b) three points of `ℝ¹` can all have norm `1/√2`, yet the edgeless graph on three vertices has no injective spherical placement in `ℝ¹` | (a) separates row 1 from the reading without the sphere; (b) from the reading without injectivity. |
| 9 | `HasCompleteComponent.separating` | for every `d ≥ 1`, `K_{d+1} ⊔ K₁` on `Fin (d + 2)` **has** a complete component, although it is not itself `K_{d+1}` | Separates row 2 from the literal exception. |
| 10 | `Problem1At.separating` | for every `d ≥ 1`, some graph on `d + 2` vertices has maximum degree `≤ d`, **has** a complete component, has **no** spherical placement in `ℝᵈ`, and is not `K_{d+1}` | Shows the component exception is what keeps row 3 from being false. Fixed by A56. |
| 11 | `Problem1BoundedAt.separating` | the same for every `d ≥ 2`, with `d + 2 ≤ 2d` | The bounded counterpart of row 10. Fixed by A56. |
| 12 | `Problem1.witness`, `Problem1At4.witness`, `Problem1Bounded.witness` | each: if the claim holds, then some nonempty graph meets all its hypotheses and has a spherical placement (the five-cycle at `d = 4`) | Guards against vacuous hypotheses. |
| 13 | `Problem1.dropHd3`, `Problem1Bounded.dropHd3` | without `3 < d` each claim is false | Counterexamples: three isolated vertices at `d = 1`; `K_{3,3}` at `d = 3` (six vertices, `≤ 2·3`). |
| 14 | Mathlib `G.maxDegree` (under `open Classical`) | the largest vertex degree of the finite graph `G`, `0` for the empty graph | The equivalence proves it agrees with B's bound on every neighbour set's cardinality. |
| 15 | Mathlib `dist` and `‖·‖` on `EuclideanSpace ℝ (Fin d)` | the Euclidean (L²) distance and norm | `EuclideanSpace` is `PiLp 2`; plain `Fin d → ℝ` would carry the sup metric. |

## Not part of the freeze

- **Which declaration Palomar sees.** At phase 1's release, `Challenge.lean` states `Problem1Bounded`.
- **The companions' proofs** (rows 8–13). Their statements are frozen above; their proofs are a leaf before the gates.
- **The open-claim marks** on rows 4 and 5 ("Open problem" in the docstring, an `open:` line in the proof block) are
  metadata under the template's convention. The manager tells the owner when they land.
