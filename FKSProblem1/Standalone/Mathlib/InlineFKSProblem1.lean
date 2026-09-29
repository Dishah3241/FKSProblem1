/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# FKS Problem 1: graphs of maximum degree d embed on a sphere in R^d

Problem 1 of N. Frankl, A. Kupavskii and K. J. Swanepoel, *Embedding graphs in Euclidean space*,
J. Combin. Theory Ser. A 171 (2020), 105146, asks:

    Is it true that for d > 3 any graph with maximum degree d, except K_{d+1}, has spherical
    dimension at most d?

## Main declarations

* `HasSphericalDimAtMost`: `G` has spherical dimension at most `d`: an injective placement of
  the vertices in `EuclideanSpace ℝ (Fin d)`, every vertex of norm `1 / √2`, every edge joining
  two points at distance exactly `1`; non-edges are unconstrained.
* `HasCompleteComponent`: some connected component of `G` is isomorphic to `K_{d+1}`; its
  negation is the componentwise reading of the exception "except `K_{d+1}`".
* `Problem1At`: the question at one fixed `d`.
* `Problem1`: the question, for every `d > 3`.
* `Problem1At4`: the `d = 4` instance, the smallest undecided instance.
* `Problem1BoundedAt`: the question at one fixed `d`, restricted to graphs on at most
  `2 * d` vertices.
* `Problem1Bounded`: the at-most-`2 * d`-vertices restriction for every `d > 3`: the first
  target, and the proved claim.

Two readings the source leaves open are settled where they occur, each with its reason:
"maximum degree `d`" is read as the upper bound `G.maxDegree ≤ d`, as the paper's own arguments
use it, and "except `K_{d+1}`" is read componentwise, as "no connected component isomorphic to
`K_{d+1}`" (`¬ HasCompleteComponent d G`), since the literal exception is refuted by
`K_{d+1} ⊔ K₁` and the paper restates its own `d = 3` exception componentwise (`main.tex` l. 431).

The Mathlib-only statement source. `Challenge.lean` is **generated** from this file: everything
above the closing proof-link note, concatenated with `scripts/palomar-challenge-footer.txt`.
Regenerate with `scripts/check-palomar-challenge.sh --update`, and CI fails when the two diverge.
Drift is therefore impossible by construction rather than by discipline.

Consequences to respect:

* this file imports **only Mathlib**, because `Challenge.lean` inherits its imports and Palomar
  requires that isolation;
* it declares propositions and contains no proofs —
  `InlineFKSProblem1Proof` proves them;
* a mathematician must be able to read it alone, so the relevant predicates are declared here,
  with the same bodies as their siblings in `StatementA`, rather than imported from elsewhere;
* every closed proposition carries a `.witness`, every non-dependent hypothesis of one carries
  a `.drop<Tag>`, and every definition a `.separating`, checked by `lake exe fidelity`.
-/

@[expose] public section

namespace FKSProblem1.Standalone.Mathlib.InlineFKSProblem1

/-- `HasSphericalDimAtMost d G`: the graph `G` on `Fin n` has spherical dimension at most `d`,
i.e. its vertices admit an injective placement `f : Fin n → EuclideanSpace ℝ (Fin d)` with every
vertex on the sphere of radius `1 / √2` centred at the origin (`‖f v‖ = 1 / √2` for every `v`)
and every edge joining two points at distance exactly `1` (`dist (f u) (f v) = 1` whenever
`G.Adj u v`). Injectivity is part of the reading: distinct vertices get distinct points.
Non-adjacent pairs are unconstrained and may also lie at distance `1`; this is the
Erdős–Harary–Tutte reading of a unit-distance representation, which the paper adopts (its
Definition 2 notes the edge set need not contain all unit-distance pairs).

Degenerate cases: the empty graph (`n = 0`) qualifies through the empty placement for every `d`,
including `d = 0`; a single vertex needs `d ≥ 1`, since `0` is the only point of `ℝ⁰` and its norm
is not `1 / √2`; isolated vertices are carried by injectivity alone. -/
def HasSphericalDimAtMost (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective f ∧
    (∀ v : Fin n, ‖f v‖ = 1 / √2) ∧ ∀ u v : Fin n, G.Adj u v → dist (f u) (f v) = 1

/-- Separating example for `HasSphericalDimAtMost`, one conjunct against each of its two nearest
wrong readings.

Without the sphere: the complete graph `K₂` has an injective placement in `ℝ¹` with its edge at
distance exactly `1` (two points of a line one unit apart), yet it has no placement satisfying
`HasSphericalDimAtMost 1`: two points of norm `1 / √2` on a line sit at distance `0` or `√2`,
never `1`. The sphere hypothesis is not decoration; on it, distance `1` is orthogonality.

Without injectivity: the edgeless graph on three vertices has a placement on the radius-`1 / √2`
sphere of `ℝ¹` once placements may collide (send every vertex to the same point), but no injective
one: that sphere is the two-point set `±(1 / √2)`. Injectivity is the clause that carries vertices
whose adjacency constrains nothing, and the edgeless graph is its honest instrument: on the
two-point sphere of `ℝ¹` no graph with an edge can serve, since no pair of its points is at
distance `1`. -/
def HasSphericalDimAtMost.separating : Prop :=
  (∃ f : Fin 2 → EuclideanSpace ℝ (Fin 1), Function.Injective f ∧ dist (f 0) (f 1) = 1) ∧
    ¬ HasSphericalDimAtMost 1 (SimpleGraph.completeGraph (Fin 2)) ∧
  (∃ f : Fin 3 → EuclideanSpace ℝ (Fin 1), ∀ v : Fin 3, ‖f v‖ = 1 / √2) ∧
    ¬ HasSphericalDimAtMost 1 (⊥ : SimpleGraph (Fin 3))

/-- `HasCompleteComponent d G`: some connected component of `G` is isomorphic to the complete
graph `K_{d+1}`. Explicitly, some vertex `v` has exactly `d + 1` reachable vertices — its
connected component, bijective with `Fin (d + 1)` — any two distinct ones being adjacent.

This is the corrected reading of the exception "except `K_{d+1}`" of FKS Problem 1. Read
literally, as excepting only the graph that *is* `K_{d+1}`, the question becomes false: the graph
`K_{d+1} ⊔ K₁` has maximum degree `d`, is not `K_{d+1}`, and has spherical dimension `d + 1`,
since its `K_{d+1}` component forces `d + 1` pairwise orthogonal vectors of norm `1 / √2`, and
`d + 1` nonzero pairwise orthogonal vectors in `ℝᵈ` are linearly independent. The paper's own
`d = 3` theorem says "contains `K_{3,3}`" (`main.tex` l. 72), and the paper restates it just
before Problem 1 as "has `K_{3,3}` as a component" (l. 431), the form its proof uses (l. 218);
under the degree bound the two agree, since a `K_{3,3}` subgraph saturates its vertices.
Under the standing hypothesis `G.maxDegree ≤ d` the component reading is
equivalent to forbidding `K_{d+1}` as a subgraph and as a clique: a `K_{d+1}` clique already
exhausts the `d` neighbours of each of its vertices, so no edge leaves it. -/
def HasCompleteComponent (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ v : Fin n, Nonempty ({w : Fin n // G.Reachable v w} ≃ Fin (d + 1)) ∧
    ∀ a b : Fin n, G.Reachable v a → G.Reachable v b → a ≠ b → G.Adj a b

/-- Separating example for `HasCompleteComponent` against the literal reading of the exception,
"the graph itself is not `K_{d+1}`". For every `d ≥ 1`, the graph on `Fin (d + 2)` whose distinct
vertices `a`, `b` are adjacent exactly when `a.val ≠ d + 1` and `b.val ≠ d + 1` is `K_{d+1} ⊔ K₁`:
it *has* a complete component on `d + 1` vertices, so the corrected exception excludes it, while
the literal exception does not, since a graph on `d + 2` vertices is not `K_{d+1}`. One object on
which the two readings of the exception differ. -/
def HasCompleteComponent.separating : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ G : SimpleGraph (Fin (d + 2)),
    (∀ a b : Fin (d + 2), G.Adj a b ↔ (a.val ≠ d + 1 ∧ b.val ≠ d + 1 ∧ a ≠ b)) ∧
      HasCompleteComponent d G ∧
      ¬ (d + 2 = d + 1 ∧ ∀ a b : Fin (d + 2), a ≠ b → G.Adj a b)

open Classical in
/-- FKS Problem 1 at a fixed dimension `d`: every graph of maximum degree at most `d` with no
connected component isomorphic to `K_{d+1}` has spherical dimension at most `d`.

Quantifier order: `d` is fixed; `n` and `G` are universally quantified; the degree bound
`G.maxDegree ≤ d` and the component exception `¬ HasCompleteComponent d G` are hypotheses; the
placement is existential, inside `HasSphericalDimAtMost`.

"Maximum degree `d`" is settled as the bound `G.maxDegree ≤ d`. The paper's own use decides it:
before applying its bounded-degree statements it disposes of smaller degree by those same
statements ("we may also assume that `Δ ≥ d`, otherwise Proposition 4 gives that `H` is
embeddable in `Sph^{d-1}`"), reading the proposition proved for maximum degree `d - 1` on graphs
of degree at most `d - 1`; and given that proposition the two readings of the problem have the
same truth value, since graphs of degree at most `d - 1` already have spherical dimension at most
`d`.

Degenerate cases sit inside the quantifiers. The empty graph qualifies vacuously and is placed by
the empty map in every `d`. At `d = 0` the exception `¬ HasCompleteComponent 0 G` rules out every
one-vertex component, hence every nonempty graph of maximum degree `0`, so the instance at
`d = 0` is true. The instances at `d = 1`, `2`, `3` are false: three isolated vertices at `d = 1`
(no `K₂` component, and the sphere `±(1 / √2)` of `ℝ¹` carries only two points); the five-cycle
at `d = 2` (consecutive adjacencies would force all five placed vectors parallel, against
injectivity); and the cube at `d = 3`, which the paper records as not embeddable on `S²` although
it is bipartite and so has no `K₄` component. The question is posed for `d > 3` and is open
there. -/
def Problem1At (d : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.maxDegree ≤ d → ¬ HasCompleteComponent d G →
    HasSphericalDimAtMost d G

open Classical in
/-- Separating example for `Problem1At`, showing that the corrected exception is what carries the
question and is not decoration. For every `d ≥ 1` there is a graph — `K_{d+1} ⊔ K₁` on `d + 2`
vertices — at which the question's other hypothesis holds (`G.maxDegree ≤ d`), whose literal
exception holds (it is not `K_{d+1}`: it has `d + 2` vertices), and whose conclusion fails (its
`K_{d+1}` component has no spherical placement in `ℝᵈ`). The corrected exception
`¬ HasCompleteComponent d G` is exactly the hypothesis that excludes this graph, which is what
distinguishes `Problem1At` from the question the literal reading would state. -/
def Problem1At.separating : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ (n : ℕ) (G : SimpleGraph (Fin n)), n = d + 2 ∧
    G.maxDegree ≤ d ∧ HasCompleteComponent d G ∧ ¬ HasSphericalDimAtMost d G ∧
    ¬ (n = d + 1 ∧ ∀ a b : Fin n, a ≠ b → G.Adj a b)

/-- Open problem. FKS Problem 1, as a proposition: for every `d > 3`, every graph of maximum
degree at most `d` with no connected component isomorphic to `K_{d+1}` has spherical dimension at
most `d`. Stated here, not settled: work on this question can end in a proof or in a disproof, at
one fixed `d ≥ 4` or for all `d > 3` at once. -/
def Problem1 : Prop := ∀ (d : ℕ) (_hd3 : 3 < d), Problem1At d

open Classical in
/-- Satisfiability witness for `Problem1`: its hypotheses are jointly satisfiable together with
its conclusion, so the question is not vacuous. Take `d = 4` and the five-cycle on `Fin 5`:
`3 < 4`, `0 < 5`, the cycle has maximum degree `2 ≤ 4`, no component on five pairwise adjacent
vertices (its degrees are `2`, not `4`), and five distinct points of norm `1 / √2` exist on a
circle in a two-dimensional coordinate subspace of `ℝ⁴`. -/
def Problem1.witness : Prop :=
  Problem1 → ∃ (d : ℕ) (n : ℕ) (G : SimpleGraph (Fin n)), 3 < d ∧ 0 < n ∧
    G.maxDegree ≤ d ∧ ¬ HasCompleteComponent d G ∧ HasSphericalDimAtMost d G

/-- Drop companion for the hypothesis `_hd3 : 3 < d` of `Problem1`: the question without the lower
bound on `d` is false. At `d = 1` the edgeless graph on three vertices has maximum degree `0 ≤ 1`,
no component isomorphic to `K₂` (its components are singletons), and no injective placement on the
two-point sphere of `ℝ¹`. -/
def Problem1.dropHd3 : Prop := ¬ ∀ (d : ℕ), Problem1At d

/-- Open problem. The instance of FKS Problem 1 at `d = 4`: every graph of maximum degree at most
`4` with no connected component isomorphic to `K₅` has spherical dimension at most `4`. This is
the smallest undecided instance: the instances at `d = 1`, `2`, `3` are false (three isolated
vertices, the five-cycle, the cube), and the source settles no case of the spherical question at
`d ≥ 4`. -/
def Problem1At4 : Prop := Problem1At 4

open Classical in
/-- Satisfiability witness for `Problem1At4`: its hypotheses are jointly satisfiable together with
its conclusion, so the `d = 4` question is not vacuous. Take the five-cycle on `Fin 5`: `0 < 5`,
maximum degree `2 ≤ 4`, no `K₅` component, and a spherical placement in `ℝ⁴` as five distinct
points of norm `1 / √2` on a circle. -/
def Problem1At4.witness : Prop :=
  Problem1At4 → ∃ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n ∧
    G.maxDegree ≤ 4 ∧ ¬ HasCompleteComponent 4 G ∧ HasSphericalDimAtMost 4 G

open Classical in
/-- FKS Problem 1 restricted to graphs on at most `2 * d` vertices, at a fixed dimension `d`:
every such graph of maximum degree at most `d` with no connected component isomorphic to
`K_{d+1}` has spherical dimension at most `d`. Quantifier order as in `Problem1At`, with the
vertex bound `n ≤ 2 * d` as an additional first hypothesis; the placement remains existential.

The bound `2 * d` is the restriction the first target asks for, and it is loose enough to keep the
known obstructions in play: `K_{d+1} ⊔ K₁` has `d + 2 ≤ 2 * d` vertices exactly when `d ≥ 2`, and
`K_{3,3}` has `6 ≤ 2 * 3` vertices. -/
def Problem1BoundedAt (d : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 2 * d → G.maxDegree ≤ d →
    ¬ HasCompleteComponent d G → HasSphericalDimAtMost d G

open Classical in
/-- Separating example for `Problem1BoundedAt`, the bounded counterpart of the separating example
for `Problem1At`: for every `d ≥ 2` (so that `d + 2 ≤ 2 * d`) the graph `K_{d+1} ⊔ K₁` on
`d + 2` vertices satisfies the vertex bound and the degree bound, is not `K_{d+1}`, has a complete
component on `d + 1` vertices, and has no spherical placement in `ℝᵈ`. The corrected exception is
what excludes it from the bounded question as well. -/
def Problem1BoundedAt.separating : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ (n : ℕ) (G : SimpleGraph (Fin n)), n = d + 2 ∧ n ≤ 2 * d ∧
    G.maxDegree ≤ d ∧ HasCompleteComponent d G ∧ ¬ HasSphericalDimAtMost d G ∧
    ¬ (n = d + 1 ∧ ∀ a b : Fin n, a ≠ b → G.Adj a b)

/-- The restriction of FKS Problem 1 to graphs on at most `2 * d` vertices, for every `d > 3`:
the first target. At `d = 3` the restricted instance is already false — `K_{3,3}` on exactly
`2 * 3` vertices has maximum degree `3`, no `K₄` component (it is bipartite), and no spherical
placement in `ℝ³`, since each of its two parts spans a subspace of dimension at least two, the two
spans are orthogonal, and `2 + 2 > 3`. -/
def Problem1Bounded : Prop := ∀ (d : ℕ) (_hd3 : 3 < d), Problem1BoundedAt d

open Classical in
/-- Satisfiability witness for `Problem1Bounded`: its hypotheses are jointly satisfiable together
with its conclusion, so the restricted question is not vacuous. Take `d = 4` and the five-cycle on
`Fin 5`: `3 < 4`, `0 < 5`, `5 ≤ 2 * 4`, maximum degree `2 ≤ 4`, no `K₅` component, and a spherical
placement in `ℝ⁴` as five distinct points of norm `1 / √2` on a circle. -/
def Problem1Bounded.witness : Prop :=
  Problem1Bounded → ∃ (d : ℕ) (n : ℕ) (G : SimpleGraph (Fin n)), 3 < d ∧ 0 < n ∧ n ≤ 2 * d ∧
    G.maxDegree ≤ d ∧ ¬ HasCompleteComponent d G ∧ HasSphericalDimAtMost d G

/-- Drop companion for the hypothesis `_hd3 : 3 < d` of `Problem1Bounded`: the restricted question
without the lower bound on `d` is false. At `d = 3`, `K_{3,3}` on six vertices satisfies
`6 ≤ 2 * 3` and `G.maxDegree ≤ 3`, has no `K₄` component, and has no spherical placement in
`ℝ³`. -/
def Problem1Bounded.dropHd3 : Prop := ¬ ∀ (d : ℕ), Problem1BoundedAt d

end FKSProblem1.Standalone.Mathlib.InlineFKSProblem1

/-!
## Formal proof

Proved in `InlineFKSProblem1Proof`. `Problem1Bounded` is the proved first target; the
`separating`, `witness` and `dropHd3` lines link the fidelity companions of the claims that carry
them.

* `Problem1` → open: FKS 2020 Problem 1
* `Problem1At4` → open: FKS 2020 Problem 1
* `Problem1Bounded` → `Problem1Bounded.proof`
* `separating` → `separating.proof`
* `witness` → `witness.proof`
* `dropHd3` → `dropHd3.proof`
-/
