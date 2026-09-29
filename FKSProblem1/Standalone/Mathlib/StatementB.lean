/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

/-!
# FKS Problem 1: the spherical dimension question

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, JCTA 171 (2020),
105146, arXiv:1802.03092, Definitions 1--2, Proposition 2 and Section 5, Problem 1.

All graphs are finite and simple. Every vertex count and every graph is universally quantified;
only the placement is existentially quantified, after the graph and its hypotheses are fixed.
The ambient space is Euclidean `ℝᵈ`, with its L² metric, and the sphere has radius `1 / √2`
and centre zero. Edges have length one; non-edges may also have length one.

"Maximum degree d" can mean equality or an upper bound. We use the upper bound, as the
paper itself does when applying Proposition 2 in the Ramsey proof (Section 4). Proposition 2
already settles degree at most `d - 1`, so for `d > 3` this asks the same remaining question
as the exact-degree reading. There is no regularity or connectedness hypothesis.

"Except K_{d+1}" could literally exclude only a graph isomorphic to that complete graph.
That reading admits `K_{d+1} ⊔ K₁`, which still cannot lie on this sphere in `ℝᵈ`.
We freeze the corrected reading: no connected component is isomorphic to `K_{d+1}`.
This follows the component wording immediately before Problem 1. It is a reading decision,
not a verbatim transcription of the exception.

The empty graph (`n = 0`) is included and has the empty placement. Isolated vertices are
allowed and must receive distinct points on the same sphere. At `d = 4`, the question covers
all finite graphs of degree at most four with no `K₅` component, and asks for a placement
in `ℝ⁴`. The first target restricts this to at most eight vertices at `d = 4`, and at most
`2 * d` vertices for every `d > 3`.

In the bounded questions, `n : Fin (2 * d + 1)` universally ranges over precisely the natural
vertex counts `0, …, 2 * d`; the vertex type is `Fin n.val`. The bound is part of the index
type, not a removable hypothesis: claiming that its removal has a counterexample would
assert a negative answer to the unrestricted open question.

The two fixed-d questions are predicates in a natural dimension parameter. The whole question,
the four-dimensional instance, and the first target are closed propositions. The fidelity
companions below are propositions too; none is supplied with a proof in this statement source.
-/

@[expose] public section

namespace FKSProblem1.StatementB

/-- An injective spherical unit-distance representation in `ℝᵈ`, with non-edges unconstrained. -/
def SphericalRepresentation (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → EuclideanSpace ℝ (Fin d),
    Function.Injective f ∧
    (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
    ∀ v w, G.Adj v w → dist (f v) (f w) = 1

/-- `K₃` fits in `ℝ²` but not on the prescribed circle. The star `K₁,₃` has a noninjective
placement on that circle but no injective one: its three leaves would occupy only two points
orthogonal to the centre vertex. Finally, two nonadjacent vertices may be at distance one. -/
def SphericalRepresentation.separating : Prop :=
  ((∃ f : Fin 3 → EuclideanSpace ℝ (Fin 2),
      Function.Injective f ∧
      ∀ v w, (SimpleGraph.completeGraph (Fin 3)).Adj v w → dist (f v) (f w) = 1) ∧
    ¬ SphericalRepresentation 2 (SimpleGraph.completeGraph (Fin 3))) ∧
  (let G := SimpleGraph.fromRel (fun v w : Fin 4 => v = 0 ∨ w = 0)
   (∃ f : Fin 4 → EuclideanSpace ℝ (Fin 2),
      (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
      ∀ v w, G.Adj v w → dist (f v) (f w) = 1) ∧
    ¬ SphericalRepresentation 2 G) ∧
  (∃ f : Fin 2 → EuclideanSpace ℝ (Fin 2),
    Function.Injective f ∧
    (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧ dist (f 0) (f 1) = 1) ∧
  SphericalRepresentation 2 (⊥ : SimpleGraph (Fin 2))

/-- Open problem: the corrected FKS question in one fixed dimension `d`, intended for `d > 3`.
The component exception excludes complete components, including those accompanied by isolates. -/
def QuestionAt (d : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
  ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
    ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
    ∃ f : Fin n → EuclideanSpace ℝ (Fin d),
      Function.Injective f ∧
      (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
      ∀ v w, G.Adj v w → dist (f v) (f w) = 1

/-- Open problem: the corrected FKS question for every natural dimension
strictly greater than three. -/
def Question : Prop :=
  ∀ d : ℕ,
  ∀ (_hdim : 3 < d),
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
  ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
    ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
    ∃ f : Fin n → EuclideanSpace ℝ (Fin d),
      Function.Injective f ∧
      (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
      ∀ v w, G.Adj v w → dist (f v) (f w) = 1

/-- Open problem: every finite graph of degree at most four without a `K₅` component has an
injective unit-distance placement on the radius-`1 / √2` sphere in `ℝ⁴`. -/
def QuestionFour : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ 4),
  ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
    ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (4 + 1)))),
    ∃ f : Fin n → EuclideanSpace ℝ (Fin 4),
      Function.Injective f ∧
      (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
      ∀ v w, G.Adj v w → dist (f v) (f w) = 1

/-- Open problem: the corrected question in fixed dimension `d`, restricted to at most `2 * d`
vertices. The index `n` includes zero and the endpoint `2 * d`. -/
def QuestionAtMostTwoMulAt (d : ℕ) : Prop :=
  ∀ (n : Fin (2 * d + 1)) (G : SimpleGraph (Fin n.val)),
  ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
  ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
    ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
    ∃ f : Fin n.val → EuclideanSpace ℝ (Fin d),
      Function.Injective f ∧
      (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
      ∀ v w, G.Adj v w → dist (f v) (f w) = 1

/-- The first target: for every `d > 3` and every graph on at most `2 * d` vertices, the
corrected FKS question holds. -/
def FirstTarget : Prop :=
  ∀ d : ℕ,
  ∀ (_hdim : 3 < d),
  ∀ (n : Fin (2 * d + 1)) (G : SimpleGraph (Fin n.val)),
  ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
  ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
    ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
    ∃ f : Fin n.val → EuclideanSpace ℝ (Fin d),
      Function.Injective f ∧
      (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
      ∀ v w, G.Adj v w → dist (f v) (f w) = 1

/-- `K_d` satisfies the hypotheses for every `d > 3` and has a placement by scaled basis
vectors. The last conjunct records the specialization of the fixed-d question to this graph. -/
def QuestionAt.witness : Prop :=
  ∀ d : ℕ, 3 < d →
    let G := SimpleGraph.completeGraph (Fin d)
    (∀ v, (G.neighborSet v).ncard ≤ d) ∧
    (∀ C : G.ConnectedComponent,
      ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))) ∧
    SphericalRepresentation d G ∧ (QuestionAt d → SphericalRepresentation d G)

/-- For each `d > 3`, this is `K_{d+1} ⊔ K₁`, on `Fin (d + 2)`: it satisfies the degree
bound and the literal exception, but has a forbidden component and no spherical placement.
The final implication is the corrected question specialized to this very graph; its component
premise fails. Thus this separator does not assert an answer to the corrected open question. -/
def QuestionAt.separating : Prop :=
  ∀ d : ℕ, 3 < d →
    let G := SimpleGraph.fromRel (fun v w : Fin (d + 2) => v.val < d + 1 ∧ w.val < d + 1)
    (∀ v, (G.neighborSet v).ncard ≤ d) ∧
    ¬ Nonempty (G ≃g SimpleGraph.completeGraph (Fin (d + 1))) ∧
    (∃ C : G.ConnectedComponent,
      Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))) ∧
    ¬ SphericalRepresentation d G ∧
    (QuestionAt d →
      (∀ C : G.ConnectedComponent,
        ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))) →
      SphericalRepresentation d G)

/-- The complete-graph witnesses are admissible; the whole question specializes to `d = 4`. -/
def Question.witness : Prop :=
  QuestionAt.witness ∧ (Question → QuestionAt 4)

/-- The literal exception fails on the complete-component examples; the whole question uses
exactly the fixed-d questions for dimensions strictly greater than three. -/
def Question.separating : Prop :=
  QuestionAt.separating ∧ (Question ↔ ∀ d : ℕ, 3 < d → QuestionAt d)

/-- `K₄` is an admissible nonempty instance, placed at the four scaled coordinate vectors. -/
def QuestionFour.witness : Prop :=
  let G := SimpleGraph.completeGraph (Fin 4)
  (∀ v, (G.neighborSet v).ncard ≤ 4) ∧
  (∀ C : G.ConnectedComponent,
    ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin 5))) ∧
  SphericalRepresentation 4 G ∧ (QuestionFour → SphericalRepresentation 4 G)

/-- The four-dimensional specialization inherits the `K₅ ⊔ K₁` separator. -/
def QuestionFour.separating : Prop :=
  QuestionAt.separating ∧ (QuestionFour ↔ QuestionAt 4)

/-- `K_d` has `d ≤ 2 * d` vertices and satisfies the bounded question's hypotheses. -/
def QuestionAtMostTwoMulAt.witness : Prop :=
  QuestionAt.witness ∧
  ∀ d : ℕ, 3 < d → d ≤ 2 * d ∧
    (QuestionAtMostTwoMulAt d →
      SphericalRepresentation d (SimpleGraph.completeGraph (Fin d)))

/-- `K_{d+1} ⊔ K₁` also lies within the vertex budget when `d > 3`. The displayed equivalence
makes explicit that the bounded question is the restriction to natural counts `n ≤ 2 * d`. -/
def QuestionAtMostTwoMulAt.separating : Prop :=
  QuestionAt.separating ∧
  ∀ d : ℕ, 3 < d → d + 2 ≤ 2 * d ∧
    (QuestionAtMostTwoMulAt d ↔
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 2 * d →
        (∀ v, (G.neighborSet v).ncard ≤ d) →
        (∀ C : G.ConnectedComponent,
          ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))) →
        SphericalRepresentation d G)

/-- The same nondegenerate complete graphs witness the first target's hypotheses; its
four-dimensional instance includes `K₄`. -/
def FirstTarget.witness : Prop :=
  QuestionAtMostTwoMulAt.witness ∧
  (FirstTarget → SphericalRepresentation 4 (SimpleGraph.completeGraph (Fin 4)))

/-- The first target has the bounded separators and ranges over precisely the intended
dimensions. -/
def FirstTarget.separating : Prop :=
  QuestionAtMostTwoMulAt.separating ∧
  (FirstTarget ↔ ∀ d : ℕ, 3 < d → QuestionAtMostTwoMulAt d)

/-- Counterexample: `d = 3` and `K₃,₃` on six vertices. Each part needs a span of
dimension at least two, and the two spans are orthogonal. There is no `K₄` component. -/
def Question.dropHdim : Prop :=
  ¬ (∀ d : ℕ,
     ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
     ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
     ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
       ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
       ∃ f : Fin n → EuclideanSpace ℝ (Fin d),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-- Counterexample: `d = 4` and `K₆`. Its sole component is not `K₅`, but six
nonzero pairwise orthogonal vectors cannot fit in `ℝ⁴`. -/
def Question.dropHdegree : Prop :=
  ¬ (∀ d : ℕ,
     ∀ (_hdim : 3 < d),
     ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
     ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
       ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
       ∃ f : Fin n → EuclideanSpace ℝ (Fin d),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-- Counterexample: `d = 4` and `K₅`. Its degree is four, but five nonzero
pairwise orthogonal vectors cannot fit in `ℝ⁴`. -/
def Question.dropHcomponent : Prop :=
  ¬ (∀ d : ℕ,
     ∀ (_hdim : 3 < d),
     ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
     ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
       ∃ f : Fin n → EuclideanSpace ℝ (Fin d),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-- Counterexample: `K₆`. Its sole component is not `K₅`, but six
nonzero pairwise orthogonal vectors cannot fit in `ℝ⁴`. -/
def QuestionFour.dropHdegree : Prop :=
  ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
     ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
       ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (4 + 1)))),
       ∃ f : Fin n → EuclideanSpace ℝ (Fin 4),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-- Counterexample: `K₅`. Its degree is four, but five nonzero
pairwise orthogonal vectors cannot fit in `ℝ⁴`. -/
def QuestionFour.dropHcomponent : Prop :=
  ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
     ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ 4),
       ∃ f : Fin n → EuclideanSpace ℝ (Fin 4),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-- Counterexample: `d = 3` and `K₃,₃` on six vertices. Each part needs a span of
dimension at least two, and the two spans are orthogonal. There is no `K₄` component.
The graph has at most `2 * d` vertices. -/
def FirstTarget.dropHdim : Prop :=
  ¬ (∀ d : ℕ,
     ∀ (n : Fin (2 * d + 1)) (G : SimpleGraph (Fin n.val)),
     ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
     ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
       ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
       ∃ f : Fin n.val → EuclideanSpace ℝ (Fin d),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-- Counterexample: `d = 4` and `K₆`. Its sole component is not `K₅`, but six
nonzero pairwise orthogonal vectors cannot fit in `ℝ⁴`.
The graph has at most `2 * d` vertices. -/
def FirstTarget.dropHdegree : Prop :=
  ¬ (∀ d : ℕ,
     ∀ (_hdim : 3 < d),
     ∀ (n : Fin (2 * d + 1)) (G : SimpleGraph (Fin n.val)),
     ∀ (_hcomponent : ∀ C : G.ConnectedComponent,
       ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1)))),
       ∃ f : Fin n.val → EuclideanSpace ℝ (Fin d),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-- Counterexample: `d = 4` and `K₅`. Its degree is four, but five nonzero
pairwise orthogonal vectors cannot fit in `ℝ⁴`.
The graph has at most `2 * d` vertices. -/
def FirstTarget.dropHcomponent : Prop :=
  ¬ (∀ d : ℕ,
     ∀ (_hdim : 3 < d),
     ∀ (n : Fin (2 * d + 1)) (G : SimpleGraph (Fin n.val)),
     ∀ (_hdegree : ∀ v, (G.neighborSet v).ncard ≤ d),
       ∃ f : Fin n.val → EuclideanSpace ℝ (Fin d),
         Function.Injective f ∧
         (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
         ∀ v w, G.Adj v w → dist (f v) (f w) = 1)

/-!
## Formal proof

Proved in `StatementBProof`. `FirstTarget` is the proved first target; the `witness`,
`separating`, `dropHdim`, `dropHdegree` and `dropHcomponent` lines link every fidelity companion.

* `Question` → open: FKS 2020 Problem 1
* `QuestionFour` → open: FKS 2020 Problem 1
* `FirstTarget` → `FirstTarget.proof`
* `witness` → `witness.proof`
* `separating` → `separating.proof`
* `dropHdim` → `dropHdim.proof`
* `dropHdegree` → `dropHdegree.proof`
* `dropHcomponent` → `dropHcomponent.proof`
-/

end FKSProblem1.StatementB
