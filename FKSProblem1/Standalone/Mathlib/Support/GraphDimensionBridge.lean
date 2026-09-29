/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem1.Standalone.Mathlib.StatementA

public import GraphDimension.Sphere.Basic

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card

import GraphDimension.Combinatorics.SimpleGraph.CompleteComponent
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Bridge to the shared unit-distance library

Statement A's spherical predicate and the shared library's `SimpleGraph.SphereEmbeddable` say the
same thing: an injective placement of the vertices in `EuclideanSpace ℝ (Fin d)` under which every
vertex lies on the sphere of radius `1 / √2` and every edge has length one, with non-edges
unconstrained. The equivalence is not definitional — the statement fixes the norm
`‖f v‖ = 1 / √2` while the library fixes the squared norm `‖f v‖ ^ 2 = 1 / 2` — so the bridge
converts the norm equation through the nonnegativity of a norm and carries the placement map and
the edge equations over unchanged.

The degree bridge restates the hypothesis `G.maxDegree ≤ d` as the bound on every neighbor set's
cardinality, the form the downstream degree and counting arguments consume. It degenerates
correctly: for the empty graph `G.maxDegree` is `0` and the neighbor-set quantifier is vacuous.

Under that same degree bound, the component bridge identifies Statement A's exception — no
connected component isomorphic to `K_{d + 1}` — with the absence of a clique of order `d + 1`:
a clique of order `d + 1` already exhausts the `d` neighbours of each of its vertices, so it is
the support of a connected component, and conversely a complete component contains such a clique.
-/

public section

namespace FKSProblem1

/-- Statement A's spherical predicate and the shared library's `SimpleGraph.SphereEmbeddable`
agree: an injective placement whose vertices have norm `1 / √2` (the statement) is exactly one
whose vertices have squared norm `1 / 2` (the library), since a norm is nonnegative and both
constants are. The placement map and the edge equations carry over unchanged, so either side's
placement results transfer to the other verbatim. -/
theorem hasSphericalDimAtMost_iff_sphereEmbeddable
    {n d : ℕ} (G : SimpleGraph (Fin n)) :
    StatementA.HasSphericalDimAtMost d G ↔ G.SphereEmbeddable d := by
  have hr : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    norm_num [div_pow, Real.sq_sqrt]
  have hn (x : EuclideanSpace ℝ (Fin d)) :
      ‖x‖ = 1 / Real.sqrt 2 ↔ ‖x‖ ^ 2 = 1 / 2 := by
    rw [← hr]
    exact (sq_eq_sq₀ (norm_nonneg x) (by positivity)).symm
  constructor
  · rintro ⟨f, hf, hnorm, hedge⟩
    exact ⟨f, hf, fun v => (hn (f v)).mp (hnorm v), hedge⟩
  · rintro ⟨f, hf, hnorm, hedge⟩
    exact ⟨f, hf, fun v => (hn (f v)).mpr (hnorm v), hedge⟩

open Classical in
/-- The bound `G.maxDegree ≤ d` holds exactly when every neighbor set has at most `d` elements,
including for the empty graph, where `G.maxDegree` is `0` and the quantifier is vacuous. -/
theorem maxDegree_le_iff_neighborSet_ncard_le
    {n d : ℕ} (G : SimpleGraph (Fin n)) :
    G.maxDegree ≤ d ↔ ∀ v, (G.neighborSet v).ncard ≤ d := by
  have hn (v : Fin n) : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree]
  simp_rw [hn]
  exact ⟨fun h v => (G.degree_le_maxDegree v).trans h,
    fun h => G.maxDegree_le_of_forall_degree_le d h⟩

open Classical in
/-- Under the degree bound, Statement A's exception `HasCompleteComponent d G` is exactly the
presence of a clique of order `d + 1`. A complete component is one: its reachability class is a
clique of order `d + 1`, and the component isomorphism counts its vertices. Conversely, a clique
of order `d + 1` already exhausts the `d` neighbours of each of its vertices, so no edge leaves
it and it is the support of a connected component. -/
theorem hasCompleteComponent_iff_not_cliqueFree
    {n d : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ d) :
    StatementA.HasCompleteComponent d G ↔ ¬ G.CliqueFree (d + 1) := by
  constructor
  · rintro ⟨v, ⟨e⟩, hcomp⟩
    have hcard : Fintype.card {w // G.Reachable v w} = d + 1 := by
      rw [Fintype.card_congr e, Fintype.card_fin]
    refine fun h => h {w | G.Reachable v w}.toFinset ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Set.mem_toFinset] at ha hb
      exact hcomp a b ha hb hab
    · rw [← Set.ncard_eq_toFinset_card', ← Set.fintypeCard_eq_ncard]
      exact hcard
  · intro h
    have hex : ∃ t : Finset (Fin n), G.IsNClique (d + 1) t := by
      by_contra hc
      exact h fun t ht => hc ⟨t, ht⟩
    obtain ⟨s, hs⟩ := hex
    obtain ⟨c, hsupp⟩ := hs.exists_connectedComponent_supp_eq hdeg
    have hspos : 0 < s.card := by rw [hs.card_eq]; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hspos
    have hvC : G.connectedComponentMk v = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp
        (by rw [hsupp]; exact Finset.mem_coe.mpr hv)
    have hmem (w : Fin n) : G.Reachable v w ↔ w ∈ (↑s : Set (Fin n)) := by
      rw [← hsupp, SimpleGraph.ConnectedComponent.mem_supp_iff, ← hvC,
        SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm]
    have hcard : Fintype.card {w // G.Reachable v w} = d + 1 := by
      have hsub : {w : Fin n // G.Reachable v w} ≃
          {w : Fin n // w ∈ (↑s : Set (Fin n))} := Equiv.subtypeEquivRight hmem
      rw [Fintype.card_congr hsub]
      exact Fintype.card_coe s |>.trans hs.card_eq
    exact ⟨v, ⟨Fintype.equivFinOfCardEq hcard⟩, fun a b ha hb hab =>
      hs.isClique ((hmem a).mp ha) ((hmem b).mp hb) hab⟩

end FKSProblem1
