/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem1.Standalone.Mathlib.StatementA

public import GraphDimension.Sphere.Basic

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card

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

end FKSProblem1
