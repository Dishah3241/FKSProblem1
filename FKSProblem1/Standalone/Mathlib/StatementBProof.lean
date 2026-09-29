/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem1.Standalone.Mathlib.StatementB

import FKSProblem1.Standalone.Mathlib.StatementAProof
import FKSProblem1.Standalone.Mathlib.Support.GraphDimensionBridge

import GraphDimension.Examples.Sphere

import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Proofs of statement B

Distance from zero is the norm, so statement A's spherical facts transfer verbatim.
`K₃` is a unit-distance graph in `ℝ²` and not a spherical one: three pairwise orthogonal
nonzero vectors do not fit in a plane. The star on four vertices sends its three leaves into
the orthogonal of the centre, a line, so the placement cannot be injective. `K_d` sits on the
sphere in `ℝᵈ` at the scaled basis. `K_{d+1} ⊔ K₁` has a `K_{d+1}` component and does not.
`K_{3,3}` needs two orthogonal planes, and `K₅` and `K₆` need more than four orthogonal
directions.
-/

public section

namespace FKSProblem1.StatementB

open FKSProblem1.StatementA
open SimpleGraph
open scoped InnerProductSpace

noncomputable section

/-! ### Norm and distance -/

private lemma spherical_iff (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    HasSphericalDimAtMost d G ↔ SphericalRepresentation d G := by
  simp only [HasSphericalDimAtMost, SphericalRepresentation, dist_zero_right]

private lemma norm_eq_inv_sqrt (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ = 1 / Real.sqrt 2 ↔ ‖x‖ ^ 2 = 1 / 2 := by
  have hr : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    norm_num [div_pow, Real.sq_sqrt]
  rw [← hr]
  exact (sq_eq_sq₀ (norm_nonneg x) (by positivity)).symm

private lemma not_spherical_top {n m : ℕ} (h : n < m) :
    ¬ SphericalRepresentation n (completeGraph (Fin m)) := by
  rw [← spherical_iff, completeGraph_eq_top]
  exact not_hasSphericalDimAtMost_top h

private lemma spherical_complete (n : ℕ) :
    SphericalRepresentation n (completeGraph (Fin n)) := by
  rw [← spherical_iff]
  exact completeGraph_spherical n

private lemma k3_unit_distance :
    ∃ f : Fin 3 → EuclideanSpace ℝ (Fin 2),
      Function.Injective f ∧
        ∀ v w, (completeGraph (Fin 3)).Adj v w → dist (f v) (f w) = 1 := by
  rw [completeGraph_eq_top]
  exact (completeGraph_fin_three_unitDistEmbeddable_two_not_sphereEmbeddable).1

private lemma sphere_k2 :
    ∃ f : Fin 2 → EuclideanSpace ℝ (Fin 2),
      Function.Injective f ∧
        (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
        dist (f 0) (f 1) = 1 := by
  obtain ⟨f, hfInj, hfNorm, hfDist⟩ := sphereEmbeddable_completeGraph 2
  refine ⟨f, hfInj, ?_, hfDist 0 1 (by simp [top_adj])⟩
  intro v
  rw [dist_zero_right]
  exact (norm_eq_inv_sqrt (f v)).mpr (hfNorm v)

private lemma bot_two_spherical :
    SphericalRepresentation 2 (⊥ : SimpleGraph (Fin 2)) := by
  obtain ⟨f, hfInj, hnorm, _⟩ := sphere_k2
  refine ⟨f, hfInj, hnorm, ?_⟩
  intro v w h
  exact ((bot_adj v w).mp h).elim

/-! ### The star on four vertices -/

/-- The star with centre `0` and leaves `1, 2, 3`. -/
private def starFin4 : SimpleGraph (Fin 4) :=
  fromRel fun v w : Fin 4 => v = 0 ∨ w = 0

private def starLeaf (i : Fin 3) : Fin 4 := ⟨i.val + 1, by omega⟩

private lemma starLeaf_injective : Function.Injective starLeaf := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [starLeaf, Fin.val_mk] at hv
  omega

private lemma starLeaf_adj (i : Fin 3) : starFin4.Adj 0 (starLeaf i) := by
  rw [starFin4, fromRel_adj]
  refine ⟨?_, Or.inl (Or.inl rfl)⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [starLeaf, Fin.val_zero, Fin.val_mk] at hv
  omega

/-- Collapsing the three leaves onto the second point of a spherical `K₂` puts every star edge
at length one, without separating the leaves. -/
private lemma starFin4_placement :
    ∃ f : Fin 4 → EuclideanSpace ℝ (Fin 2),
      (∀ v, dist (f v) 0 = 1 / Real.sqrt 2) ∧
        ∀ v w, starFin4.Adj v w → dist (f v) (f w) = 1 := by
  obtain ⟨g, _, hgNorm, hgDist⟩ := sphereEmbeddable_completeGraph 2
  refine ⟨fun i => g (if i = 0 then 0 else 1), ?_, ?_⟩
  · intro v
    rw [dist_zero_right]
    exact (norm_eq_inv_sqrt _).mpr (hgNorm _)
  · intro v w hvw
    rw [starFin4, fromRel_adj] at hvw
    have htouch : v = 0 ∨ w = 0 := by
      rcases hvw.2 with h | h
      · exact h
      · exact h.symm
    rcases htouch with hv | hw
    · subst hv
      have hw0 : w ≠ 0 := hvw.1.symm
      change dist (g (if (0 : Fin 4) = 0 then (0 : Fin 2) else 1))
          (g (if w = 0 then (0 : Fin 2) else 1)) = 1
      rw [ite_eq_left rfl, ite_eq_right hw0]
      exact hgDist 0 1 (by simp [top_adj])
    · subst hw
      have hv0 : v ≠ 0 := hvw.1
      change dist (g (if v = 0 then (0 : Fin 2) else 1))
          (g (if (0 : Fin 4) = 0 then (0 : Fin 2) else 1)) = 1
      rw [ite_eq_right hv0, ite_eq_left rfl]
      exact hgDist 1 0 (by simp [top_adj])

/-- An injective spherical placement would put the three leaves in the orthogonal of the centre,
which is a line in `ℝ²`. -/
private lemma starFin4_not_spherical : ¬ SphericalRepresentation 2 starFin4 :=
  open Module Submodule in by
    intro h
    rw [← spherical_iff, FKSProblem1.hasSphericalDimAtMost_iff_sphereEmbeddable,
      SphereEmbeddable.iff_orthogonal] at h
    obtain ⟨f, hfInj, hfNorm, hfOrth⟩ := h
    have hleaf0 : f (starLeaf 0) ≠ 0 := by
      intro hz
      have hsq := hfNorm (starLeaf 0)
      rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
      norm_num at hsq
    have hnorm (i : Fin 3) : ‖f (starLeaf i)‖ = ‖f (starLeaf 0)‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
        rw [hfNorm (starLeaf i), hfNorm (starLeaf 0)]
    have hcenter : f 0 ≠ 0 := by
      intro hz
      have hsq := hfNorm 0
      rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
      norm_num at hsq
    have hmem (i : Fin 3) : f (starLeaf i) ∈ (ℝ ∙ f 0)ᗮ := by
      rw [mem_orthogonal_singleton_iff_inner_right]
      exact hfOrth 0 (starLeaf i) (starLeaf_adj i)
    have hsub : span ℝ (Set.range (f ∘ starLeaf)) ≤ (ℝ ∙ f 0)ᗮ := by
      rw [span_le]
      rintro _ ⟨i, rfl⟩
      exact hmem i
    have hspan1 : Module.finrank ℝ (ℝ ∙ f 0) = 1 := finrank_span_singleton hcenter
    have hsum := finrank_add_finrank_orthogonal (ℝ ∙ f 0)
    rw [finrank_euclideanSpace_fin, hspan1] at hsum
    have horthRank : finrank ℝ (ℝ ∙ f 0)ᗮ = 1 := by
      omega
    have hrank : finrank ℝ (span ℝ (Set.range (f ∘ starLeaf))) ≤ 1 := by
      calc
        finrank ℝ (span ℝ (Set.range (f ∘ starLeaf)))
          ≤ finrank ℝ (ℝ ∙ f 0)ᗮ := finrank_mono hsub
        _ = 1 := horthRank
    exact not_injective_three_equal_norm (hfInj.comp starLeaf_injective) hnorm hleaf0 hrank

/-! ### Complete graphs and the clique with an isolated vertex -/

private lemma complete_ncard_le {n d : ℕ} (h : n ≤ d + 1) (v : Fin n) :
    ((completeGraph (Fin n)).neighborSet v).ncard ≤ d := by
  have hv := completeGraph_ncard v
  omega

private lemma questionAt_separator (d : ℕ) (_hd : 3 < d) :
    (∀ v, ((cliqueJoinIsolate d).neighborSet v).ncard ≤ d) ∧
      ¬ Nonempty ((cliqueJoinIsolate d) ≃g completeGraph (Fin (d + 1))) ∧
        (∃ C : (cliqueJoinIsolate d).ConnectedComponent,
          Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (d + 1)))) ∧
          ¬ SphericalRepresentation d (cliqueJoinIsolate d) ∧
            (QuestionAt d →
              (∀ C : (cliqueJoinIsolate d).ConnectedComponent,
                ¬ Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (d + 1)))) →
                SphericalRepresentation d (cliqueJoinIsolate d)) := by
  refine ⟨cliqueJoin_ncard d, cliqueJoin_not_iso d, cliqueJoin_component_iso d, ?_, ?_⟩
  · rw [← spherical_iff]
    exact cliqueJoin_not_spherical d
  · intro _ hC
    obtain ⟨C, hIso⟩ := cliqueJoin_component_iso d
    exact (hC C hIso).elim

/-- A vertex count `n ≤ 2 * d` is an index in `Fin (2 * d + 1)`, and conversely. -/
private lemma questionBounded_iff (d : ℕ) :
    QuestionAtMostTwoMulAt d ↔
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 2 * d →
        (∀ v, (G.neighborSet v).ncard ≤ d) →
        (∀ C : G.ConnectedComponent,
          ¬ Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (d + 1)))) →
        SphericalRepresentation d G := by
  unfold QuestionAtMostTwoMulAt
  simp only [SphericalRepresentation]
  constructor
  · intro h n G hn hdeg hcomp
    exact h ⟨n, Nat.lt_succ_of_le hn⟩ G hdeg hcomp
  · intro h n G hdeg hcomp
    exact h n.val G (Nat.le_of_lt_succ n.isLt) hdeg hcomp

/-! ### `K_{3,3}`, `K₅` and `K₆` -/

private lemma utility_degree_le (v : Fin 6) :
    (utilityGraph.neighborSet v).ncard ≤ 3 := by
  have hv := utility_ncard v
  omega

private lemma utility_no_k4 :
    ∀ C : utilityGraph.ConnectedComponent,
      ¬ Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (3 + 1))) :=
  (not_hasCompleteComponent_iso 3 utilityGraph).mp utility_not_component

private lemma not_spherical_utility : ¬ SphericalRepresentation 3 utilityGraph := by
  rw [← spherical_iff]
  exact utility_not_spherical

private lemma k6_no_k5 :
    ∀ C : (completeGraph (Fin 6)).ConnectedComponent,
      ¬ Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (4 + 1))) :=
  completeGraph_no_component_iso (n := 6) (d := 4) (by decide)

private lemma k5_degree_le (v : Fin 5) :
    ((completeGraph (Fin 5)).neighborSet v).ncard ≤ 4 :=
  complete_ncard_le (by decide) v

/-! ### The companions -/

theorem SphericalRepresentation.separating.proof : SphericalRepresentation.separating :=
  ⟨⟨k3_unit_distance, not_spherical_top (by decide : (2 : ℕ) < 3)⟩,
    ⟨starFin4_placement, starFin4_not_spherical⟩, sphere_k2, bot_two_spherical⟩

theorem QuestionAt.witness.proof : QuestionAt.witness := by
  intro d _hd
  exact ⟨fun v => complete_ncard_le (by omega) v,
    completeGraph_no_component_iso (n := d) (d := d) (by omega),
    spherical_complete d, fun _ => spherical_complete d⟩

theorem QuestionAt.separating.proof : QuestionAt.separating := by
  intro d hd
  rw [← cliqueJoinIsolate_def]
  exact questionAt_separator d hd

theorem Question.witness.proof : Question.witness :=
  ⟨QuestionAt.witness.proof, fun h => h 4 (by decide)⟩

theorem Question.separating.proof : Question.separating :=
  ⟨QuestionAt.separating.proof, Iff.rfl⟩

theorem QuestionFour.witness.proof : QuestionFour.witness :=
  ⟨fun v => complete_ncard_le (by decide) v,
    completeGraph_no_component_iso (n := 4) (d := 4) (by decide),
    spherical_complete 4, fun _ => spherical_complete 4⟩

theorem QuestionFour.separating.proof : QuestionFour.separating :=
  ⟨QuestionAt.separating.proof, Iff.rfl⟩

theorem QuestionAtMostTwoMulAt.witness.proof : QuestionAtMostTwoMulAt.witness :=
  ⟨QuestionAt.witness.proof, fun d _hd => ⟨by omega, fun _ => spherical_complete d⟩⟩

theorem QuestionAtMostTwoMulAt.separating.proof : QuestionAtMostTwoMulAt.separating :=
  ⟨QuestionAt.separating.proof, fun d hd => ⟨by omega, questionBounded_iff d⟩⟩

theorem FirstTarget.witness.proof : FirstTarget.witness :=
  ⟨QuestionAtMostTwoMulAt.witness.proof, fun _ => spherical_complete 4⟩

theorem FirstTarget.separating.proof : FirstTarget.separating :=
  ⟨QuestionAtMostTwoMulAt.separating.proof, Iff.rfl⟩

theorem Question.dropHdim.proof : Question.dropHdim := by
  intro h
  exact not_spherical_utility <|
    h 3 6 utilityGraph utility_degree_le utility_no_k4

theorem Question.dropHdegree.proof : Question.dropHdegree := by
  intro h
  exact not_spherical_top (by decide : (4 : ℕ) < 6) <|
    h 4 (by decide) 6 (completeGraph (Fin 6)) k6_no_k5

theorem Question.dropHcomponent.proof : Question.dropHcomponent := by
  intro h
  exact not_spherical_top (by decide : (4 : ℕ) < 5) <|
    h 4 (by decide) 5 (completeGraph (Fin 5)) k5_degree_le

theorem QuestionFour.dropHdegree.proof : QuestionFour.dropHdegree := by
  intro h
  exact not_spherical_top (by decide : (4 : ℕ) < 6) <|
    h 6 (completeGraph (Fin 6)) k6_no_k5

theorem QuestionFour.dropHcomponent.proof : QuestionFour.dropHcomponent := by
  intro h
  exact not_spherical_top (by decide : (4 : ℕ) < 5) <|
    h 5 (completeGraph (Fin 5)) k5_degree_le

theorem FirstTarget.dropHdim.proof : FirstTarget.dropHdim := by
  intro h
  exact not_spherical_utility <|
    h 3 ⟨6, by decide⟩ utilityGraph utility_degree_le utility_no_k4

theorem FirstTarget.dropHdegree.proof : FirstTarget.dropHdegree := by
  intro h
  exact not_spherical_top (by decide : (4 : ℕ) < 6) <|
    h 4 (by decide) ⟨6, by decide⟩ (completeGraph (Fin 6)) k6_no_k5

theorem FirstTarget.dropHcomponent.proof : FirstTarget.dropHcomponent := by
  intro h
  exact not_spherical_top (by decide : (4 : ℕ) < 5) <|
    h 4 (by decide) ⟨5, by decide⟩ (completeGraph (Fin 5)) k5_degree_le

end

end FKSProblem1.StatementB
