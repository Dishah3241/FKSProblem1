/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem1.Standalone.Mathlib.StatementA

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import FKSProblem1.Standalone.Mathlib.Support.GraphDimensionBridge

import GraphDimension.Examples.Sphere
import GraphDimension.Sphere.Basic
import GraphDimension.Sphere.Cycles

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proofs of statement A

`d + 1` pairwise orthogonal nonzero vectors do not fit in `ℝᵈ`, three points of equal positive
norm do not fit in a line, and the two parts of `K_{3,3}` span orthogonal subspaces of dimension
at least two inside `ℝ³`. The five-cycle has a spherical placement in `ℝ³`, and appending a zero
coordinate carries that placement into `ℝ⁴`.
-/

public section

namespace FKSProblem1.StatementA

open SimpleGraph
open scoped InnerProductSpace

noncomputable section

/-! ### Equal norms on a line -/

/-- The point `x` of the real axis, as a point of `EuclideanSpace ℝ (Fin 1)`. -/
def linePt (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 x

lemma dist_linePt (x y : ℝ) : dist (linePt x) (linePt y) = |x - y| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]
  simp [linePt, PiLp.single_eq_same]

lemma norm_linePt (x : ℝ) : ‖linePt x‖ = |x| := by
  have hz : linePt 0 = 0 := by simp [linePt]
  rw [← dist_zero_right, ← hz, dist_linePt, sub_zero]

lemma linePt_ne_linePt {x y : ℝ} (h : x ≠ y) : linePt x ≠ linePt y := by
  intro hxy
  apply h
  simpa [linePt, PiLp.single_eq_same] using
    congrArg (fun p : EuclideanSpace ℝ (Fin 1) => p.ofLp 0) hxy

/-- Three injective points of equal positive norm cannot span a subspace of dimension at most one:
that subspace is a line through the origin, whose sphere meets the common norm in at most two
points. -/
lemma not_injective_three_equal_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {p : Fin 3 → E} (hinj : Function.Injective p) (hnorm : ∀ i, ‖p i‖ = ‖p 0‖) (h0 : p 0 ≠ 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range p)) ≤ 1) : False := by
  open Submodule in
  have hrank1 : Module.finrank ℝ (span ℝ (Set.range p)) = 1 := by
    apply le_antisymm hrank
    rw [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
    intro hz
    have hzero :=
      (finrank_zero_iff_forall_zero (K := ℝ) (V := span ℝ (Set.range p))).mp hz
        ⟨p 0, subset_span ⟨0, rfl⟩⟩
    exact h0 (congrArg Subtype.val hzero)
  have hspan : span ℝ (Set.range p) = ℝ ∙ p 0 :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrank1 (subset_span ⟨0, rfl⟩) h0
  have hmem (i : Fin 3) : p i ∈ ℝ ∙ p 0 := by
    rw [← hspan]
    exact subset_span ⟨i, rfl⟩
  choose c hc using fun i => (mem_span_singleton).mp (hmem i)
  have hsign (i : Fin 3) : c i = 1 ∨ c i = -1 := by
    have hmul : |c i| * ‖p 0‖ = ‖p 0‖ := by
      calc |c i| * ‖p 0‖
          = ‖c i • p 0‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = ‖p i‖ := by rw [hc i]
        _ = ‖p 0‖ := hnorm i
    have habs : |c i| = 1 :=
      mul_right_cancel₀ (norm_ne_zero_iff.mpr h0) (by simpa using hmul)
    rcases lt_trichotomy (c i) 0 with hlt | heq | hgt
    · rw [abs_of_neg hlt] at habs
      exact Or.inr (by linarith)
    · rw [heq, abs_zero] at habs
      norm_num at habs
    · rw [abs_of_pos hgt] at habs
      exact Or.inl habs
  have hpair : ∃ i j : Fin 3, i ≠ j ∧ c i = c j := by
    rcases hsign 0 with h0s | h0s <;> rcases hsign 1 with h1s | h1s <;>
      rcases hsign 2 with h2s | h2s
    · exact ⟨0, 1, by decide, by rw [h0s, h1s]⟩
    · exact ⟨0, 1, by decide, by rw [h0s, h1s]⟩
    · exact ⟨0, 2, by decide, by rw [h0s, h2s]⟩
    · exact ⟨1, 2, by decide, by rw [h1s, h2s]⟩
    · exact ⟨1, 2, by decide, by rw [h1s, h2s]⟩
    · exact ⟨0, 2, by decide, by rw [h0s, h2s]⟩
    · exact ⟨0, 1, by decide, by rw [h0s, h1s]⟩
    · exact ⟨0, 1, by decide, by rw [h0s, h1s]⟩
  obtain ⟨i, j, hij, heq⟩ := hpair
  exact hinj.ne hij (by rw [← hc i, ← hc j, heq])

/-- `K_m` has no spherical placement in `ℝⁿ` when `n < m`: a spherical placement would be `m`
pairwise orthogonal nonzero vectors. -/
private lemma not_sphereEmbeddable_top {n m : ℕ} (h : n < m) :
    ¬ (⊤ : SimpleGraph (Fin m)).SphereEmbeddable n := by
  intro hsph
  rw [SphereEmbeddable.iff_orthogonal] at hsph
  obtain ⟨f, _, hfNorm, hfOrth⟩ := hsph
  have hne : ∀ i, f i ≠ 0 := by
    intro i hi
    have := hfNorm i
    rw [hi, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at this
    norm_num at this
  have ho : Pairwise fun i j : Fin m => ⟪f i, f j⟫_ℝ = 0 := by
    intro i j hij
    exact hfOrth i j (by rwa [top_adj])
  have hcard :=
    (linearIndependent_of_ne_zero_of_inner_eq_zero hne ho).fintype_card_le_finrank
  simp only [finrank_euclideanSpace_fin, Fintype.card_fin] at hcard
  omega

lemma not_hasSphericalDimAtMost_top {n m : ℕ} (h : n < m) :
    ¬ HasSphericalDimAtMost n (⊤ : SimpleGraph (Fin m)) := by
  rw [FKSProblem1.hasSphericalDimAtMost_iff_sphereEmbeddable]
  exact not_sphereEmbeddable_top h

lemma k2_on_line :
    ∃ f : Fin 2 → EuclideanSpace ℝ (Fin 1), Function.Injective f ∧ dist (f 0) (f 1) = 1 := by
  refine ⟨fun i => if i = 0 then linePt 0 else linePt 1, ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd h (linePt_ne_linePt (by norm_num))
    · exact absurd h (linePt_ne_linePt (by norm_num)).symm
    · rfl
  · simp [dist_linePt, abs_neg, abs_one]

lemma three_equal_norm_on_line :
    ∃ f : Fin 3 → EuclideanSpace ℝ (Fin 1), ∀ v, ‖f v‖ = 1 / √2 := by
  refine ⟨fun _ => linePt (1 / √2), fun v => ?_⟩
  rw [norm_linePt, abs_of_nonneg (by positivity)]

lemma not_hasSpherical_bot_three : ¬ HasSphericalDimAtMost 1 (⊥ : SimpleGraph (Fin 3)) := by
  intro ⟨f, hf, hnorm, _⟩
  have h0 : f 0 ≠ 0 := by
    intro hz
    have h0eq := hnorm 0
    rw [hz, norm_zero] at h0eq
    exact ne_of_lt (by positivity : (0 : ℝ) < 1 / √2) h0eq
  have hnorm' : ∀ i, ‖f i‖ = ‖f 0‖ := fun i => by rw [hnorm i, hnorm 0]
  have hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range f)) ≤ 1 :=
    (Submodule.finrank_le _).trans_eq finrank_euclideanSpace_fin
  exact not_injective_three_equal_norm hf hnorm' h0 hrank

/-! ### `K_{d+1}` with an isolated vertex -/

/-- `K_{d+1} ⊔ K₁` on `Fin (d + 2)`: distinct vertices are adjacent exactly when neither is the
last index. -/
@[expose] def cliqueJoinIsolate (d : ℕ) : SimpleGraph (Fin (d + 2)) :=
  fromRel fun v w => v.val < d + 1 ∧ w.val < d + 1

lemma cliqueJoinIsolate_def (d : ℕ) :
    cliqueJoinIsolate d =
      fromRel (fun v w : Fin (d + 2) => v.val < d + 1 ∧ w.val < d + 1) := rfl

lemma cliqueJoinIsolate_adj {d : ℕ} {a b : Fin (d + 2)} :
    (cliqueJoinIsolate d).Adj a b ↔ a ≠ b ∧ a.val < d + 1 ∧ b.val < d + 1 := by
  rw [cliqueJoinIsolate, fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h.1, h.2⟩
    · exact ⟨hne, h.2, h.1⟩
  · rintro ⟨hne, ha, hb⟩
    exact ⟨hne, Or.inl ⟨ha, hb⟩⟩

lemma cliqueJoinIsolate_adj_ne {d : ℕ} {a b : Fin (d + 2)} :
    (cliqueJoinIsolate d).Adj a b ↔ a.val ≠ d + 1 ∧ b.val ≠ d + 1 ∧ a ≠ b := by
  rw [cliqueJoinIsolate_adj]
  constructor
  · rintro ⟨hne, ha, hb⟩
    exact ⟨by have := a.isLt; omega, by have := b.isLt; omega, hne⟩
  · rintro ⟨ha, hb, hne⟩
    exact ⟨hne, by have := a.isLt; omega, by have := b.isLt; omega⟩

/-- The clique vertices, those whose value is strictly less than `d + 1`, are a copy of
`Fin (d + 1)`. -/
def cliqueIdx (d : ℕ) : {w : Fin (d + 2) // w.val < d + 1} ≃ Fin (d + 1) where
  toFun w := ⟨w.1.val, w.2⟩
  invFun i := ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, i.isLt⟩
  left_inv w := by ext; rfl
  right_inv i := by ext; rfl

lemma cliqueJoin_zero_lt (d : ℕ) : ((0 : Fin (d + 2))).val < d + 1 := by
  rw [Fin.val_zero]
  exact Nat.succ_pos d

lemma cliqueJoin_walk_mem {d : ℕ} {a b : Fin (d + 2)} (p : (cliqueJoinIsolate d).Walk a b)
    (ha : a.val < d + 1) : b.val < d + 1 := by
  induction p with
  | nil => exact ha
  | cons h _ ih => exact ih ((cliqueJoinIsolate_adj.mp h).2.2)

lemma cliqueJoin_reachable_zero {d : ℕ} {b : Fin (d + 2)} :
    (cliqueJoinIsolate d).Reachable 0 b ↔ b.val < d + 1 := by
  constructor
  · intro h
    exact h.elim fun p => cliqueJoin_walk_mem p (cliqueJoin_zero_lt d)
  · intro hb
    by_cases h0 : b = 0
    · rw [h0]
    · have hne : (0 : Fin (d + 2)) ≠ b := fun h => h0 h.symm
      exact ⟨Walk.cons (cliqueJoinIsolate_adj.mpr ⟨hne, cliqueJoin_zero_lt d, hb⟩) Walk.nil⟩

lemma cliqueJoin_hasComponent (d : ℕ) : HasCompleteComponent d (cliqueJoinIsolate d) := by
  refine ⟨0,
    ⟨(Equiv.subtypeEquivRight fun b => cliqueJoin_reachable_zero (b := b)).trans (cliqueIdx d)⟩,
    ?_⟩
  intro a b ha hb hab
  exact cliqueJoinIsolate_adj.mpr ⟨hab, cliqueJoin_reachable_zero.mp ha,
    cliqueJoin_reachable_zero.mp hb⟩

lemma cliqueSet_card (d : ℕ) :
    (Finset.univ.filter fun w : Fin (d + 2) => w.val < d + 1).card = d + 1 := by
  rw [← Fintype.card_subtype, Fintype.card_congr (cliqueIdx d), Fintype.card_fin]

open Classical in
lemma cliqueJoin_degree_clique {d : ℕ} {v : Fin (d + 2)} (hv : v.val < d + 1) :
    (cliqueJoinIsolate d).degree v = d := by
  rw [← card_neighborFinset_eq_degree]
  have hfin :
      (cliqueJoinIsolate d).neighborFinset v =
        (Finset.univ.filter fun w : Fin (d + 2) => w.val < d + 1).erase v := by
    ext w
    simp only [mem_neighborFinset, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
      true_and, cliqueJoinIsolate_adj]
    constructor
    · rintro ⟨hne, _, hw⟩
      exact ⟨hne.symm, hw⟩
    · rintro ⟨hne, hw⟩
      exact ⟨hne.symm, hv, hw⟩
  have hmem : v ∈ Finset.univ.filter fun w : Fin (d + 2) => w.val < d + 1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  rw [hfin, Finset.card_erase_of_mem hmem, cliqueSet_card]
  omega

open Classical in
lemma cliqueJoin_degree_isolate {d : ℕ} {v : Fin (d + 2)} (hv : ¬ v.val < d + 1) :
    (cliqueJoinIsolate d).degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero]
  ext w
  simp only [mem_neighborFinset, Finset.notMem_empty, iff_false, cliqueJoinIsolate_adj]
  rintro ⟨_, hv', _⟩
  exact hv hv'

open Classical in
lemma cliqueJoin_ncard (d : ℕ) (v : Fin (d + 2)) :
    ((cliqueJoinIsolate d).neighborSet v).ncard ≤ d := by
  rw [ncard_neighborSet]
  by_cases hv : v.val < d + 1
  · rw [cliqueJoin_degree_clique hv]
  · rw [cliqueJoin_degree_isolate hv]
    omega

lemma cliqueJoin_not_spherical (d : ℕ) :
    ¬ HasSphericalDimAtMost d (cliqueJoinIsolate d) := by
  rw [FKSProblem1.hasSphericalDimAtMost_iff_sphereEmbeddable]
  intro h
  let φ : (⊤ : SimpleGraph (Fin (d + 1))) →g cliqueJoinIsolate d :=
    { toFun := fun i => ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      map_rel' := by
        intro a b hab
        rw [top_adj] at hab
        rw [cliqueJoinIsolate_adj]
        exact ⟨fun h => hab (Fin.ext (congrArg (fun x : Fin (d + 2) => x.val) h)),
          a.isLt, b.isLt⟩ }
  have hφ : Function.Injective φ := fun a b h =>
    Fin.ext (congrArg (fun x : Fin (d + 2) => x.val) h)
  exact not_sphereEmbeddable_top (Nat.lt_succ_self d) (h.comap φ hφ)

/-- A reachability class of size `d + 1` on which every pair is adjacent is a connected component
isomorphic to `K_{d+1}`. -/
lemma hasCompleteComponent_iff (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    HasCompleteComponent d G ↔
      ∃ C : G.ConnectedComponent,
        Nonempty (C.toSimpleGraph ≃g (⊤ : SimpleGraph (Fin (d + 1)))) := by
  let e (v : Fin n) : (G.connectedComponentMk v).supp ≃ {w : Fin n // G.Reachable v w} :=
    Equiv.subtypeEquivRight fun w => by
      simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, reachable_comm]
  constructor
  · rintro ⟨v, ⟨f⟩, h⟩
    refine ⟨G.connectedComponentMk v, ⟨{ (e v).trans f with map_rel_iff' := ?_ }⟩⟩
    intro a b
    change ((e v).trans f) a ≠ ((e v).trans f) b ↔ G.Adj a.val b.val
    rw [((e v).trans f).injective.ne_iff]
    constructor
    · intro hab
      exact h _ _ ((e v) a).property ((e v) b).property fun heq => hab (Subtype.ext heq)
    · intro hab heq
      exact hab.ne (congrArg Subtype.val heq)
  · rintro ⟨C, ⟨f⟩⟩
    obtain ⟨v, rfl⟩ := C.exists_rep
    refine ⟨v, ⟨(e v).symm.trans f.toEquiv⟩, ?_⟩
    intro a b ha hb hab
    have hne : (e v).symm ⟨a, ha⟩ ≠ (e v).symm ⟨b, hb⟩ := by
      intro heq
      exact hab (congrArg Subtype.val ((e v).symm.injective heq))
    exact f.map_rel_iff.mp (f.injective.ne hne)

lemma not_hasCompleteComponent_iso (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    ¬ HasCompleteComponent d G ↔
      ∀ C : G.ConnectedComponent,
        ¬ Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (d + 1))) := by
  rw [hasCompleteComponent_iff, completeGraph_eq_top]
  exact not_exists

lemma not_iso_of_card_ne {n k : ℕ} (G : SimpleGraph (Fin n)) (h : n ≠ k) :
    ¬ Nonempty (G ≃g completeGraph (Fin k)) := by
  intro ⟨e⟩
  have hc := Fintype.card_congr e.toEquiv
  rw [Fintype.card_fin, Fintype.card_fin] at hc
  exact h hc

lemma cliqueJoin_not_iso (d : ℕ) :
    ¬ Nonempty (cliqueJoinIsolate d ≃g completeGraph (Fin (d + 1))) :=
  not_iso_of_card_ne _ (by omega)

lemma cliqueJoin_component_iso (d : ℕ) :
    ∃ C : (cliqueJoinIsolate d).ConnectedComponent,
      Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (d + 1))) :=
  (hasCompleteComponent_iff d _).mp (cliqueJoin_hasComponent d)

/-! ### Complete graphs -/

lemma completeGraph_ncard {n : ℕ} (v : Fin n) :
    ((completeGraph (Fin n)).neighborSet v).ncard = n - 1 := by
  rw [ncard_neighborSet, ← card_neighborFinset_eq_degree, neighborFinset_top,
    Finset.card_compl, Finset.card_singleton, Fintype.card_fin]

lemma completeGraph_spherical (n : ℕ) :
    HasSphericalDimAtMost n (completeGraph (Fin n)) := by
  rw [FKSProblem1.hasSphericalDimAtMost_iff_sphereEmbeddable, completeGraph_eq_top]
  exact sphereEmbeddable_completeGraph n

open Classical in
lemma not_hasCompleteComponent_completeGraph {n d : ℕ} (h : n ≠ d + 1) :
    ¬ HasCompleteComponent d (completeGraph (Fin n)) := by
  intro ⟨v, ⟨e⟩, _⟩
  have eall : {w // (completeGraph (Fin n)).Reachable v w} ≃ Fin n :=
    (Equiv.subtypeEquivRight fun w =>
      iff_of_true (reachable_top (u := v) (v := w)) trivial).trans
      (Equiv.subtypeUnivEquiv fun _ => trivial)
  have hcard : d + 1 = n := by
    have h1 : Fintype.card {w // (completeGraph (Fin n)).Reachable v w} = d + 1 := by
      rw [Fintype.card_congr e, Fintype.card_fin]
    have h2 : Fintype.card {w // (completeGraph (Fin n)).Reachable v w} = n := by
      rw [Fintype.card_congr eall, Fintype.card_fin]
    exact h1.symm.trans h2
  exact h hcard.symm

lemma completeGraph_no_component_iso {n d : ℕ} (h : n ≠ d + 1) :
    ∀ C : (completeGraph (Fin n)).ConnectedComponent,
      ¬ Nonempty (C.toSimpleGraph ≃g completeGraph (Fin (d + 1))) :=
  (not_hasCompleteComponent_iso d _).mp (not_hasCompleteComponent_completeGraph h)

/-! ### The utility graph `K_{3,3}` on `Fin 6` -/

/-- `K_{3,3}` on `Fin 6`, with parts `{0, 1, 2}` and `{3, 4, 5}`. -/
def utilityGraph : SimpleGraph (Fin 6) :=
  fromRel fun v w => v.val < 3 ∧ 3 ≤ w.val

def utilityLeft (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩

def utilityRight (i : Fin 3) : Fin 6 := ⟨i.val + 3, by omega⟩

lemma utilityLeft_injective : Function.Injective utilityLeft := fun i j h =>
  Fin.ext (by simpa [utilityLeft] using congrArg Fin.val h)

lemma utilityRight_injective : Function.Injective utilityRight := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [utilityRight, Fin.val_mk] at this
  omega

lemma utility_adj_iff {a b : Fin 6} :
    utilityGraph.Adj a b ↔
      (a.val < 3 ∧ 3 ≤ b.val) ∨ (b.val < 3 ∧ 3 ≤ a.val) := by
  rw [utilityGraph, fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    cases h with
    | inl h => omega
    | inr h => omega

lemma utility_cross (i j : Fin 3) : utilityGraph.Adj (utilityLeft i) (utilityRight j) := by
  refine utility_adj_iff.mpr (Or.inl ⟨?_, ?_⟩)
  · simp [utilityLeft]
  · simp [utilityRight]

open Classical in
lemma utility_degree (v : Fin 6) : utilityGraph.degree v = 3 := by
  rw [← card_neighborFinset_eq_degree]
  by_cases hv : v.val < 3
  · have hset :
        utilityGraph.neighborFinset v = (Finset.univ : Finset (Fin 3)).image utilityRight := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hadj
        have hge : 3 ≤ w.val := by
          have h := utility_adj_iff.mp hadj
          omega
        refine ⟨⟨w.val - 3, by omega⟩, ?_⟩
        apply Fin.ext
        simp only [utilityRight, Fin.val_mk]
        omega
      · rintro ⟨j, rfl⟩
        exact utility_adj_iff.mpr <| Or.inl ⟨hv, by simp [utilityRight]⟩
    rw [hset, Finset.card_image_of_injective _ utilityRight_injective, Finset.card_univ,
      Fintype.card_fin]
  · have hv' : 3 ≤ v.val := by omega
    have hset :
        utilityGraph.neighborFinset v = (Finset.univ : Finset (Fin 3)).image utilityLeft := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hadj
        have hlt : w.val < 3 := by
          have h := utility_adj_iff.mp hadj
          omega
        refine ⟨⟨w.val, hlt⟩, ?_⟩
        apply Fin.ext
        simp [utilityLeft]
      · rintro ⟨j, rfl⟩
        exact utility_adj_iff.mpr <| Or.inr ⟨by simp [utilityLeft], hv'⟩
    rw [hset, Finset.card_image_of_injective _ utilityLeft_injective, Finset.card_univ,
      Fintype.card_fin]

open Classical in
lemma utility_ncard (v : Fin 6) : (utilityGraph.neighborSet v).ncard = 3 := by
  rw [ncard_neighborSet, utility_degree]

open Classical in
lemma utility_not_component : ¬ HasCompleteComponent 3 utilityGraph := by
  intro ⟨v, ⟨e⟩, hadj⟩
  let s := Finset.univ.filter fun w : Fin 6 => utilityGraph.Reachable v w
  have hs : s.card = 4 := by
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fin]
  let left := s.filter fun w => w.val < 3
  let right := s.filter fun w => ¬ w.val < 3
  have hdisj : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro w hwL hwR
    simp only [left, right, Finset.mem_filter] at hwL hwR
    exact hwR.2 hwL.2
  have hunion : left ∪ right = s := by
    ext w
    simp only [Finset.mem_union, left, right, s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩)
      · exact hw
      · exact hw
    · intro hw
      by_cases hwv : w.val < 3
      · exact Or.inl ⟨hw, hwv⟩
      · exact Or.inr ⟨hw, hwv⟩
  have hleft : left.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hne
    have haR : utilityGraph.Reachable v a := by
      simp only [left, s, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha.1
    have hbR : utilityGraph.Reachable v b := by
      simp only [left, s, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hb.1
    have haL : a.val < 3 := by
      simp only [left, Finset.mem_filter] at ha
      exact ha.2
    have hbL : b.val < 3 := by
      simp only [left, Finset.mem_filter] at hb
      exact hb.2
    have := utility_adj_iff.mp (hadj a b haR hbR hne)
    omega
  have hright : right.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hne
    have haR : utilityGraph.Reachable v a := by
      simp only [right, s, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha.1
    have hbR : utilityGraph.Reachable v b := by
      simp only [right, s, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hb.1
    have haRge : 3 ≤ a.val := by
      simp only [right, Finset.mem_filter] at ha
      omega
    have hbRge : 3 ≤ b.val := by
      simp only [right, Finset.mem_filter] at hb
      omega
    have := utility_adj_iff.mp (hadj a b haR hbR hne)
    omega
  have hcard : s.card = left.card + right.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  omega

/-- Each part of `K_{3,3}` is orthogonal to the other and needs two dimensions, so the two spans
do not fit in `ℝ³`. -/
private lemma utility_not_sphereEmbeddable : ¬ utilityGraph.SphereEmbeddable 3 := by
  intro h
  rw [SphereEmbeddable.iff_orthogonal] at h
  obtain ⟨f, hfInj, hfNorm, hfOrth⟩ := h
  let L : Fin 3 → EuclideanSpace ℝ (Fin 3) := f ∘ utilityLeft
  let R : Fin 3 → EuclideanSpace ℝ (Fin 3) := f ∘ utilityRight
  have hLeq : L = f ∘ utilityLeft := rfl
  have hReq : R = f ∘ utilityRight := rfl
  have hLinj : Function.Injective L := by
    rw [hLeq]
    exact hfInj.comp utilityLeft_injective
  have hRinj : Function.Injective R := by
    rw [hReq]
    exact hfInj.comp utilityRight_injective
  have hLnormSq (i : Fin 3) : ‖L i‖ ^ 2 = 1 / 2 := by
    rw [hLeq]
    exact hfNorm (utilityLeft i)
  have hRnormSq (i : Fin 3) : ‖R i‖ ^ 2 = 1 / 2 := by
    rw [hReq]
    exact hfNorm (utilityRight i)
  have hLnorm : ∀ i, ‖L i‖ = ‖L 0‖ := by
    intro i
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (by rw [hLnormSq i, hLnormSq 0])
  have hRnorm : ∀ i, ‖R i‖ = ‖R 0‖ := by
    intro i
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (by rw [hRnormSq i, hRnormSq 0])
  have hL0 : L 0 ≠ 0 := by
    intro hz
    have hsq := hLnormSq 0
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
    norm_num at hsq
  have hR0 : R 0 ≠ 0 := by
    intro hz
    have hsq := hRnormSq 0
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
    norm_num at hsq
  have hcross (i j : Fin 3) : ⟪L i, R j⟫_ℝ = 0 := by
    rw [hLeq, hReq]
    exact hfOrth _ _ (utility_cross i j)
  have horth : Submodule.span ℝ (Set.range L) ≤ (Submodule.span ℝ (Set.range R))ᗮ := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    refine (Submodule.mem_orthogonal (Submodule.span ℝ (Set.range R)) (L i)).mpr ?_
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      rw [real_inner_comm]
      exact hcross i j
    | zero => simp
    | add y z _ _ ihy ihz => rw [inner_add_left, ihy, ihz, add_zero]
    | smul a y _ ihy => rw [real_inner_smul_left, ihy, mul_zero]
  have hLrank : 2 ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range L)) := by
    by_contra hlt
    exact not_injective_three_equal_norm hLinj hLnorm hL0 (by omega)
  have hRrank : 2 ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range R)) := by
    by_contra hlt
    exact not_injective_three_equal_norm hRinj hRnorm hR0 (by omega)
  have hsum :=
    Submodule.finrank_add_finrank_orthogonal (K := Submodule.span ℝ (Set.range R))
  rw [finrank_euclideanSpace_fin] at hsum
  have hmono :
      Module.finrank ℝ (Submodule.span ℝ (Set.range L)) ≤
        Module.finrank ℝ (Submodule.span ℝ (Set.range R))ᗮ :=
    Submodule.finrank_mono horth
  have hle : Module.finrank ℝ (Submodule.span ℝ (Set.range L)) +
      Module.finrank ℝ (Submodule.span ℝ (Set.range R)) ≤ 3 := by
    calc Module.finrank ℝ (Submodule.span ℝ (Set.range L)) +
          Module.finrank ℝ (Submodule.span ℝ (Set.range R))
        ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range R))ᗮ +
            Module.finrank ℝ (Submodule.span ℝ (Set.range R)) :=
          Nat.add_le_add_right hmono _
      _ = 3 := by rw [add_comm]; exact hsum
  have hge := Nat.add_le_add hLrank hRrank
  omega

lemma utility_not_spherical : ¬ HasSphericalDimAtMost 3 utilityGraph := by
  rw [FKSProblem1.hasSphericalDimAtMost_iff_sphereEmbeddable]
  exact utility_not_sphereEmbeddable

/-! ### The five-cycle and the edgeless graph -/

lemma cycle5_ncard (v : Fin 5) : ((cycleGraph 5).neighborSet v).ncard = 2 := by
  rw [cycleGraph_neighborSet (n := 3)]
  refine Set.ncard_pair ?_
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

open Classical in
lemma cycle5_not_component : ¬ HasCompleteComponent 4 (cycleGraph 5) := by
  intro ⟨v, ⟨e⟩, hadj⟩
  let t := (Finset.univ.filter fun w : Fin 5 => (cycleGraph 5).Reachable v w).erase v
  have ht : t.card = 4 := by
    have hmem : v ∈ Finset.univ.filter fun w : Fin 5 => (cycleGraph 5).Reachable v w :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, Reachable.refl v⟩
    have hfilter :
        (Finset.univ.filter fun w : Fin 5 => (cycleGraph 5).Reachable v w).card = 5 := by
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fin]
    rw [Finset.card_erase_of_mem hmem, hfilter]
  have hsub : (t : Set (Fin 5)) ⊆ (cycleGraph 5).neighborSet v := by
    intro w hw
    simp only [t, Finset.mem_coe, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
      true_and] at hw
    simpa [mem_neighborSet] using hadj v w (Reachable.refl v) hw.2 (Ne.symm hw.1)
  have hle : t.card ≤ ((cycleGraph 5).neighborSet v).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub
  rw [cycle5_ncard, ht] at hle
  omega

lemma cycle5_spherical : HasSphericalDimAtMost 4 (cycleGraph 5) := by
  rw [FKSProblem1.hasSphericalDimAtMost_iff_sphereEmbeddable]
  exact (SphereEmbeddable.cycleGraph 5 (by decide)).mono (by decide)

lemma bot_ncard {n : ℕ} (v : Fin n) :
    ((⊥ : SimpleGraph (Fin n)).neighborSet v).ncard = 0 := by
  have h : (⊥ : SimpleGraph (Fin n)).neighborSet v = ∅ := by
    ext w
    simp [neighborSet, bot_adj]
  rw [h]
  simp

open Classical in
lemma bot_not_component {n d : ℕ} (hd : 0 < d) :
    ¬ HasCompleteComponent d (⊥ : SimpleGraph (Fin n)) := by
  intro ⟨v, ⟨e⟩, _⟩
  obtain ⟨a, b, hab⟩ :=
    Fintype.exists_pair_of_one_lt_card
      (α := {w // (⊥ : SimpleGraph (Fin n)).Reachable v w}) (by
        rw [Fintype.card_congr e, Fintype.card_fin]
        omega)
  have hreach : (⊥ : SimpleGraph (Fin n)).Reachable a.1 b.1 := a.2.symm.trans b.2
  exact hab (Subtype.ext (reachable_bot.mp hreach))

/-! ### The companions -/

theorem HasSphericalDimAtMost.separating.proof : HasSphericalDimAtMost.separating :=
  ⟨k2_on_line, by
      simpa [completeGraph_eq_top] using not_hasSphericalDimAtMost_top (by decide : 1 < 2),
    three_equal_norm_on_line, not_hasSpherical_bot_three⟩

theorem HasCompleteComponent.separating.proof : HasCompleteComponent.separating := by
  intro d _hd
  refine ⟨cliqueJoinIsolate d, fun _ _ => cliqueJoinIsolate_adj_ne, cliqueJoin_hasComponent d, ?_⟩
  intro ⟨h, _⟩
  omega

theorem Problem1At.separating.proof : Problem1At.separating := by
  intro d _hd
  refine ⟨d + 2, cliqueJoinIsolate d, rfl,
    (FKSProblem1.maxDegree_le_iff_neighborSet_ncard_le _).mpr (cliqueJoin_ncard d),
    cliqueJoin_hasComponent d, cliqueJoin_not_spherical d, ?_⟩
  intro ⟨h, _⟩
  omega

theorem Problem1BoundedAt.separating.proof : Problem1BoundedAt.separating := by
  intro d hd
  refine ⟨d + 2, cliqueJoinIsolate d, rfl, ?_,
    (FKSProblem1.maxDegree_le_iff_neighborSet_ncard_le _).mpr (cliqueJoin_ncard d),
    cliqueJoin_hasComponent d, cliqueJoin_not_spherical d, ?_⟩
  · omega
  · intro ⟨h, _⟩
    omega

theorem Problem1.witness.proof : Problem1.witness := by
  intro _
  refine ⟨4, 5, cycleGraph 5, by decide, by decide,
    (FKSProblem1.maxDegree_le_iff_neighborSet_ncard_le _).mpr (fun v => by
      rw [cycle5_ncard]; omega),
    cycle5_not_component, cycle5_spherical⟩

theorem Problem1At4.witness.proof : Problem1At4.witness := by
  intro _
  refine ⟨5, cycleGraph 5, by decide,
    (FKSProblem1.maxDegree_le_iff_neighborSet_ncard_le _).mpr (fun v => by
      rw [cycle5_ncard]; omega),
    cycle5_not_component, cycle5_spherical⟩

theorem Problem1Bounded.witness.proof : Problem1Bounded.witness := by
  intro _
  refine ⟨4, 5, cycleGraph 5, by decide, by decide, by decide,
    (FKSProblem1.maxDegree_le_iff_neighborSet_ncard_le _).mpr (fun v => by
      rw [cycle5_ncard]; omega),
    cycle5_not_component, cycle5_spherical⟩

theorem Problem1.dropHd3.proof : Problem1.dropHd3 := by
  intro h
  exact not_hasSpherical_bot_three <|
    h 1 3 (⊥ : SimpleGraph (Fin 3))
      ((FKSProblem1.maxDegree_le_iff_neighborSet_ncard_le _).mpr fun v => by
        rw [bot_ncard]; omega)
      (bot_not_component (by decide))

theorem Problem1Bounded.dropHd3.proof : Problem1Bounded.dropHd3 := by
  intro h
  exact utility_not_spherical <|
    h 3 6 utilityGraph (by decide)
      ((FKSProblem1.maxDegree_le_iff_neighborSet_ncard_le _).mpr fun v => by
        rw [utility_ncard])
      utility_not_component

end

end FKSProblem1.StatementA
