module

public import FKSProblem1.Standalone.Mathlib.StatementA
public import FKSProblem1.Standalone.Mathlib.StatementB

/-!
# Equivalence of the two statements of FKS Problem 1

The placement, degree, component and vertex-count encodings agree in every natural dimension,
including zero, and for every finite vertex count, including the empty graph.
-/

public section

namespace FKSProblem1.Stage1

/-- Norm and distance from zero give the same spherical placement condition. -/
theorem hasSphericalDimAtMost_iff (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    StatementA.HasSphericalDimAtMost d G ↔ StatementB.SphericalRepresentation d G := by
  simp only [StatementA.HasSphericalDimAtMost, StatementB.SphericalRepresentation, dist_zero_right]

open Classical in
/-- The maximum-degree bound is the bound on the cardinality of every neighbor set. -/
theorem maxDegree_le_iff (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.maxDegree ≤ d ↔ ∀ v, (G.neighborSet v).ncard ≤ d := by
  simp only [G.ncard_neighborSet]
  exact ⟨fun h v => (G.degree_le_maxDegree v).trans h,
    G.maxDegree_le_of_forall_degree_le d⟩

/-- A complete reachability class on `d + 1` vertices is exactly a component isomorphic
to the complete graph on `Fin (d + 1)`. -/
theorem hasCompleteComponent_iff (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    StatementA.HasCompleteComponent d G ↔
      ∃ C : G.ConnectedComponent,
        Nonempty (C.toSimpleGraph ≃g (⊤ : SimpleGraph (Fin (d + 1)))) := by
  let e (v : Fin n) : (G.connectedComponentMk v).supp ≃
      {w : Fin n // G.Reachable v w} :=
    Equiv.subtypeEquivRight fun w => by
      simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm]
  constructor
  · rintro ⟨v, ⟨f⟩, h⟩
    refine ⟨G.connectedComponentMk v, ⟨{ (e v).trans f with map_rel_iff' := ?_ }⟩⟩
    intro a b
    change ((e v).trans f) a ≠ ((e v).trans f) b ↔ G.Adj a.val b.val
    rw [((e v).trans f).injective.ne_iff]
    constructor
    · intro hab
      exact h _ _ ((e v) a).property ((e v) b).property
        (fun heq => hab (Subtype.ext heq))
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

/-- Negating the component-existence bridge gives the shared component exception. -/
theorem not_hasCompleteComponent_iff (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    ¬ StatementA.HasCompleteComponent d G ↔
      ∀ C : G.ConnectedComponent,
        ¬ Nonempty (C.toSimpleGraph ≃g SimpleGraph.completeGraph (Fin (d + 1))) := by
  rw [hasCompleteComponent_iff]
  exact not_exists

/-- The two fixed-dimensional questions are equivalent, for every natural dimension. -/
theorem problem1At_iff (d : ℕ) : StatementA.Problem1At d ↔ StatementB.QuestionAt d := by
  classical
  unfold StatementA.Problem1At StatementB.QuestionAt
  simp only [maxDegree_le_iff, not_hasCompleteComponent_iff, hasSphericalDimAtMost_iff,
    StatementB.SphericalRepresentation]

/-- The two questions over all dimensions strictly greater than three are equivalent. -/
theorem problem1_iff : StatementA.Problem1 ↔ StatementB.Question := by
  change (∀ d, 3 < d → StatementA.Problem1At d) ↔
    ∀ d, 3 < d → StatementB.QuestionAt d
  simp only [problem1At_iff]

/-- The two four-dimensional questions are equivalent. -/
theorem problem1At4_iff : StatementA.Problem1At4 ↔ StatementB.QuestionFour := by
  exact problem1At_iff 4

/-- A bounded natural vertex count is equivalently an index in `Fin (2 * d + 1)`. -/
theorem forall_vertexCount_iff (d : ℕ) (P : ℕ → Prop) :
    (∀ n, n ≤ 2 * d → P n) ↔ ∀ n : Fin (2 * d + 1), P n.val := by
  exact ⟨fun h n => h n.val (Nat.le_of_lt_succ n.isLt),
    fun h n hn => h ⟨n, Nat.lt_succ_of_le hn⟩⟩

/-- The questions restricted to at most `2 * d` vertices are equivalent, including both
endpoints of the vertex-count range. -/
theorem problem1BoundedAt_iff (d : ℕ) :
    StatementA.Problem1BoundedAt d ↔ StatementB.QuestionAtMostTwoMulAt d := by
  classical
  unfold StatementA.Problem1BoundedAt StatementB.QuestionAtMostTwoMulAt
  simp only [maxDegree_le_iff, not_hasCompleteComponent_iff, hasSphericalDimAtMost_iff,
    StatementB.SphericalRepresentation]
  conv_lhs =>
    intro n
    rw [forall_comm]
  exact forall_vertexCount_iff d _

/-- The two bounded questions over all dimensions strictly greater than three are equivalent. -/
theorem problem1Bounded_iff : StatementA.Problem1Bounded ↔ StatementB.FirstTarget := by
  change (∀ d, 3 < d → StatementA.Problem1BoundedAt d) ↔
    ∀ d, 3 < d → StatementB.QuestionAtMostTwoMulAt d
  simp only [problem1BoundedAt_iff]

end FKSProblem1.Stage1
