module
public import KKP.Bridge
@[expose] public section

namespace KKP
open Matrix

lemma zero_pair_card (s : ℕ) :
    ((Finset.univ : Finset (Fin 3 × Fin (s + 1))).filter fun x =>
      x.1 = 0 ∧ x.2 = 0).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨(0, 0), ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.ext_iff, Fin.ext_iff]

/-- The adjacency action on the first integer vector. -/
theorem adjacency_witnessU (s : ℕ) (hs : 0 < s) (v : BridgeVertex s) :
    ((bridgeGraph s).adjMatrix ℝ *ᵥ witnessU s) v =
      match v with
      | .inl _ => 2 * (s : ℝ)
      | .inr b => if b.val = 0 then 1 else 0 := by
  cases s with
  | zero => omega
  | succ s =>
    rcases v with ⟨i, a⟩ | b
    · fin_cases i <;>
        simp [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
          SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessU, Fin.sum_univ_succ] <;> ring
    · fin_cases b <;>
        simp [mulVec, dotProduct, Fintype.sum_sum_type, SimpleGraph.adjMatrix,
          bridgeGraph, bridgeAdj, witnessU, zero_pair_card s]

/-- The adjacency action on the second integer vector. -/
theorem adjacency_witnessV (s : ℕ) (hs : 0 < s) (v : BridgeVertex s) :
    ((bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s) v =
      match v with
      | .inl (i, a) => if i.val = 0 ∧ a.val = 0 then 3 * (s : ℝ) else 0
      | .inr b => 9 * (s : ℝ) + if b.val = 0 then (s : ℝ) - 1 else 0 := by
  cases s with
  | zero => omega
  | succ s =>
    rcases v with ⟨i, a⟩ | b
    · fin_cases i <;> by_cases ha : a.val = 0 <;>
        simp [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
          SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessV, Fin.sum_univ_succ, ha]
    · fin_cases b <;>
        simp +contextual [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
          SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessV, Fin.sum_univ_succ] <;> ring

/-- Raw quadratic form of the first integer witness. -/
theorem witnessU_quadratic (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessU s = 6 * (s : ℝ) ^ 2 := by
  cases s with
  | zero => omega
  | succ s =>
    simp [dotProduct, adjacency_witnessU _ hs, Fintype.sum_sum_type, witnessU]
    ring

/-- Raw mixed adjacency form of the two integer witnesses. -/
theorem witnesses_mixed (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s = 3 * (s : ℝ) := by
  cases s with
  | zero => omega
  | succ s =>
    simp [dotProduct, adjacency_witnessV _ hs, Fintype.sum_sum_type,
      Fintype.sum_prod_type, witnessU, Fin.sum_univ_succ]

/-- Raw quadratic form of the second integer witness. -/
theorem witnessV_quadratic (s : ℕ) (hs : 0 < s) :
    witnessV s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s =
      (s : ℝ) * (114 * (s : ℝ) - 6) := by
  cases s with
  | zero => omega
  | succ s =>
    simp [dotProduct, adjacency_witnessV _ hs, Fintype.sum_sum_type,
      Fintype.sum_prod_type, witnessV, Fin.sum_univ_succ]
    ring

/-- The graph has exactly `3s²+7` unordered edges. -/
theorem bridgeGraph_edge_count (s : ℕ) (hs : 0 < s) :
    (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 := by
  cases s with
  | zero => omega
  | succ s =>
    have hdegree (v : BridgeVertex (s + 1)) : (bridgeGraph (s + 1)).degree v =
        ∑ w : BridgeVertex (s + 1), if (bridgeGraph (s + 1)).Adj v w then 1 else 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      simp
    have hsum : (∑ v : BridgeVertex (s + 1), ∑ w : BridgeVertex (s + 1),
        if (bridgeGraph (s + 1)).Adj v w then (1 : ℕ) else 0) = 6 * (s + 1) ^ 2 + 14 := by
      simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_add_distrib,
        bridgeGraph, bridgeAdj, Fin.sum_univ_succ]
      rw [zero_pair_card s]
      ring
    have h := (bridgeGraph (s + 1)).sum_degrees_eq_twice_card_edges
    simp_rw [hdegree] at h
    rw [hsum] at h
    omega

end KKP
