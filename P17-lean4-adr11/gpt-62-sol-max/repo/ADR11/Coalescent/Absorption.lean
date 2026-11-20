module

public import ADR11.Coalescent.Factorization

/-! At infinite time, only the path weights ending with one root survive. -/

@[expose] public section

namespace ADR11

open Finset Real Filter Topology

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- `exp(-(m choose 2) t)` tends to `1` if `m = 1` and to `0` if `m ≥ 2`. -/
private theorem absorb_tendsto_exp (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ => exp (-(rate m * t))) atTop
      (𝓝 (if m = 1 then 1 else 0)) := by
  split_ifs with h
  · subst h
    simp
  · exact tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (rate_pos (by omega)) tendsto_id)

/-- The jump chain runs until at most one root is left. -/
private theorem absorb_tendsto {F : ClusterFamily L} (hF : IsForest F) (G : ClusterFamily L) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (tavareCoeff (deathRank F) 1 1 * mergeCount (deathRank F - 1) F G)) := by
  simp_rw [kingmanTransition_eq_sum_Icc hF, pathWeight, spectralMix]
  let k := deathRank F
  have hk : 1 ≤ k := le_max_right ..
  have H := tendsto_finsetSum (Icc 1 k) fun j hj =>
    (tendsto_finsetSum (Icc j k) fun m hm =>
      (absorb_tendsto_exp m ((mem_Icc.1 hj).1.trans (mem_Icc.1 hm).1)).mul_const
        (tavareCoeff k j m)).mul_const (mergeCount (k-j) F G)
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_Icc, hk, and_true] at H
  rw [sum_eq_single_of_mem 1 (mem_Icc.2 ⟨le_rfl, hk⟩) (by grind)] at H
  exact H

theorem kingmanAbsorption_apply {F : ClusterFamily L} (hF : IsForest F) (G : ClusterFamily L) :
    kingmanAbsorption F G = tavareCoeff (deathRank F) 1 1 * mergeCount (deathRank F - 1) F G :=
  (absorb_tendsto hF G).limUnder_eq

theorem tendsto_kingmanTransition {F : ClusterFamily L} (hF : IsForest F) (G : ClusterFamily L) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) :=
  kingmanAbsorption_apply hF G ▸ absorb_tendsto hF G

theorem kingmanAbsorption_nonneg {F : ClusterFamily L} (hF : IsForest F) (G : ClusterFamily L) :
    0 ≤ kingmanAbsorption F G :=
  ge_of_tendsto (tendsto_kingmanTransition hF G)
    ((eventually_ge_atTop 0).mono fun _ ht => kingmanTransition_nonneg ht _ _)

theorem kingmanAbsorption_sum {F : ClusterFamily L} (hF : IsForest F) :
    ∑ G, kingmanAbsorption F G = 1 := by
  have H := tendsto_finsetSum univ fun G _ => tendsto_kingmanTransition hF G
  simp_rw [kingmanTransition_sum hF] at H
  exact tendsto_nhds_unique H tendsto_const_nhds

theorem kingmanTransition_mul_kingmanAbsorption {F : ClusterFamily L} (hF : IsForest F)
    (t : ℝ) (G : ClusterFamily L) :
    ∑ F', kingmanTransition t F F' * kingmanAbsorption F' G = kingmanAbsorption F G := by
  have H := (tendsto_kingmanTransition hF G).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  simp only [Function.comp_def, id_eq, kingmanTransition_add, Matrix.mul_apply] at H
  refine tendsto_nhds_unique (tendsto_finsetSum univ fun F' _ => ?_) H
  by_cases h : kingmanTransition t F F' = 0
  · simpa only [h, zero_mul] using tendsto_const_nhds
  · exact (tendsto_kingmanTransition (kingmanTransition_support hF h).1 G).const_mul _

end ADR11
