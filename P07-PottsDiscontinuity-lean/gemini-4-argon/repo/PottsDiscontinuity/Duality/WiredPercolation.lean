module

public import PottsDiscontinuity.Duality.ConnectionSymmetry
public import PottsDiscontinuity.Duality.PercolationErgodicity
public import PottsDiscontinuity.Duality.PlanarConnectionAlternative
public import PottsDiscontinuity.Duality.ReverseInfiniteDuality

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial MeasureTheory
open scoped BigOperators
noncomputable section

local instance largeCircuitDualFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) := Fintype.ofFinite _

attribute [local instance] rectangleLabelCutNeighborFintype

private lemma halfBox_outer_isolated (M : ℕ) (σ : RectangleVertex (-(M : ℤ), 0) (2 * M) M → Bool)
    (hbdry : ∀ v : RectangleVertex (-(M : ℤ), 0) (2 * M) M,
      v.1.1 = -(M : ℤ) ∨ v.1.1 = (M : ℤ) ∨ v.1.2 = (M : ℤ) → σ v = false)
    (z : RectangleDualVertex (-(M : ℤ), 0) (2 * M) M)
    (hz : z.1.1 = -(M : ℤ) - 1 ∨ z.1.1 = (M : ℤ) ∨ z.1.2 = (M : ℤ)) :
    (rectangleLabelCutDualGraph (-(M : ℤ), 0) (2 * M) M σ).IsIsolated z := by
  intro y hadj
  obtain ⟨⟨⟨x, y0⟩, axis⟩, hs, ht, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond (-(M : ℤ), 0) (2 * M) M σ z y).1 hadj
  have hs0 := (mem_latticeRectangle (-(M : ℤ), 0) _ (2 * M) M).1 hs
  have ht0 := (mem_latticeRectangle (-(M : ℤ), 0) _ (2 * M) M).1 ht
  cases axis <;> simp only [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
  · have hy0 : y0 = (M : ℤ) := by
      rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        have hx1 := congrArg Prod.fst h1 <;> have hy1 := congrArg Prod.snd h1 <;>
        dsimp at hx1 hy1 <;> omega
    change σ ⟨(x, y0), hs⟩ != σ ⟨(x + 1, y0), ht⟩ at hdiff
    simp [hbdry ⟨(x, y0), hs⟩ (Or.inr (Or.inr hy0)),
      hbdry ⟨(x + 1, y0), ht⟩ (Or.inr (Or.inr hy0))] at hdiff
  · have hx0 : x = -(M : ℤ) ∨ x = (M : ℤ) := by
      rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        have hx1 := congrArg Prod.fst h1 <;> have hy1 := congrArg Prod.snd h1 <;>
        dsimp at hx1 hy1 <;> omega
    change σ ⟨(x, y0), hs⟩ != σ ⟨(x, y0 + 1), ht⟩ at hdiff
    simp [hbdry ⟨(x, y0), hs⟩ (hx0.imp id Or.inl),
      hbdry ⟨(x, y0 + 1), ht⟩ (hx0.imp id Or.inl)] at hdiff

private theorem no_infinite_cluster_implies_opposite_connections (ω : LatticeConfiguration)
    (hno : ω ∉ existsInfiniteCluster) (R : ℕ) :
    ∃ k l : ℕ, R ≤ k ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ connectionEvent ((k : ℤ), -1) (-(l : ℤ) - 1, -1) := by
  classical
  have hUfin : (⋃ r ∈ Finset.range (R + 1), cluster ω ((r : ℤ), 0)).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun r _ =>
      Set.not_infinite.1 fun hinf => hno ⟨((r : ℤ), 0), hinf⟩
  obtain ⟨K, hK⟩ := (hUfin.image fun z : ℤ × ℤ => max z.1.natAbs z.2.natAbs).bddAbove
  let M : ℕ := max K R + 1
  have hRM : R < M := by omega
  let a : LatticeVertex := (-(M : ℤ), 0)
  let W : ℕ := 2 * M
  let H : ℕ := M
  let A := rectangleRestriction a W H ω
  let L : Finset (RectangleVertex a W H) :=
    Finset.univ.filter fun v => 0 ≤ v.1.1 ∧ v.1.1 ≤ (R : ℤ) ∧ v.1.2 = 0
  let σ : RectangleVertex a W H → Bool := actualReachabilityLabel (rectangleGraph a W H) A L
  have hseed (v : RectangleVertex a W H) (hv : 0 ≤ v.1.1 ∧ v.1.1 ≤ (R : ℤ) ∧ v.1.2 = 0) :
      σ v = true :=
    actualReachabilityLabel_eq_true_of_mem _ _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩)
  have hbdry (v : RectangleVertex a W H)
      (hv : v.1.1 = -(M : ℤ) ∨ v.1.1 = (M : ℤ) ∨ v.1.2 = (M : ℤ)) : σ v = false := by
    refine Bool.eq_false_iff.2 fun htrue => ?_
    obtain ⟨u, huL, hconn⟩ := of_decide_eq_true htrue
    obtain ⟨_, hu0, huR, huy⟩ := Finset.mem_filter.1 huL
    have hreach : v.1 ∈ cluster ω ((u.1.1.toNat : ℤ), 0) := by
      rw [← (Prod.ext (Int.toNat_of_nonneg hu0).symm huy : u.1 = ((u.1.1.toNat : ℤ), 0))]
      exact hconn.map (sampledOpenGraphHom (rectangleGraph a W H)
        (frozenEdgeEmbedding (latticeRectangle a W H)) (fun _ => rfl) A ω
        (fun e he => (mem_rectangleRestriction a W H ω e).1 he))
    have hvK : max v.1.1.natAbs v.1.2.natAbs ≤ K :=
      hK ⟨v.1, Set.mem_biUnion (Finset.mem_range.2 (by omega)) hreach, rfl⟩
    have : v.1.1.natAbs < M ∧ v.1.2.natAbs < M := ⟨by omega, by omega⟩
    rcases hv with h | h | h <;> omega
  let B_right := (Finset.Ico (M + R) W).image (rectangleDualBottomPortVertex a W H)
  let B_left := (Finset.range M).image (rectangleDualBottomPortVertex a W H)
  have hdisj : Disjoint B_right B_left := Finset.disjoint_left.2 fun z hzr hzl => by
    rcases Finset.mem_image.1 hzr with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.1 hzl with ⟨j, hj, heq⟩
    have := rectangleDualBottomPortVertex_injOn_range a W H
      (Finset.mem_range.2 (Finset.mem_Ico.1 hi).2)
      (Finset.mem_range.2 (by have := Finset.mem_range.1 hj; dsimp [W]; omega)) heq.symm
    have := Finset.mem_range.1 hj; have := (Finset.mem_Ico.1 hi).1; omega
  have heven (z : RectangleDualVertex a W H) (hzB : z ∉ B_right) (hzT : z ∉ B_left) :
      Even (((rectangleLabelCutDualGraph a W H σ).neighborSet z).ncard) := by
    rcases z with ⟨⟨x, y⟩, hzz⟩
    have hz_exp := (mem_rectangleDualExpanded_iff a W H (x, y)).1 hzz
    dsimp [a, W, H] at hz_exp
    by_cases houter : x = -(M : ℤ) - 1 ∨ x = (M : ℤ) ∨ y = (M : ℤ)
    · rw [SimpleGraph.ncard_neighborSet,
        (halfBox_outer_isolated M σ hbdry ⟨(x, y), hzz⟩ houter).degree_eq_zero]
      exact ⟨0, rfl⟩
    · by_cases hy : y = -1
      · let i := (x + (M : ℤ)).toNat
        have hiW : i < W := by dsimp [i, W]; omega
        have hz_eq : (⟨(x, y), hzz⟩ : RectangleDualVertex a W H) =
            rectangleDualBottomPortVertex a W H i := by
          ext <;> simp [rectangleDualBottomPortVertex, a, W, i, hy, Nat.min_eq_left hiW.le] <;> omega
        have hi_mid : M ≤ i ∧ i < M + R :=
          ⟨by by_contra hlt; exact hzT (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), hz_eq.symm⟩),
           by by_contra hge; exact hzB (Finset.mem_image.2 ⟨i, Finset.mem_Ico.2 ⟨by omega, hiW⟩, hz_eq.symm⟩)⟩
        have h1 : rectangleClampedBottomLabel a W H σ i = true := by
          rw [rectangleClampedBottomLabel_val a W H σ i hiW.le]
          exact hseed _ ⟨by dsimp [a]; omega, by dsimp [a]; omega, rfl⟩
        have h2 : rectangleClampedBottomLabel a W H σ (i + 1) = true := by
          rw [rectangleClampedBottomLabel_val a W H σ (i + 1) hiW]
          exact hseed _ ⟨by dsimp [a]; omega, by dsimp [a]; omega, rfl⟩
        rw [SimpleGraph.ncard_neighborSet, hz_eq, rectangleDualBottomPort_degree a W H σ i hiW, h1, h2]
        exact ⟨0, rfl⟩
      · have hpar := rectangleLabelCutDual_interior_degree_even a W H σ x y
          (by dsimp [a]; omega) (by dsimp [a, W]; omega) (by dsimp [a]; omega) (by dsimp [a, H]; omega)
        rwa [← SimpleGraph.ncard_neighborSet] at hpar
  have hodd : Odd (∑ z ∈ B_right, ((rectangleLabelCutDualGraph a W H σ).neighborSet z).ncard) := by
    simp_rw [SimpleGraph.ncard_neighborSet]
    rw [Finset.sum_image ((rectangleDualBottomPortVertex_injOn_range a W H).mono fun i hi =>
        Finset.mem_range.2 (Finset.mem_Ico.1 hi).2),
      Finset.sum_congr rfl fun i hi => rectangleDualBottomPort_degree a W H σ i (Finset.mem_Ico.1 hi).2,
      Finset.sum_Ico_eq_sum_range, show W - (M + R) = M - R by dsimp [W]; omega]
    let f (j : ℕ) := rectangleClampedBottomLabel a W H σ (M + R + j)
    change Odd (∑ j ∈ Finset.range (M - R), if f j != f (j + 1) then 1 else 0)
    rw [rectangleBoolFlipCount_odd_iff]
    have hf0 : f 0 = true := by
      dsimp [f]
      rw [rectangleClampedBottomLabel_val a W H σ (M + R) (by dsimp [W]; omega)]
      exact hseed _ ⟨by dsimp [a]; omega, by dsimp [a]; omega, rfl⟩
    have hf1 : f (M - R) = false := by
      dsimp [f]
      rw [show M + R + (M - R) = W by dsimp [W]; omega, rectangleClampedBottomLabel_val a W H σ W le_rfl]
      exact hbdry _ (Or.inr (Or.inl (by dsimp [a, W]; omega)))
    simp [hf0, hf1]
  obtain ⟨b, hb, w, hw, hreach⟩ :=
    @exists_reachable_between_of_odd_ncard_neighbor_sum
      (RectangleDualVertex a W H) (largeCircuitDualFintype a W H)
      (rectangleLabelCutDualGraph a W H σ) (Classical.decEq _) (Classical.decRel _)
      B_right B_left hdisj heven hodd
  rcases Finset.mem_image.1 hb with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.1 hw with ⟨j, hj, rfl⟩
  have hi_Ico := Finset.mem_Ico.1 hi
  have hj_lt := Finset.mem_range.1 hj
  have hconn := (actualConnected_mono (rectangleLabelCutDualConfiguration_subset_actualDual a W H A σ
    (rectangle_labelCutEdge_closed_of_actualReachability a W H A L)) hreach).map
    (sampledOpenGraphHom (rectangleDualGraph a W H) (rectangleDualEdgeToSquareEdge a W H)
      (fun _ => rfl) (rectanglePrimalDualConfigurationEquiv a W H A)
      (wholePlaneDualConfigurationHomeomorph ω) fun e he => by
        rw [dual_rectangleRestriction_at a W H ω e, decide_eq_true_eq]; exact he)
  refine ⟨i - M, M - 1 - j, by omega, ?_⟩
  have hb_val : (rectangleDualBottomPortVertex a W H i).1 = (((i - M : ℕ) : ℤ), -1) := by
    rw [rectangleDualBottomPort_val_of_lt a W H i hi_Ico.2]; ext <;> dsimp [a] <;> omega
  have hw_val : (rectangleDualBottomPortVertex a W H j).1 = (-((M - 1 - j : ℕ) : ℤ) - 1, -1) := by
    rw [rectangleDualBottomPort_val_of_lt a W H j (by dsimp [W]; omega)]; ext <;> dsimp [a] <;> omega
  change (rcInfiniteOpenGraph (wholePlaneDualConfigurationHomeomorph ω)).Reachable _ _
  rwa [← hb_val, ← hw_val]

private def oppositeConnectionEvent (t : ℕ × ℕ) : Set LatticeConfiguration :=
  connectionEvent ((t.1 : ℤ), -1) (-(t.2 : ℤ) - 1, -1)

private theorem free_ae_finite_oppositeConnections (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    ∀ᵐ ω ∂μ, {t : ℕ × ℕ | ω ∈ oppositeConnectionEvent t}.Finite := by
  have := hμ.1
  have hnat : Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.2 (neg_neg_of_pos hc)
  have hmajor := (hnat.mul_of_nonneg hnat (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).mul_left C
  refine ae_finite_setOfPred_mem (ne_top_of_le_ne_top hmajor.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum fun t => ?_))
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  let u : LatticeVertex := ((t.1 : ℤ), -1)
  let w : LatticeVertex := (-(t.2 : ℤ) - 1, -1)
  have ht := free_connection_translate θ μ hμ u 0 (w - u)
  simp only [zero_add, sub_add_cancel] at ht
  rw [show (μ (oppositeConnectionEvent t)).toReal = twoPoint μ (w - u) from congrArg ENNReal.toReal ht]
  refine (hdecay (w - u)).trans ?_
  have hd : (t.1 : ℝ) + (t.2 : ℝ) ≤ |((w - u).1 : ℝ)| + |((w - u).2 : ℝ)| := by
    exact_mod_cast (show (t.1 : ℤ) + (t.2 : ℤ) ≤ |(w - u).1| + |(w - u).2| by
      dsimp [u, w]; simp only [abs_eq_max_neg]; omega)
  rw [← Real.exp_add]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (by nlinarith only [mul_le_mul_of_nonneg_left hd hc.le])) hC

theorem wired_ae_existsInfiniteCluster_of_free_decay (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    ∀ᵐ ω ∂μ₁, ω ∈ existsInfiniteCluster := by
  have hfree := free_ae_finite_oppositeConnections θ μ₀ hμ₀ C c hC hc hdecay
  rw [← wired_map_dual_eq_free θ μ₀ μ₁ hμ₀ hμ₁] at hfree
  filter_upwards [ae_of_ae_map wholePlaneDualConfigurationHomeomorph_measurable.aemeasurable hfree]
    with ω hω
  by_contra hn
  obtain ⟨k, l, hk, hconn⟩ :=
    no_infinite_cluster_implies_opposite_connections ω hn (hω.toFinset.sup Prod.fst + 1)
  have := Finset.le_sup (f := Prod.fst) ((hω.mem_toFinset (a := (k, l))).2 hconn)
  omega

theorem wired_existsInfiniteCluster_eq_one_of_free_decay (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    μ₁ existsInfiniteCluster = 1 := by
  have := hμ₁.1
  have hz : μ₁ (existsInfiniteCluster)ᶜ = 0 :=
    ae_iff.1 (wired_ae_existsInfiniteCluster_of_free_decay θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay)
  have hmeas : MeasurableSet existsInfiniteCluster := RCInfinite.measurableSet_infiniteClusterEvent
  simpa only [hz, add_zero, measure_univ] using measure_add_measure_compl (μ := μ₁) hmeas

theorem wired_origin_pos_of_free_exponential_decay (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ∀ x : LatticeVertex, twoPoint μ₀ x ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    0 < μ₁ (infiniteClusterAt 0) :=
  (existsInfiniteCluster_pos_iff_origin_pos (dualParameters θ) 1 μ₁ hμ₁).1
    ((wired_existsInfiniteCluster_eq_one_of_free_decay θ μ₀ μ₁ hμ₀ hμ₁ C c hC hc hdecay).symm ▸
      zero_lt_one)

end
end PottsDiscontinuity.Duality
