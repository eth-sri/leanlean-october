module
public import AnalyticESC.Dimension.NaturalMeasure

@[expose] public section
namespace AnalyticESC
open Set Metric Filter Topology MeasureTheory

noncomputable abbrev cell (r : ℝ) (k : ℤ) := Ico (k * r) ((k+1)*r)
noncomputable abbrev grid (μ : Measure ℝ) (q r : ℝ) (k : ℤ) := μ.real (cell r k) ^ q
noncomputable def lqSum (μ : Measure ℝ) (q r : ℝ) := ∑' k, grid μ q r k
section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {q r : ℝ}

private lemma grid_sum (hq : 1 ≤ q) : Summable (grid μ q r) ∧ lqSum μ q r ∈ Icc 0 1 := by
  have hd : Pairwise (Function.onFun Disjoint (cell r)) := by simpa  using pairwise_disjoint_Ico_zsmul r
  have H (S : Finset ℤ) : ∑ k ∈ S, grid μ q r k ≤ 1 := by
    apply (Finset.sum_le_sum fun k _ => Real.rpow_le_self_of_le_one (by positivity) measureReal_le_one hq).trans
    rw [←measureReal_biUnion_finset  (hd.set_pairwise S) (fun _ _ => measurableSet_Ico)]; exact measureReal_le_one
  have pos (k : ℤ) : 0 ≤ grid μ q r k := Real.rpow_nonneg measureReal_nonneg _
  have hs := summable_of_sum_le pos H
  exact ⟨hs,tsum_nonneg pos,hs.tsum_le_of_sum_le H⟩

/-- The contribution of one cell suffices for an upper bound on the spectrum,
since `log r < 0`. -/
private lemma spectrum {d} (hm : ∀ r : Scale, 0 < μ.real (cell r 0))
    (hd : RatioLimit (fun r => μ.real (cell r 0)) d) (hq : 1 ≤ q) :
    liminf (fun r : Scale => logRatio (lqSum μ q r) r) scaleZero ≤ q*d := by
  have : scaleZero.NeBot := (map_neBot_iff (fun r : Scale => (r:ℝ))).mp (scale_map ▸ inferInstanceAs (𝓝[>] 0).NeBot)
  have h (r : Scale) : logRatio (lqSum μ q r) r ∈ Icc 0 (q*logRatio (μ.real (cell r 0)) r) := by
    obtain ⟨hs,l,u⟩ := grid_sum  μ hq
    have e := Real.log_le_log (Real.rpow_pos_of_pos (hm r) q) (hs.le_tsum 0 fun _ _ => Real.rpow_nonneg measureReal_nonneg q)
    rw [Real.log_rpow (hm r)] at e
    have neg := (Real.log_neg r.2.1 r.2.2).le
    exact ⟨div_nonneg_of_nonpos (Real.log_nonpos l u) neg,by simp only [logRatio,divide,←mul_div_assoc]; exact div_le_div_of_nonpos_of_le neg e⟩
  have H := hd.const_mul q
  rw [← H.liminf_eq]; exact liminf_le_liminf (.of_forall fun r => (h r).2)
    (isBoundedUnder_of_eventually_ge (.of_forall fun r => (h r).1)) H.isCoboundedUnder_ge

end

lemma example_lq {s ν} [IsProbabilityMeasure ν] (h : exampleIFS.Gibbs s ν) {q : ℝ} (hq : 1 < q) (hne : q-1 ≠ 0) :
    let D := Challenge.lqDim (exampleIFS.natural ν) q hne
    D ≤ q/(q-1)*(s-1/3) ∧ (3*s < q → D < s) := by
  obtain ⟨pos,lim⟩ := edge_mass h (S := fun r => cell r 0) (fun _ => measurableSet_Ico)
    (by grind) (by grind)
  have e := spectrum _ pos lim hq.le
  have bound : Challenge.lqDim (exampleIFS.natural ν) q hne ≤ q/(q-1)*(s-1/3) := by
    unfold Challenge.lqDim divide; rw [div_mul_eq_mul_div]; bound
  refine ⟨bound,fun hl => bound.trans_lt ?_⟩
  rw [div_mul_eq_mul_div,div_lt_iff₀ (sub_pos.mpr hq)]; linarith

end AnalyticESC
