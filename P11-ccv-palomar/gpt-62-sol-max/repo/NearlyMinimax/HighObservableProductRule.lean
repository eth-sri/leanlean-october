module

public import NearlyMinimax.HistoryPriorWeakTransport


@[expose] public section

/-! Actual time-dependent observable product rule under the constructed history prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Differentiation of a time-dependent bounded observable under the actual
positive marked-history law. The prior derivative is proved from its genuine
source polynomial and append generator. -/
theorem historyMarkedPrior_observable_product_rule {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    {G G' : ℝ → HistoryMarked dependent E → ℝ} {M M' : ℝ}
    (hG : BoundedPath (Ioo 0 T) G M) (hG' : BoundedPath (Ioo 0 T) G' M')
    (hGD : ∀ h u, u ∈ Ioo 0 T → HasDerivAt (fun v => G v h) (G' u h) u) :
    HasDerivAt (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a)
      ((∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
        historyMarkedPriorGenerator dependent P.symm Δ t π a (G t)) t := by
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := P.reference_probability
  obtain ⟨hφ, hφ'⟩ := P.density_path_bounds Ioo_subset_Icc_self
  have h1 := hG'.mul hφ
  have h2 := hG.mul hφ'
  have hd := (hG.mul hφ).hasDerivAt_integral (μ := μ) (h1.add h2) (Ioo_mem_nhds ht.1 ht.2)
    (fun u hu h => (hGD h u hu).mul (historyMarkedDensity_hasDerivAt dependent _ u a h))
  have hti := Ioo_subset_Icc_self ht
  have hsecond := historyMarkedDensityDerivative_integral_eq_generator P hti
    (G t) (hG.measurable t) M hG.nonneg (by simpa only [Real.norm_eq_abs] using hG.norm_le t ht)
  rw [← historyMarkedPriorGenerator_eq_reference P hti (G t)] at hsecond
  rw [integral_add (h1.integrable ht) (h2.integrable ht), ← P.integral_eq_density hti (G' t), hsecond] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
  exact P.integral_eq_density (Ioo_subset_Icc_self hu) (G u)

end NearlyMinimax
