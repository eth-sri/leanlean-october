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
theorem historyMarkedPrior_observable_product_rule {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hlabels : DegreeAtMost dependent Δ)
    {T B t : ℝ} (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {a : E → ℝ} (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {G G' : ℝ → HistoryMarked dependent E → ℝ}
    {M M' : ℝ} (hM : 0 ≤ M) (path : BoundedPath (Ioo 0 T) G G' M M') :
    HasDerivAt (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a)
      ((∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
        historyMarkedPriorGenerator Δ t π a (G t)) t := by
  let μ := historyMarkedReference dependent Δ π
  let _  := historyMarkedReference_probability hΔ hlabels π
  have hρ := historyReferenceRho_pos Δ
  have ht' : t ∈ Ioo 0 T := ⟨ht, htT⟩
  have hs u (hu : u ∈ Ioo 0 T) := historyActivity_mono hu.2.le hB hρ.le hsmall
  have dens := historyDensityPath hlabels hρ hB ha habound hsmall Ioo_subset_Icc_self
  have hd := ((path.mul dens).integral_deriv μ (Ioo_mem_nhds ht htT)).2
  rw [integral_add ((path.velocity.mul dens.family).integrable μ ht')
    ((path.family.mul dens.velocity).integrable μ ht')] at hd
  rw [historyMarkedPrior_integral_eq_expectation hlabels ht.le hB π ha habound (hs t ht'),
    historyMarkedPriorGenerator_eq_reference hlabels ht.le hB π ha habound (hs t ht'),
    ← historyMarkedDensityDerivative_integral_eq_generator hΔ hlabels ht.le hB π ha habound
      (hs t ht') (path.family.measurable t) hM (path.family.bound t ht')]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  exact historyMarkedPrior_integral_eq_expectation hlabels hu.1.le hB π ha habound (hs u hu) (G u)

end NearlyMinimax
