module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov

/-!
# Endpoint-safe reverse-time Steklov convergence

This module upgrades the strict-interior Steklov convergence theorem to the
whole closed time interval.  The proof uses the zero extension only inside
ordinary Lebesgue integrals, so no endpoint values are interpreted as traces.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem endpoint_ae_mem_Ioo_on_Icc (T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), t ∈ Ioo 0 T := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [Ioo_ae_eq_Icc (μ := volume)] with t ht
  exact ht.mpr

/-- Forward Steklov averages converge strongly in Bochner `L²` on the full
closed reverse-time interval; endpoint values are measure-null. -/
theorem tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (_hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc 0 T,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_forwardSteklov_sqNorm_integral_on T f (Icc 0 T) (endpoint_ae_mem_Ioo_on_Icc T)

/-- Backward Steklov averages converge strongly in Bochner `L²` on the full
closed reverse-time interval; endpoint values are measure-null. -/
theorem tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (_hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc 0 T,
        ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_backwardSteklov_sqNorm_integral_on T f (Icc 0 T) (endpoint_ae_mem_Ioo_on_Icc T)

end HypoellipticAleksandrov.Parabolic.Dirichlet
