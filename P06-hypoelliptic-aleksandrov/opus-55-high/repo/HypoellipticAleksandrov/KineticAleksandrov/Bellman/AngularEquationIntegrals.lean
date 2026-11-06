module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesRadial
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestSupport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Integrating the actual homogeneous angular representation -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The literal radial integral is the positive Lebesgue integral with s^(3-β). -/
theorem bellmanRadialWeight_integral (β : ℝ) (f : ℝ → ℝ) :
    (∫ s, f s.val ∂bellmanRadialWeight β) =
      ∫ s in Ioi (0 : ℝ), s ^ (3 - β) * f s := by
  have hm : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (3 - β))) := by fun_prop
  rw [bellmanRadialWeight, integral_withDensity_eq_integral_toReal_smul hm]
  · have hw (s : BellmanPositiveTime) :
        (ENNReal.ofReal _).toReal = s.val ^ (3 - β) :=
      ENNReal.toReal_ofReal (Real.rpow_nonneg s.property.le _)
    simp only [hw]
    have hem : MeasurableEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Ioi
    have he := hem.integral_map
      (fun s : ℝ => s ^ (3 - β) * f s) (μ := bellmanPositiveTimeVolume)
    rw [map_bellmanPositiveTimeVolume_coe] at he
    simp_all
  simp

/-- A test supported in positive position integrates against precisely that restriction. -/
theorem bellman_integral_positive_restrict (μ : Measure BellmanPuncturedPlane)
    (f : ℝ × ℝ → ℝ) (hs : tsupport f ⊆ {q : ℝ × ℝ | 0 < q.1}) :
    (∫ q, f q.val ∂μ.restrict {q | 0 < q.val.1}) = ∫ q, f q.val ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  apply image_eq_zero_of_notMem_tsupport
  grind

end HypoellipticAleksandrov.KineticAleksandrov
