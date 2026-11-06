module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityAction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityMoments
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityBand
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsActual
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Uniform velocity occupation and quadratic moment

This is the source node `l:timed-entrance#integrated-velocity` for smooth autonomous
coefficients. The band test is the literal bounded Borel indicator under the actual semigroup.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory
open Filter SectionTwo
open scoped ENNReal

/- Source occupation bound for any realizing full-space evolution. -/
theorem velocity_occupation_and_moment
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (r T : ℝ) (z : Z),
      0 < r → 0 < T →
      let E := fullSpaceEvolution hH hLE hlam hLam A
      (∫ t in Ioc 0 T, velocityBandAction E r t z) ≤ C * r * Real.sqrt T ∧
        (∫ w, (w.2 - z.2) ^ 2 ∂kernelXV E (Real.toNNReal T) z) ≤ 2 * Lam * T := by
  refine ⟨64 * Real.sqrt (2 * Lam) / lam, ?_, ?_⟩
  · have hLp : 0 < Lam := hlam.trans_le hLam
    positivity
  · intro A r T z hr hT
    let E := fullSpaceEvolution hH hLE hlam hLam A
    have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
    have _h_inl_13 : (∫ t in Ioc 0 T, velocityBandAction E r t z) ≤ (64 * Real.sqrt (2 * Lam) / lam) * r * Real.sqrt T := by
      have hLn := hlam.le.trans hLam
      have h := velocityGreenRaw_band_mass_le hH hlam hLam A E hE hr hT z
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rw [ENNReal.toReal_ofReal (by positivity)] at hb
      have ha : (∫ t in Ioc 0 T, velocityBandAction E r t z) =
          (∫ t in Ioc 0 T, (velocityBandProbability E r z t).toReal) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => velocityBandAction_eq_probability A E hE r t z
      have _h_xinl_0 : (∫ t in Ioc 0 T, (velocityBandProbability E r z t).toReal) =
          (velocityGreenRaw E T hT z (velocityRawBand r)).toReal := by
        rw [integral_Ioc_eq_integral_Ioo, integral_toReal
          (velocityBandProbability_measurable E r z).aemeasurable]
        · rw [velocityGreenRaw_band_eq_lintegral E hT r z]
        · exact Eventually.of_forall fun t =>
            (velocityBandProbability_le_one E r z t).trans_lt ENNReal.one_lt_top
      rw [ha, _h_xinl_0]
      apply hb.trans_eq
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Lam)]
      ring
    refine ⟨_h_inl_13, ?_⟩
    have hm : (∫ w, (w.2 - z.2) ^ 2 ∂kernelXV E (Real.toNNReal T) z) ≤ 2 * Lam * ((Real.toNNReal T) : ℝ) := by
      let T := (Real.toNNReal T)
      have h := kernelXV_velocity_2_moment hlam A E hE z T
      have _h_xinl_0 : Integrable (fun w : Z => (w.2 - z.2) ^ 2) (kernelXV E T z) := by
        apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
          (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2 - z.2)))).mp
        exact ne_of_lt ((kernelXV_velocity_2_moment hlam A E hE z T).trans_lt
          ENNReal.ofReal_lt_top)
      rw [← ofReal_integral_eq_lintegral_ofReal
        _h_xinl_0
        (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2 - z.2)))] at h
      have hL := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    simpa only [Real.coe_toNNReal T hT.le] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
