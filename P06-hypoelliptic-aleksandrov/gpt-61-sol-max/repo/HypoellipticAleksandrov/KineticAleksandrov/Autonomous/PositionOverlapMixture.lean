module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapHolder
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual densities of finite mixtures of active Green measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point)

/-- Integrating the canonical joint density against a physical starting measure. -/
def positionMixtureDensity
     : Point → ℝ≥0∞ :=
  fun z => ∫⁻ e, positionActiveDensity hH hLE hlam hLam A c e z ∂nu

/-- The actual density of a finite starting mixture is measurable. -/
theorem measurable_positionMixtureDensity
     [SFinite nu] :
    Measurable (positionMixtureDensity hH hLE hlam hLam A c nu) := (measurable_positionActiveDensity hH hLE hlam hLam A c).lintegral_prod_left'

/-- Fubini identifies the actual Green mixture with its integrated joint density. -/
theorem withDensity_positionMixtureDensity (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [SFinite nu] :
    volume.withDensity (positionMixtureDensity hH hLE hlam hLam A c nu) =
      enlargedActiveGreen hH hLE hlam hLam A c nu := by
  have  := density_volume_sigmaFinite
  ext B hB
  change (volume.withDensity (positionMixtureDensity hH hLE hlam hLam A c nu)) B =
    (nu.bind (enlargedActiveGreenKernel hH hLE hlam hLam A c)) B
  rw [withDensity_apply _ hB, Measure.bind_apply hB (Kernel.aemeasurable _)]
  unfold positionMixtureDensity
  rw [← lintegral_lintegral_swap (μ := nu) (ν := volume.restrict B)
    (f := positionActiveDensity hH hLE hlam hLam A c)
    (measurable_positionActiveDensity hH hLE hlam hLam A c).aemeasurable]
  apply lintegral_congr
  intro e
  rw [← withDensity_apply _ hB, withDensity_positionActiveDensity hpush hH hLE hlam hLam]

/-- A positive mixture inherits a uniform pole bound, with its total starting mass. -/
theorem positionPositiveNorm_mixture_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) [IsFiniteMeasure nu] (m : Measure Y) [SFinite m]
    (F : X → Y → ℝ≥0∞) (hF : Measurable (Function.uncurry F))
    (q : ℝ) (hq : 1 < q) (K : ℝ≥0∞)
    (hK : ∀ᵐ x ∂nu, positionPositiveNorm m q (F x) ≤ K) :
    positionPositiveNorm m q (fun y => ∫⁻ x, F x y ∂nu) ≤ nu univ * K := by
  let sharedTerm_9162066f67 := ((nu univ) ^ (q - 1))


  unfold positionPositiveNorm
  apply (ENNReal.rpow_le_rpow (by
      calc
        _ ≤ ∫⁻ y, sharedTerm_9162066f67 * (∫⁻ x, F x y ^ q ∂nu) ∂m := by
          apply lintegral_mono
          intro y
          exact position_integral_rpow_le nu _ (hF.comp (measurable_id.prodMk measurable_const))
            q hq
        _ = sharedTerm_9162066f67 * ∫⁻ x, ∫⁻ y, F x y ^ q ∂m ∂nu := by

          rw [lintegral_const_mul _ (show Measurable (fun y => ∫⁻ x, F x y ^ q ∂nu) from (hF.pow_const q).lintegral_prod_left')]
          exact congrArg (fun t => sharedTerm_9162066f67 * t)
            (lintegral_lintegral_swap (μ := nu) (ν := m)
              (f := fun x y => F x y ^ q) (hF.pow_const q).aemeasurable).symm
        _ ≤ sharedTerm_9162066f67 * (nu univ * K ^ q) := by
          gcongr
          simpa only [lintegral_const, mul_comm] using lintegral_mono_ae (show ∀ᵐ x ∂nu, (∫⁻ y, F x y ^ q ∂m) ≤ K ^ q by
              filter_upwards [hK] with x hx

              simpa only [positionPositiveNorm, ← ENNReal.rpow_mul,
                one_div_mul_cancel (by linarith : q ≠ 0), ENNReal.rpow_one] using (ENNReal.rpow_le_rpow hx (by linarith : 0 ≤ q)))
        _ = (nu univ * K) ^ q := by
          rw [← mul_assoc, position_rpow_sub_one_mul _ q hq.le,
            ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]) (one_div_nonneg.mpr (by linarith))).trans_eq
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith : q ≠ 0), ENNReal.rpow_one]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
