module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureIntegrationByParts
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDegree
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive
import Mathlib.Tactic

/-! # The degree-two stationary adjoint witness from the explicit Kolmogorov Gaussian -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The actual fundamental measure solves the stationary adjoint identity on punctured tests. -/
theorem bellmanFundamentalMeasure_stationary :
    IsBellmanStationaryAdjointPair bellmanFundamentalMeasure bellmanFundamentalMeasure := by
  intro φ hφ hc hs
  let fx  := fun q => q.2 * fderiv ℝ φ q (1, 0)
  let fv  := fun q =>
    fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)
  have hcx : HasCompactSupport fx := (hc.fderiv_apply ℝ _).mul_left
  have hcv : HasCompactSupport fv :=
    (hc.fderiv_apply ℝ _).fderiv_apply ℝ _
  have hx : Continuous fx := continuous_snd.mul
    (bellman_contDiff_direction hφ _).continuous
  have hv : Continuous fv :=
    (bellman_contDiff_direction (bellman_contDiff_direction hφ _) _).continuous
  have hsx : tsupport fx ⊆ {q | q ≠ (0, 0)} :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have hsv : tsupport fv ⊆ {q | q ≠ (0, 0)} :=
    (tsupport_fderiv_apply_subset ℝ _).trans
      ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have hiX := bellman_integrable_fundamental_test hx hcx hsx
  have hiV := bellman_integrable_fundamental_test hv hcv hsv
  rw [← integral_add hiX hiV]
  rw [bellmanFundamentalMeasure_integral_test (f := fun q => fx q + fv q) (hx.add hv) (hcx.add hcv)
    ((tsupport_add fx fv).trans (union_subset hsx hsv))]
  have heq (t : BellmanPositiveTime) (q : ℝ × ℝ) :
      -q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) +
        fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1) =
      bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q := by
    rw [bellmanGaussianKernel_fderiv_position, bellmanGaussianKernel_fderiv_velocity_twice]
    dsimp [bellmanGaussianTimeCoefficient]
    ring
  change (∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ, bellmanGaussianKernel t q *
    (q.2 * fderiv ℝ φ q _ +
      fderiv ℝ _ q _))
    ∂bellmanPositiveTimeVolume) = 0
  simp_rw [bellmanGaussianKernel_integral_generator _ φ hφ hc, heq]
  exact bellmanGaussianTimeDerivative_integral_test_eq_zero hφ.continuous hc hs

/-- The explicit Gaussian fundamental measure supplies the degree-two witness at every ratio. -/
theorem two_mem_bellmanAdmissibleDegrees (R : ℝ) (hR : 1 ≤ R) :
    (2 : ℝ) ∈ bellmanAdmissibleDegrees R := by
  rw [mem_bellmanAdmissibleDegrees_iff]
  refine ⟨bellmanFundamentalMeasure, bellmanFundamentalMeasure,
    bellmanFundamentalMeasure_radon, bellmanFundamentalMeasure_radon,
    Or.inl bellmanFundamentalMeasure_ne_zero, ?_, ?_,
    bellmanFundamentalMeasure_stationary, bellmanFundamentalMeasure_densityDegree,
    bellmanFundamentalMeasure_densityDegree⟩
  · simp
  · calc
      bellmanFundamentalMeasure = (1 : ENNReal) • bellmanFundamentalMeasure := by simp
      _ ≤ ENNReal.ofReal R • bellmanFundamentalMeasure := by
        gcongr
        simp_all

end HypoellipticAleksandrov.KineticAleksandrov
