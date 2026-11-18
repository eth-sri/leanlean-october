module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePlaneScaling
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDegree
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A continuous factor times a continuous compactly supported test is integrable. -/
theorem bellman_integrable_mul_test {f g : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun q => f q * g q) :=
  (hf.mul hg).integrable_of_hasCompactSupport hc.mul_left

/-- Integration by parts for smooth functions with a compactly supported right factor. -/
theorem bellman_integral_mul_direction {f g : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (v : ℝ × ℝ) :
    (∫ q, f q * fderiv ℝ g q v) = -(∫ q, fderiv ℝ f q v * g q) := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact bellman_integrable_mul_test (bellman_contDiff_direction hf v).continuous
      hg.continuous hc
  · exact bellman_integrable_mul_test hf.continuous
      (bellman_contDiff_direction hg v).continuous (hc.fderiv_apply ℝ v)
  · exact bellman_integrable_mul_test hf.continuous hg.continuous hc
  · exact fun q _ => hf.differentiable (by simp) q
  · exact fun q _ => hg.differentiable (by simp) q

/-- Spatial transfer of the Kolmogorov generator from the test to the Gaussian. -/
theorem bellmanGaussianKernel_integral_generator (t : BellmanPositiveTime)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (∫ q, bellmanGaussianKernel t q *
      (q.2 * fderiv ℝ φ q (1, 0) +
        fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1))) =
    ∫ q, (-q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) +
      fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1)) *
        φ q := by
  have hk := contDiff_bellmanGaussianKernel t
  have hvφ : ContDiff ℝ (⊤ : ℕ∞) (fun q => q.2 * φ q) :=
    contDiff_snd.mul hφ
  have hd (q : ℝ × ℝ) : fderiv ℝ (fun z => z.2 * φ z) q (1, 0) =
      q.2 * fderiv ℝ φ q (1, 0) := by
    rw [fderiv_fun_mul differentiableAt_snd (hφ.differentiable (by simp) q)]
    simp [fderiv_snd]
  have hx := bellman_integral_mul_direction hk hvφ hc.mul_left (1, 0)
  simp only [hd] at hx
  have hv := bellman_integral_mul_direction hk (bellman_contDiff_direction hφ (0, 1))
    (hc.fderiv_apply ℝ (0, 1)) (0, 1)
  rw [(bellman_integral_mul_direction (bellman_contDiff_direction hk (0, 1)) hφ hc (0, 1)), neg_neg] at hv
  have hiX : Integrable (fun q => bellmanGaussianKernel t q *
      (q.2 * fderiv ℝ φ q (1, 0))) :=
    bellman_integrable_mul_test hk.continuous
      (continuous_snd.mul (bellman_contDiff_direction hφ (1, 0)).continuous)
      (hc.fderiv_apply ℝ (1, 0)).mul_left
  have hjX : Integrable (fun q => -q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) *
      φ q) := bellman_integrable_mul_test
        (continuous_snd.neg.mul (bellman_contDiff_direction hk (1, 0)).continuous)
        hφ.continuous hc
  simp only [mul_add, add_mul]
  rw [integral_add hiX (bellman_integrable_mul_test hk.continuous (bellman_contDiff_direction (bellman_contDiff_direction hφ (0, 1)) (0, 1)).continuous ((hc.fderiv_apply ℝ (0, 1)).fderiv_apply ℝ (0, 1))), integral_add hjX (bellman_integrable_mul_test (bellman_contDiff_direction (bellman_contDiff_direction hk (0, 1)) (0, 1)).continuous hφ.continuous hc), hx, hv]
  congr 1
  rw [← integral_neg]
  congr 1
  funext q
  ring


/-- The actual fundamental measure solves the stationary adjoint identity on punctured tests. -/
theorem bellmanFundamentalMeasure_stationary :
    IsBellmanStationaryAdjointPair bellmanFundamentalMeasure bellmanFundamentalMeasure := by
  intro φ hφ hc hs
  let fx : ℝ × ℝ → ℝ := fun q => q.2 * fderiv ℝ φ q (1, 0)
  let fv : ℝ × ℝ → ℝ := fun q =>
    fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)
  have hcx : HasCompactSupport fx := (hc.fderiv_apply ℝ (1, 0)).mul_left
  have hcv :=
    (hc.fderiv_apply ℝ (0, 1)).fderiv_apply ℝ (0, 1)
  have hx : Continuous fx := continuous_snd.mul
    (bellman_contDiff_direction hφ (1, 0)).continuous
  have hv :=
    (bellman_contDiff_direction (bellman_contDiff_direction hφ (0, 1)) (0, 1)).continuous
  have hsx : tsupport fx ⊆ {q | q ≠ (0, 0)} :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hs)
  have hsv :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
      ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hs)
  rw [← integral_add (bellman_integrable_fundamental_test hx hcx hsx) (bellman_integrable_fundamental_test hv hcv hsv)]
  rw [bellmanFundamentalMeasure_integral_test (f := fun q => fx q + fv q) (hx.add hv) (hcx.add hcv)
    ((tsupport_add fx fv).trans (union_subset hsx hsv))]
  have heq (t : BellmanPositiveTime) (q : ℝ × ℝ) :
      -q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) +
        fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1) =
      bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q := by
    rw [bellmanGaussianKernel_fderiv_position, bellmanGaussianKernel_fderiv_velocity_twice]
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
    ring
  change (∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ, bellmanGaussianKernel t q *
    (q.2 * fderiv ℝ φ q (1, 0) +
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)))
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
        simpa using ENNReal.ofReal_le_ofReal hR

end HypoellipticAleksandrov.KineticAleksandrov

