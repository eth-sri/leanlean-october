module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1Fourier
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Integrability of every Fourier moment of the exit measure -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open MeasureTheory SectionTwo

section
variable {d : ℕ} (hd : 1 ≤ d) (n : ℕ)

include hd
/-- Every polynomial moment of stretched exponential radial decay is integrable. -/
theorem integrable_exitFrequency_moment
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun ξ : PDE.Vec d =>
      ‖ξ‖ ^ n * Real.exp (-c * ‖ξ‖ ^ (1 / 3 : ℝ))) := by
  have : NeZero d := ⟨by omega⟩
  have hdim : Module.finrank ℝ (PDE.Vec d) = d := by
    simpa only [Fintype.card_fin] using
      (Module.finrank_fintype_fun_eq_card ℝ (η := Fin d))
  apply (integrable_fun_norm_addHaar (volume : Measure (PDE.Vec d))
    (f := fun x  => x ^ n * Real.exp (-c * x ^ (1 / 3 : ℝ)))).mpr
  rw [hdim]

  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (show -1 < ((d - 1 + n : ℕ) : ℝ) by

      linarith)
    (by norm_num : (0 : ℝ) < 1 / 3) hc
  refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_natCast, pow_add]
  simp only [smul_eq_mul]
  ring

/-- Rescaling the stretched exponential preserves every polynomial moment. -/
theorem integrable_exitFrequency_scaled_moment
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    Integrable (fun ξ : PDE.Vec d =>
      ‖ξ‖ ^ n * Real.exp (-c * (R ^ 3 * ‖ξ‖) ^ (1 / 3 : ℝ))) := by
  have hi := integrable_exitFrequency_moment hd n (c := c * (R ^ 3) ^ (1 / 3 : ℝ))
    (mul_pos hc (Real.rpow_pos_of_pos (pow_pos hR 3) _))
  convert hi using 1
  funext ξ
  rw [Real.mul_rpow (pow_nonneg hR.le _) (norm_nonneg _)]
  ring_nf
end


/-- The upstream total-variation decay gives every moment in the complete `L¹` space. -/
theorem ballExitL1Fourier_integrable_moments
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (n : ℕ) :
    Integrable (fun ξ => ‖ξ‖ ^ n *
      ‖exitL1Fourier (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) ξ‖) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ :=
    ballExit_fourier_decay hH hLE d hd lam Lam hlam hLam
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T

  apply ((integrable_exitFrequency_scaled_moment hd n hc hR).const_mul C).mono'
    (continuous_norm.pow n |>.mul (continuous_exitL1Fourier ν).norm).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  change ‖‖ξ‖ ^ n * ‖exitL1Fourier ν ξ‖‖ ≤
    C * (‖ξ‖ ^ n * Real.exp (-c * (R ^ 3 * ‖ξ‖) ^ (1 / 3 : ℝ)))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (norm_nonneg _)), norm_exitL1Fourier]




  simpa only [mul_left_comm C] using mul_le_mul_of_nonneg_left ((hdecay B hB v₀ R hR P T hv hT ξ).trans (mul_le_mul_of_nonneg_left (by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hc.le)
      apply Real.rpow_le_rpow (mul_nonneg (pow_nonneg hR.le _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (PDE.norm_le_vecEuclideanNorm ξ) (pow_nonneg hR.le _)) (by norm_num)) hC.le)) (pow_nonneg (norm_nonneg ξ) n)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
