module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1InversionReal
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupport
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Compact position support and its raw volume for the single real inverse -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo


variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B) (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R) (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})

/-- The Euclidean cone is contained in a compact coordinate ball of radius `R³`. -/
theorem ballExit_ae_position_bound

    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    ∀ᵐ p ∂ballExit hH hLE hd hlam hLam B hB v₀ hR P T, ‖p.1‖ ≤ R ^ 3 := by
  filter_upwards [ballExit_cone hH hLE hd hlam hLam B hB v₀ hR P T] with p hp

  have hcone := (PDE.norm_le_vecEuclideanNorm p.1).trans hp.2.2


  exact hcone.trans ((mul_le_mul_of_nonneg_left (show p.2.1 - P.1.time ≤ R ^ 2 / 8 by linarith only [hp.2.1, hT]) hR.le).trans (show _ by
      have hnn := pow_nonneg hR.le 3
      nlinarith))

/-- The smooth real inverse vanishes everywhere outside the compact reached-position ball. -/
theorem ballExitL1Density_zero_outside

    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    ∀ y : PDE.Vec d, R ^ 3 < ‖y‖ →
      exitL1Density (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) y = 0 := by
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T


  have hU : IsOpen (show PDE.VelocityRegion d from {y | R ^ 3 < ‖y‖}) := isOpen_lt continuous_const continuous_norm

  have hs := ballExit_ae_position_bound hH hLE hd hlam hLam B hB v₀ hR P T hT
  rw [ballExit_eq_withDensity_exitJointDensity hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT, ae_withDensity_iff (measurable_exitJointDensity ν).ennreal_ofReal] at hs




  have hcont := (ballExitL1Density_contDiff hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT).continuous
  exact fun y hy => Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr (by
      filter_upwards [(Measure.ae_ae_of_ae_prod hs)] with y hy
      intro hyU
      apply Lp.ext
      filter_upwards [ballExitL1Density_coe hH hLE hd hlam hLam B hB v₀ hR P T hv hT y,
        hy, (ballExitPositionKernel_density hH hLE hd hlam hLam B hB v₀ hR P T hv hT), Lp.coeFn_zero (E := ℂ) (p := 1) (μ := exitMarginal ν)]
        with z hz hzs hzn hz0
      have hg : exitJointDensity ν (y, z) = 0 := by


        exact le_antisymm (by
            apply ENNReal.ofReal_eq_zero.mp
            by_contra hne
            exact (not_le_of_gt hyU) (hzs hne)) (hzn.2 y)
      rw [hz, hg, Complex.ofReal_zero, hz0]
      rfl)) hU hcont.continuousOn continuousOn_const hy

variable {d : ℕ}

/-- The support bounding ball has the required raw `R^(3d)` volume. -/
theorem exitPositionBoundingBall_volume  {R : ℝ} (hR : 0 < R) :
    (volume : Measure (PDE.Vec d)) (Metric.closedBall 0 (R ^ 3)) =
      ENNReal.ofReal ((2 : ℝ) ^ d * R ^ (3 * d)) := by
  rw [Real.volume_pi_closedBall _ (pow_pos hR 3).le, Fintype.card_fin,
    mul_pow, ← pow_mul]

variable {E : Type*}

/-- Every derivative of a compactly supported position function has the same support bound. -/
theorem exitDerivative_zero_outside   [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : PDE.Vec d → E) (r : ℝ)
    (hzero : ∀ y, r < ‖y‖ → G y = 0) (j : ℕ) :
    ∀ y, r < ‖y‖ → iteratedFDeriv ℝ j G y = 0 := by


  intro y hy
  apply Function.notMem_support.mp
  intro hmem
  have hm := (closure_minimal (show _ by
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h
      exact hy (hzero y (lt_of_not_ge h))) Metric.isClosed_closedBall) (support_iteratedFDeriv_subset j hmem)
  rw [Metric.mem_closedBall, dist_zero_right] at hm
  exact (not_le_of_gt hy) hm

/-- Raw support volume bounds the integral of any globally bounded derivative. -/
theorem exitDerivative_integral_le_volume   [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : PDE.Vec d → E) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ y, R ^ 3 < ‖y‖ → G y = 0) (j : ℕ) {M : ℝ}
    (_hM : 0 ≤ M) (hbound : ∀ y, ‖iteratedFDeriv ℝ j G y‖ ≤ M) :
    (∫ y, ‖iteratedFDeriv ℝ j G y‖) ≤ ((2 : ℝ) ^ d * R ^ (3 * d)) * M := by
  have hz := exitDerivative_zero_outside G (R ^ 3) hzero j
  have he : (∫ y in Metric.closedBall 0 (R ^ 3), ‖iteratedFDeriv ℝ j G y‖) =
      ∫ y, ‖iteratedFDeriv ℝ j G y‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      simp_all)
  have hf : (volume : Measure (PDE.Vec d)) (Metric.closedBall 0 (R ^ 3)) < ⊤ :=
    (isCompact_closedBall (0 : PDE.Vec d) (R ^ 3)).measure_lt_top

  have hb := norm_setIntegral_le_of_norm_le_const
    (f := fun y => ‖iteratedFDeriv ℝ j G y‖) hf (fun y _hy =>
    by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound y)
  have hvr : (volume : Measure (PDE.Vec d)).real (Metric.closedBall 0 (R ^ 3)) =
      (2 : ℝ) ^ d * R ^ (3 * d) := by
    rw [Measure.real, (exitPositionBoundingBall_volume (d := d) hR), ENNReal.toReal_ofReal (by positivity)]
  rw [he, hvr, Real.norm_eq_abs] at hb
  exact ((le_abs_self _).trans hb).trans_eq (mul_comm _ _)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
