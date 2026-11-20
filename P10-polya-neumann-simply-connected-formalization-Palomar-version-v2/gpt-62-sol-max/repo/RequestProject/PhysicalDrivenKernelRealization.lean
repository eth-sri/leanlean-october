module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.PhysicalVolterraNormalization

/-!
# Hardy input from the driven observation kernel

The periodic zeroth gauge of an L² driven vector gives the regular Hardy
input, with the ordinary `sqrt(2π)` Fourier scale and nonpositive support.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate

/-- The actual continuous circle representative of the zeroth driven
gauge. Its matching endpoint values come from the true observation kernel. -/
def physicalDrivenKernelCircleGauge
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hO : observationAdj W g = 0) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨AddCircle.liftIco (2 * Real.pi) 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) 0), by
    obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO 0
    exact AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
      (physicalDrivenGauge_continuousOn γ hγ E _
        (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) 0)⟩

theorem physicalDrivenKernelCircleGauge_fourierCoeff
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    (hO : observationAdj W g = 0) :
    fourierCoeff (physicalDrivenKernelCircleGauge γ hγ E hW g hg hO) =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) :=
  fourierCoeff_eq_on_circle _

section

variable {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0)
include hγLip hγ hW g hg hO

/-- The genuine normalized Hardy input of the driven kernel. The
ordinary averaged coefficient is multiplied by sqrt(2π) sqrt(λ_n). -/
def physicalDrivenKernelInput : L2Z :=
  (Real.sqrt (2 * Real.pi) : ℂ) • sobVec (1 / 2 : ℝ)
    (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0))
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_half hγLip hγ hW g hg hO)

theorem physicalDrivenKernelInput_apply (n : ℤ) :
    physicalDrivenKernelInput hγLip hγ hW g hg hO n =
      (Real.sqrt (2 * Real.pi) : ℂ) * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) n := by
  simp  [physicalDrivenKernelInput, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    sobVec_apply, mul_assoc]

theorem fromL2_physicalDrivenKernelInput :
    fromL2 (1 / 2 : ℝ) (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      (Real.sqrt (2 * Real.pi) : ℂ) •
        fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) := by
  rw [physicalDrivenKernelInput, fromL2_smul, fromL2_sobVec]

/-- The normalized input has the actual extra half order supplied by
the forced zeroth-row equation, without a regularity premise on g's kernel. -/
theorem fromL2_physicalDrivenKernelInput_isSobolevSeq_one :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ)
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) := by
  rw [fromL2_physicalDrivenKernelInput]
  exact isSobolevSeq_smul _
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)

theorem normalizedHardyAverage_physicalDrivenKernelInput :
    normalizedHardyAverage (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
      fromL2 (1 / 2 : ℝ) (physicalDrivenKernelInput hγLip hγ hW g hg hO) = _
  rw [fromL2_physicalDrivenKernelInput, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The initial Hardy value reconstructed from the derived coefficients
is the actual continuous driven zeroth gauge at every parameter. -/
theorem hardyFourierTrace_physicalDrivenKernelInput (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) θ =
      physicalDrivenPeriodicGauge γ E W g 0 θ := by
  let H := physicalDrivenKernelCircleGauge γ hγ.continuous E hW.1 g
    (intervalIntegrable_boundary_of_memLp g hg) hO
  have hcoef : fourierCoeff H =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) :=
    physicalDrivenKernelCircleGauge_fourierCoeff _ _ _ _ _ _ _
  have hsum : Summable (fun n => ‖fourierCoeff H n‖) := by
    rw [hcoef]
    exact (sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa using physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)).1
  rw [normalizedHardyAverage_physicalDrivenKernelInput, ← hcoef]
  exact hardyFourierTrace_fourierCoeff H hsum θ

end

/-- The input reconstructed from the driven gauge belongs to the full nonpositive sector. -/
theorem physicalDrivenKernelInput_nonpositive {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {L : NNReal} (hLip : LipschitzWith L (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E W) (g : BoundaryL2)
    (hO : observationAdj W (g : ℝ → ℂ) = 0) :
    IsNonpositiveFourierSupport (physicalDrivenKernelInput hLip
      (contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F (coords.smooth.of_le (by simp)))
      hW g (Lp.memLp g) hO) := by
  have h := localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable
    coords hLip hE hW g (intervalIntegrable_boundaryL2 g) hO 0
  intro n hn'
  rw [physicalDrivenKernelInput_apply, h n hn', mul_zero]

end PolyaNeumann

end
