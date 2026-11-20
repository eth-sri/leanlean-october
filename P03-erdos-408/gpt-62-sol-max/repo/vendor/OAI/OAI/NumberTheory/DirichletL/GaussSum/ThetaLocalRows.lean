module

public import OAI.NumberTheory.DirichletL.GaussSum.AbelPhaseLimit

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar Filter Asymptotics MeasureTheory
open scoped Topology
open Real Finset Complex
open scoped Classical
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fixed_kernel_eq_dualFixedTerm
    (a b k l : ℤ) (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      fixedDualPhase c y =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) (k,l) := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let y : O := dualFrequencyEquiv (k,l)
  have hnormC : ((‖eisEmbedding y‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  have hreal : Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) =
      (OscSpecial.dualAmp η (a : ℝ) (b : ℝ) (k,l) : ℂ) := by
    rw [hnormC]
    dsimp [OscSpecial.dualAmp, OscSpecial.dualScale, OscSpecial.dualQ]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase : fixedDualPhase c y =
      Complex.exp (Complex.I *
        (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) (k,l) : ℂ)) := by
    have h := breveE_dual_quadratic_real_scale 1 a b k l
    have harg : fixedDualPhase c y =
        Complex.exp (-(2 * Real.pi * Complex.I *
          (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) / (4 : ℂ)) := by
      change ShortDraftTrace.breveE
        (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
          (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
          eisLam / (4 : ℂ)) = _
      simpa using h
    rw [harg]
    congr 1
    dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
    push_cast
    ring
  dsimp only
  rw [hreal, hphase]
  rfl

open Filter

noncomputable def actualVariableDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  ShortDraftTrace.breveE
    (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
      eisLam /
      ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))

noncomputable def actualFixedDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  fixedDualPhase (ActualEisensteinCoordinates.eval a b) y

private theorem dualScale_cast (η a b : ℝ) :
    (OscSpecial.dualScale η a b : ℂ) =
      (η : ℂ) * (OscSpecial.q a b : ℂ) /
        (4 * (OscSpecial.r η a b : ℂ)) := by
  dsimp [OscSpecial.dualScale]
  push_cast
  ring

theorem actual_variable_kernel_eq_dualVarTerm
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
  have hq := osc_q_pos a b hc
  have h := (dual_gaussian_is_actual_trace_phase
    a b z.1 z.2 hc η hη).symm.trans
      (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z)
  unfold actualVariableDualKernel
  rw [dualScale_cast]
  exact h

theorem actual_fixed_kernel_eq_dualFixedTerm_point
    (a b : ℤ) (η : ℝ) (z : ℤ × ℤ) :
    actualFixedDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
  rcases z with ⟨k,l⟩
  exact actual_fixed_kernel_eq_dualFixedTerm a b k l η

theorem actual_dual_phase_error_tendsto_zero
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto
      (fun η : ℝ => η * ‖
        (∑' y : O, actualVariableDualKernel a b η y) -
        (∑' y : O, actualFixedDualKernel a b η y)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hq := osc_q_pos a b hc
  have hbase := OscSpecial.normalized_dual_phase_sum_error_tendsto_zero hq
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  have hvar :
      (∑' y : O, actualVariableDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualVariableDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualVariableDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualVariableDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_variable_kernel_eq_dualVarTerm a b hc η hη z
  have hfixed :
      (∑' y : O, actualFixedDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualFixedDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualFixedDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualFixedDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_fixed_kernel_eq_dualFixedTerm_point a b η z
  rw [hvar, hfixed]

end

section
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_poisson_kernel
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O, actualVariableDualKernel a b η y := by
  dsimp only
  rw [actual_oscillatory_poisson a b hc η hη]
  congr 1
  apply tsum_congr
  intro y
  unfold actualVariableDualKernel
  rw [dualScale_cast]


private theorem actualOriginalAbelDualLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (dualAbelMass a b * fixedDualResidueSum c))) := by
  refine (abel_transfer
    (fun η => 1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ)))
    (fun η => ∑' y : O, actualVariableDualKernel a b η y)
    (fun η => ∑' y : O, actualFixedDualKernel a b η y)
    _ _ (OscSpecial.prefactor_tendsto (osc_q_pos a b hc))
    ?_ (actual_dual_phase_error_tendsto_zero a b hc)).congr' ?_
  · simpa only [actualFixedDualKernel, mul_comm] using variableDualPhase_abel_limit a b hc
  · filter_upwards [self_mem_nhdsWithin] with η hη
    rw [actual_oscillatory_poisson_kernel a b hc η hη]

private theorem full_dual_abel_coefficient (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    ((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) * dualAbelMass a b =
      (((2 / (Real.sqrt 3 * ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖) : ℝ) : ℂ) / 2) := by
  have hn : (‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))
  unfold dualAbelMass
  rw [osc_q_eq_eis_norm_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  push_cast
  field_simp [hn]

theorem quadraticGammaO_eq_fourTerms (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc = breveGaussianFourTerms a b := by
  let c := ActualEisensteinCoordinates.eval a b
  have hEq := tendsto_nhds_unique (original_abel_gamma_limit c hc) (actualOriginalAbelDualLimit a b hc)
  have hn := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
  have hA : (((2 / (Real.sqrt 3 * ‖eisEmbedding c‖) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : 0 < 2 / (Real.sqrt 3 * ‖eisEmbedding c‖)).ne'
  apply mul_left_cancel₀ hA
  simpa only [← mul_assoc, full_dual_abel_coefficient a b hc, div_mul_eq_mul_div,
    mul_div_assoc, fixedDualPhase_four_terms] using hEq

end

end ActualEisensteinCubic

theorem theta_counter_lambda_eq : ActualEisensteinCubic.lambda =
    ActualEisensteinCoordinates.eval (-1) 1 := by
  have homega : ActualEisensteinCubic.omega = ActualEisensteinCoordinates.omega := by
    rfl
  rw [ActualEisensteinCubic.lambda, ActualEisensteinCoordinates.eval, homega]
  ring

open EisensteinEmbedding ConcreteTraceCRT


namespace ShortDraftLocal


end ShortDraftLocal

end

end OAI
