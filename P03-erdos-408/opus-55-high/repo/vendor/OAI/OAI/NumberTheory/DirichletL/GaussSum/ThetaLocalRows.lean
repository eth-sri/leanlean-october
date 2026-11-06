module

public import OAI.NumberTheory.DirichletL.GaussSum.AbelPhaseLimit

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open Real
open Finset Complex
open Filter Real Asymptotics
open Filter
open ShortDraftLatticeCount
open Filter
open scoped Topology

namespace ActualEisensteinCubic

section

open ConcreteTraceCRT

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

open scoped Topology
open Filter

def actualVariableDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  ShortDraftTrace.breveE
    (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
      eisLam /
      ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))

def actualFixedDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  fixedDualPhase (ActualEisensteinCoordinates.eval a b) y

private theorem dualScale_cast (η a b : ℝ) :
    (OscSpecial.dualScale η a b : ℂ) =
      (η : ℂ) * (OscSpecial.q a b : ℂ) /
        (4 * (OscSpecial.r η a b : ℂ)) := by
  dsimp [OscSpecial.dualScale]
  simp

theorem actual_variable_kernel_eq_dualVarTerm
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      linarith)
  have h := (dual_gaussian_is_actual_trace_phase
    a b z.1 z.2 hc η hη).symm.trans
      (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z)
  unfold actualVariableDualKernel
  rw [dualScale_cast]
  omega

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
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      linarith)
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
  simp_all

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualFixedAbelLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by simp)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' y : O, actualFixedDualKernel a b η y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r))) := by
  simpa only [actualFixedDualKernel, mul_comm] using
    variableDualPhase_abel_limit a b hc

end

section

open ConcreteTraceCRT

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

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualVariableAbelLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by simp)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      ((1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ))) *
        (∑' y : O, actualVariableDualKernel a b η y)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      linarith)
  exact abel_transfer
    (fun η => 1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ)))
    (fun η => ∑' y : O, actualVariableDualKernel a b η y)
    (fun η => ∑' y : O, actualFixedDualKernel a b η y)
    _ _ (OscSpecial.prefactor_tendsto hq)
    (actualFixedAbelLimit a b hc)
    (actual_dual_phase_error_tendsto_zero a b hc)

theorem actualOriginalAbelDualLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by simp)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  apply (actualVariableAbelLimit a b hc).congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  rw [actual_oscillatory_poisson_kernel a b hc η hη]

end

section

theorem dual_abel_coefficient (a b : ℤ)
    (hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ)) :
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
      ((2 / (Real.sqrt 3 *
        (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)) =
      ((2 / (Real.sqrt 3 * OscSpecial.q (a : ℝ) (b : ℝ)) : ℝ) : ℂ) := by
  dsimp only
  rw [two_coordinate_norm_four]
  have hqC : (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity)
  push_cast
  ring

theorem full_dual_abel_coefficient (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) *
        ((2 / (Real.sqrt 3 *
          (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ))) =
      (((2 / (Real.sqrt 3 * ‖ConcreteTraceCRT.eisEmbedding c‖) : ℝ) : ℂ) / 2) := by
  dsimp only
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by linarith)
  rw [dual_abel_coefficient a b hq]
  have hqnorm := osc_q_eq_eis_norm_sq a b
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) =
      ‖ConcreteTraceCRT.eisEmbedding
        (ActualEisensteinCoordinates.eval a b)‖ := by
    rw [hqnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt, hqnorm]
  have hn : (‖ConcreteTraceCRT.eisEmbedding
      (ActualEisensteinCoordinates.eval a b)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (by grind)
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity)
  push_cast
  grind

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem quadraticGammaO_eq_fourTerms (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      breveGaussianFourTerms a b := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let n : ℝ := ‖eisEmbedding c‖
  let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by simp)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let S : ℂ := ∑ r : O ⧸ Ideal.span {(2 : O)},
    fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hEq0 := tendsto_nhds_unique
    (original_abel_gamma_limit c hc)
    (actualOriginalAbelDualLimit a b hc)
  have hEq : (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc) =
      (((Real.sqrt q / 2 : ℝ) : ℂ) *
        ((((4 / q : ℝ) : ℂ) * L2) * S)) := by
    simpa only [c, n, q, a2, b2, L2, S, mul_assoc] using hEq0
  have hC : (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) * L2)) =
      (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) := by
    simpa only [c, n, q, a2, b2, L2] using
      full_dual_abel_coefficient a b hc
  have hA : ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) ≠ 0 := by
    have hn : 0 < n := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    have hs : 0 < Real.sqrt 3 := by positivity
    exact_mod_cast (by positivity)
  have hG : quadraticGammaO c hc = S / 2 := by
    apply mul_left_cancel₀ hA
    calc
      ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc =
          ((Real.sqrt q / 2 : ℝ) : ℂ) *
            ((((4 / q : ℝ) : ℂ) * L2) * S) := hEq
      _ = (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) * S := by grind
      _ = ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * (S / 2) := by ring
  change quadraticGammaO c hc = breveGaussianFourTerms a b
  calc
    quadraticGammaO c hc = S / 2 := hG
    _ = breveGaussianFourTerms a b := fixedDualPhase_four_terms a b

end

end ActualEisensteinCubic

theorem theta_counter_lambda_eq : ActualEisensteinCubic.lambda =
    ActualEisensteinCoordinates.eval (-1) 1 := by
  have homega : ActualEisensteinCubic.omega = ActualEisensteinCoordinates.omega := by
    rfl
  rw [ActualEisensteinCubic.lambda, ActualEisensteinCoordinates.eval, homega]
  ring

open ConcreteTraceCRT


namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end ShortDraftLocal

end

end OAI
