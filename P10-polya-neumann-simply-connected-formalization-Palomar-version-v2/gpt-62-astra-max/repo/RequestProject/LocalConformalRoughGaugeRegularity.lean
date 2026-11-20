module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.RoughVekuaTransport
public import RequestProject.PhysicalDrivenReconstruction
public import RequestProject.LocalConformalRoughHardySupport
public import RequestProject.PlanarNotation

/-
The factorial gauge of the genuine rough driven vector.  Only its zeroth
row contains the L2 primitive.  The entire regular correction is retained,
and the positive-row AC equations give the actual moment recurrence.
This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

local notation "μB" => angleMeasure

section GenuineGauge

variable {γ : ℝ → ℂ} {E : ℝ} {W : TransportPath}

section

variable (p : BoundaryL2) (m α : ℂ) (n j N : ℕ) (θ : ℝ)

theorem roughVekuaGauge_scaledRow_zero_split :
    physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) 0 θ =
      -Complex.I * p θ +
        physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0 θ := by
  have hs0 : vacuumWeight ≠ 0 := by
    simp
  simp only [physicalDrivenScaledRow, pow_zero, one_mul, physicalDrivenRow, if_true,
    roughVekuaDrivenVector, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, mul_one]
  field_simp [hs0] <;> ring

theorem roughVekuaGauge_scaledRow_succ_eq :
    physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1) θ =
      physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 1) θ := by
  simp [physicalDrivenScaledRow, physicalDrivenRow, roughVekuaDrivenVector_positive_coord]

theorem roughVekuaGauge_partial_succ_eq :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N θ =
      physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) (j + 1) N θ := by
  apply Finset.sum_congr rfl
  simp [physicalDrivenGaugeTerm, ← Nat.add_assoc, roughVekuaGauge_scaledRow_succ_eq]

theorem roughVekuaGauge_succ_eq :
    physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) θ =
      physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) (j + 1) θ := by
  apply tsum_congr
  simp [physicalDrivenGaugeTerm, ← Nat.add_assoc, roughVekuaGauge_scaledRow_succ_eq]

/-- The full zeroth gauge includes the actual rough primitive, with its
original scalar and its entire regular correction. -/
theorem roughVekuaGauge_zero_split :
    physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) 0 θ =
      -Complex.I * p θ + physicalDrivenGauge γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 θ := by
  
  
  rw [physicalDrivenGauge, ((summable_norm_physicalDrivenGaugeTerm γ E
    (roughVekuaDrivenVector γ E W p m α) 0 θ).of_norm).tsum_eq_zero_add, physicalDrivenGauge, ((summable_norm_physicalDrivenGaugeTerm γ E
    (roughVekuaRegularCorrection γ E W p m α) 0 θ).of_norm).tsum_eq_zero_add]
  have he : (fun l : ℕ => physicalDrivenGaugeTerm γ E
      (roughVekuaDrivenVector γ E W p m α) 0 (l + 1) θ) =
      fun l => physicalDrivenGaugeTerm γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 (l + 1) θ := by
    simp [physicalDrivenGaugeTerm, roughVekuaGauge_scaledRow_succ_eq]
  rw [he]
  simp only [physicalDrivenGaugeTerm, physicalDrivenPower, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, Nat.zero_add, roughVekuaGauge_scaledRow_zero_split]
  ring

theorem roughVekuaGauge_partial_zero_split :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) 0 N θ =
      -Complex.I * p θ + physicalDrivenGaugePartial γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 N θ := by
  induction N with
  | zero =>
    simpa [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower] using
      roughVekuaGauge_scaledRow_zero_split p m α θ
  | succ N ih =>
    simp only [physicalDrivenGaugePartial, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp [physicalDrivenGaugeTerm, roughVekuaGauge_scaledRow_succ_eq] <;> ring

end

variable {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    (hW : IsTransport γ E W)

include hK hγ hW in
theorem roughVekuaGauge_regular_memLp (p : BoundaryL2) (m α : ℂ) (j : ℕ) :
    MemLp (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) j) 2 μB := memLp_angle_of_continuousOn (physicalDrivenGauge_continuousOn γ hγ.continuous E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j)

section

variable (hE : 0 < E) (p : BoundaryL2) (m α : ℂ) (n : ℕ)
    (hα : roughVekuaRegularCorrection γ E W p m α anglePeriod = α • basisVec 0) (j N k : ℕ)

include hK hγ hW in
theorem roughVekuaGauge_zero_memLp :
    MemLp (physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) 0) 2 μB := MemLp.ae_eq (Eventually.of_forall fun θ => by
    simp [roughVekuaGauge_zero_split]) (((Lp.memLp p).const_smul (-Complex.I)).add
      (roughVekuaGauge_regular_memLp hK hγ hW p m α 0))

include hK hγ hW in
private theorem roughGauge_regular_row_ac :
    AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) n)
      0 anglePeriod := by
  have hc := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec n))
    (roughVekuaRegularCorrection_absolutelyContinuous hK hγ hW p m α)
  by_cases hn : n = 0
  · subst n
    convert hc.const_smul vacuumWeight using 1 <;>
      ext θ <;>
      simp [physicalDrivenScaledRow, physicalDrivenRow, inner_basisVec, smul_eq_mul]
  · convert hc.const_smul (physicalDrivenQ E ^ n) using 1 <;>
      ext θ <;>
      simp [physicalDrivenScaledRow, physicalDrivenRow, hn, inner_basisVec]

include hK hγ hW in
private theorem roughGauge_regular_partial_ac :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j N)
      0 anglePeriod := by
  have ht (l : ℕ) : AbsolutelyContinuousOnInterval
      (physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j l)
      0 anglePeriod := by
    
    refine (driven_c1_absolutelyContinuous ?_).smul (roughGauge_regular_row_ac hK hγ hW p m α _)
    exact ((hγ.sub contDiff_const).neg.pow l).div_const _
  induction N with
  | zero =>
    have he : physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j 0 =
        physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j 0 := Finset.sum_range_one _
    simp [*]
  | succ N ih =>
    have he : physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α)
        j (N + 1) = fun θ =>
          physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j N θ +
            physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j (N + 1) θ := by
      funext θ
      exact Finset.sum_range_succ _ _
    rw [he]
    exact ih.add (ht (N + 1))

include hK hγ hW in
private theorem roughGauge_partial_succ_ac :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N)
      0 anglePeriod := by
  
  rw [(funext (roughVekuaGauge_partial_succ_eq p m α j N))]
  exact roughGauge_regular_partial_ac hK hγ hW p m α (j + 1) N

include hK hγ hW in
theorem roughVekuaGauge_partial_succ_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt
        (physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N)
        (physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) j N θ +
          deriv γ θ * physicalDrivenPower γ N θ * physicalDrivenScaledRow E
            (roughVekuaDrivenVector γ E W p m α) (N + j + 2) θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α j]
      with θ hθ hmem
    convert hθ hmem using 1
    · funext s
      simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenRow]
    · simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow]
      ring
  | succ N ih =>
    filter_upwards [ih, roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α
      (N + j + 1)] with θ hθ hd hmem
    
    have he (k : ℕ) : physicalDrivenGaugePartial γ E
        (roughVekuaDrivenVector γ E W p m α) k (N + 1) = fun s =>
          physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) k N s +
            physicalDrivenGaugeTerm γ E (roughVekuaDrivenVector γ E W p m α) k (N + 1) s := by
      funext s
      exact Finset.sum_range_succ _ _
    rw [he]
    convert (hθ hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ N θ).mul (hd hmem)) using 1
    · funext s
      simp [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_left_comm]
    · rw [he]
      simp only [physicalDrivenGaugeTerm, Nat.add_comm, Nat.add_left_comm]
      ring

include hK hγ hW in
private theorem roughGauge_partial_memLp :
    MemLp (physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) j N) 2 μB := by
  
  have hc := physicalDrivenGaugePartial_continuousOn γ hγ.continuous E _ (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j N
  cases j with
  | zero =>
    exact MemLp.ae_eq (Eventually.of_forall fun θ => by
      simp [roughVekuaGauge_partial_zero_split])
      (((Lp.memLp p).const_smul (-Complex.I)).add (memLp_angle_of_continuousOn hc))
  | succ j =>
    exact MemLp.ae_eq (Eventually.of_forall fun θ => by
      rw [roughVekuaGauge_partial_succ_eq]) (memLp_angle_of_continuousOn hc)

include hW in
private theorem roughGauge_partial_succ_zero :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N 0 = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  rw [physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
    physicalDrivenScaledRow, roughVekuaDrivenRow_succ_zero hW]
  simp

include hα in
private theorem roughGauge_partial_succ_endpoint :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N
      anglePeriod = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  rw [physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
    physicalDrivenScaledRow, roughVekuaDrivenRow_succ_endpoint p m α hα]
  simp

include hα in
include hK hγ hW in
/-- Actual AC integration by parts for the positive finite gauge. The
zeroth gauge is used only as an L2 integrand, and the finite tail remains. -/
theorem roughVekuaGauge_momentPartial_recurrence :
    physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E
      (roughVekuaDrivenVector γ E W p m α) j N k +
      (k : ℂ) * physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) (j + 1) N (k - 1) =
      -physicalDrivenTailMoment γ E (roughVekuaDrivenVector γ E W p m α) j N k := by
  let f := roughVekuaDrivenVector γ E W p m α
  let z  := fun θ => conj (physicalDrivenCentered γ θ)
  let s := physicalDrivenGaugePartial γ E f (j + 1) N
  let a  := fun θ => conj (deriv γ θ) * physicalDrivenGaugePartial γ E f j N θ * z θ ^ k
  let b  := fun θ => conj (deriv γ θ) * s θ * z θ ^ (k - 1)
  let t  := fun θ => deriv γ θ * physicalDrivenPower γ N θ *
    physicalDrivenScaledRow E f (N + j + 2) θ * z θ ^ k
  let r  := fun θ => physicalDrivenQ E ^ 2 * a θ + k * b θ + t θ
  have hz1 : ContDiff ℝ 1 z :=
    Complex.conjCLE.contDiff.comp (hγ.sub contDiff_const)
  have hsz := (roughGauge_partial_succ_ac hK hγ hW p m α j N).smul
    (driven_c1_absolutelyContinuous (hz1.pow k))
  
  have ha : MemLp a 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ k) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow k)
    simpa only [a, f, mul_assoc, mul_left_comm, mul_comm] using
      rough_memLp_continuous_mul hw (roughGauge_partial_memLp hK hγ hW p m α j N)
  have hb : MemLp b 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ (k - 1)) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow _)
    simpa only [b, s, f, mul_assoc, mul_left_comm, mul_comm] using
      rough_memLp_continuous_mul hw (roughGauge_partial_memLp hK hγ hW p m α _ N)
  have ht : MemLp t 2 μB := by
    have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
    have hc : ContinuousOn t angleInterval := by
      have hp : Continuous (physicalDrivenPower γ N) := by
        exact ((hγ.continuous.sub continuous_const).neg.pow N).div_const _
      have hd : ContinuousOn
          (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (N + j + 2))
          angleInterval := continuousOn_const.mul
        (physicalDrivenRow_continuousOn _ hv _)
      
      
      
      convert (((hγ.continuous_deriv_one.mul hp).continuousOn.mul hd).mul
        (hz1.continuous.pow k).continuousOn) using 1
      ext θ
      exact congrArg (fun q => deriv γ θ * physicalDrivenPower γ N θ * q * z θ ^ k)
        (roughVekuaGauge_scaledRow_succ_eq p m α _ θ)
    exact memLp_angle_of_continuousOn hc
  have hr := ((ha.const_smul (physicalDrivenQ E ^ 2)).add (hb.const_smul (k : ℂ))).add ht
  have hd : ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (fun θ => s θ * z θ ^ k) (r θ) θ := by
    filter_upwards [roughVekuaGauge_partial_succ_ae_hasDerivAt hK hγ hW p m α j N]
      with θ hθ hmem
    have hdz : HasDerivAt z (conj (deriv γ θ)) θ := ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
    convert (hθ hmem).mul (hdz.pow k) using 1
    · simp <;> ring
  
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (by
        simpa only [s, f, Pi.smul_apply, smul_eq_mul, Pi.mul_def] using hsz) (by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact hr.integrable (by norm_num)) hd anglePeriod ⟨Real.two_pi_pos.le, le_rfl⟩
  have hs0 : s 0 = 0 := roughGauge_partial_succ_zero hW p m α j N
  have hsT : s anglePeriod = 0 := roughGauge_partial_succ_endpoint p m α hα j N
  simp [hs0, hsT] at he
  have hia := intervalIntegrable_boundary_of_memLp a ha
  have hib := intervalIntegrable_boundary_of_memLp b hb
  
  
  rw [intervalIntegral.integral_add ((hia.const_mul _).add (hib.const_mul _)) (intervalIntegrable_boundary_of_memLp t ht),
    intervalIntegral.integral_add (hia.const_mul _) (hib.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  exact eq_neg_of_add_eq_zero_left he.symm

include hK hγ hW in
theorem roughVekuaGauge_momentPartial_tendsto :
    Tendsto (fun N : ℕ => physicalDrivenMomentPartial γ E
      (roughVekuaDrivenVector γ E W p m α) j N k) atTop
      (𝓝 (physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k)) := by
  let v := roughVekuaRegularCorrection γ E W p m α
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  cases j with
  | succ j =>
    have he (N : ℕ) : physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) (j + 1) N k =
        physicalDrivenMomentPartial γ E v (j + 1) N k := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp
      rw [roughVekuaGauge_partial_succ_eq p m α j N θ]
    have he' : physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) k =
        physicalDrivenMoment γ E v (j + 1) k := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [v]
      rw [roughVekuaGauge_succ_eq p m α j θ]
    simpa [he, he'] using physicalDrivenMomentPartial_tendsto γ hγ E v hv (j + 1) k
  | zero =>
    let w  := fun θ => conj (deriv γ θ) * conj (physicalDrivenCentered γ θ) ^ k
    let c  := ∫ₚ θ, w θ * (-Complex.I * p θ)
    have hw : Continuous w := (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
      ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow k)
    have hbase : MemLp (fun θ : ℝ => w θ * (-Complex.I * p θ)) 2 μB := by
      simpa only [Pi.smul_def, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        (rough_memLp_continuous_mul hw (Lp.memLp p)).const_smul (-Complex.I)
    have hi := intervalIntegrable_boundary_of_memLp _ hbase
    have he (N : ℕ) : physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) 0 N k = c + physicalDrivenMomentPartial γ E v 0 N k := by
      
      calc
        _ = ∫ₚ θ, w θ * (-Complex.I * p θ) +
            w θ * physicalDrivenGaugePartial γ E v 0 N θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp
          rw [roughVekuaGauge_partial_zero_split p m α N θ]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add hi (intervalIntegrable_boundary_of_memLp _ (rough_memLp_continuous_mul hw
            (memLp_angle_of_continuousOn (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E v hv 0 N))))]
          congr 1
          apply intervalIntegral.integral_congr
          intro θ _
          ring
    have he' : physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) 0 k =
        c + physicalDrivenMoment γ E v 0 k := by
      
      calc
        _ = ∫ₚ θ, w θ * (-Complex.I * p θ) +
            w θ * physicalDrivenGauge γ E v 0 θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp
          rw [roughVekuaGauge_zero_split p m α θ]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add hi (intervalIntegrable_boundary_of_memLp _ (rough_memLp_continuous_mul hw
            (roughVekuaGauge_regular_memLp hK hγ hW p m α 0)))]
          congr 1
          apply intervalIntegral.integral_congr
          intro θ _
          ring
    simpa [he, he'] using (physicalDrivenMomentPartial_tendsto γ hγ E v hv 0 k).const_add c

include hK hγ hW in
theorem roughVekuaGauge_tailMoment_tendsto_zero :
    Tendsto (fun N : ℕ => physicalDrivenTailMoment γ E
      (roughVekuaDrivenVector γ E W p m α) j N k) atTop (𝓝 0) := by
  have he (N : ℕ) : physicalDrivenTailMoment γ E (roughVekuaDrivenVector γ E W p m α) j N k =
      physicalDrivenTailMoment γ E (roughVekuaRegularCorrection γ E W p m α) j N k := by
    apply intervalIntegral.integral_congr
    intro θ _
    change deriv γ θ * physicalDrivenPower γ N θ *
      physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (N + j + 2) θ *
      conj (physicalDrivenCentered γ θ) ^ k = _
    rw [roughVekuaGauge_scaledRow_succ_eq p m α (N + j + 1) θ]
  simpa [he] using physicalDrivenTailMoment_tendsto_zero γ hγ E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j k

include hα in
include hK hγ hW in
theorem roughVekuaGauge_moment_recurrence :
    physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k +
      (k : ℂ) * physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) (k - 1) = 0 := by
  have hl := ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α j k).const_mul (physicalDrivenQ E ^ 2)).add
      ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α (j + 1) (k - 1)).const_mul (k : ℂ))
  
  apply tendsto_nhds_unique hl
  simpa only [roughVekuaGauge_momentPartial_recurrence hK hγ hW p m α hα, neg_zero] using
    (roughVekuaGauge_tailMoment_tendsto_zero hK hγ hW p m α j k).neg

include hE hα in
include hK hγ hW in
/-- Every original physical moment vanishes, including all moments of
the rough zeroth gauge. No trace point value of its primitive is used. -/
theorem roughVekuaGauge_physicalMoment_eq_zero :
    physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k = 0 := by
  induction k generalizing j with
  | zero =>
    have h := roughVekuaGauge_moment_recurrence hK hγ hW p m α hα j 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)
  | succ k ih =>
    have h := roughVekuaGauge_moment_recurrence hK hγ hW p m α hα j (k + 1)
    rw [Nat.add_sub_cancel, ih (j + 1), mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)

include hK hγ hW in
private theorem roughGauge_regular_zero_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0)
        (2 * deriv γ θ * physicalDrivenScaledRow E
          (roughVekuaRegularCorrection γ E W p m α) 1 θ - Complex.I * m) θ := by
  filter_upwards [roughVekuaRegularCorrection_ae_hasDerivAt hK hγ hW p m α]
    with θ hθ hmem
  have hd := (((innerSL ℂ (basisVec 0)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hθ hmem)).const_mul vacuumWeight
  change HasDerivAt
    (fun t : ℝ => vacuumWeight * inner ℂ (basisVec 0)
      (roughVekuaRegularCorrection γ E W p m α t))
    (vacuumWeight * inner ℂ (basisVec 0)
      (transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
        (-(Complex.I / vacuumWeight)) • roughVekuaRegularForce γ E p m θ)) θ at hd
  rw [roughVekuaRegularCorrection_derivative_eq_transportCoeff] at hd
  simp only [inner_basisVec] at hd
  have hs : vacuumWeight ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : vacuumWeight ≠ 0 := by
    simp
  have hcoup (a b c : ℂ) :
      vacuumWeight * (a * (b * (vacuumWeight * c))) =
        2 * b * (a * c) := calc
      _ = vacuumWeight ^ 2 * (b * (a * c)) := by ring
      _ = _ := by rw [hs]; ring
  have hforce : vacuumWeight * (-(Complex.I / vacuumWeight) * m) =
      -Complex.I * m := by
    field_simp [hs0]
  have he : physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0 =
      fun t : ℝ => vacuumWeight *
        (roughVekuaRegularCorrection γ E W p m α t : ℕ → ℂ) 0 := by
    funext t
    simp [physicalDrivenScaledRow, physicalDrivenRow]
  rw [he]
  apply hd.congr_deriv
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, if_true, mul_one]
  rw [transportCoeff_apply_coord, shiftN_apply_zero,
    roughVekuaDrivenVector_positive_coord]
  simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_one, physicalDrivenQ,
    Nat.one_ne_zero, if_false, shiftWeight, if_true, mul_zero, add_zero]
  rw [mul_add, hcoup, hforce]
  ring

include hK hγ hW in
private theorem roughGauge_regular_positive_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt
        (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ((if n = 0 then -Complex.I * p θ else 0) +
              physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) n θ)) θ := by
  filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α n]
    with θ hθ hmem
  
  rw [(funext (roughVekuaGauge_scaledRow_succ_eq p m α n))] at hθ
  convert hθ hmem using 1
  cases n with
  | zero => simp [roughVekuaGauge_scaledRow_succ_eq, roughVekuaGauge_scaledRow_zero_split]
  | succ n => simp [roughVekuaGauge_scaledRow_succ_eq]

/-- The actual L2 derivative of the continuous correction gauge. The
rough primitive occurs only multiplied by a true continuous coefficient. -/
def roughVekuaGaugeRegularDerivative (γ : ℝ → ℂ) (E : ℝ)
    (W : TransportPath) (p : BoundaryL2) (m α : ℂ) (θ : ℝ) : ℂ :=
  physicalDrivenGaugeZeroContinuousPart γ E (roughVekuaRegularCorrection γ E W p m α) θ -
    Complex.I * m - Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
      physicalDrivenPower γ 1 θ * p θ

include hK hγ hW in
theorem roughVekuaGauge_regular_derivative_memLp :
    MemLp (roughVekuaGaugeRegularDerivative γ E W p m α) 2 μB := by
  
  
  refine ((memLp_angle_of_continuousOn (physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α))).sub (memLp_const _)).sub
    (rough_memLp_continuous_mul ?_ (Lp.memLp p))
  have hp : Continuous (physicalDrivenPower γ 1) := ((hγ.continuous.sub continuous_const).neg.pow 1).div_const _
  fun_prop

include hK hγ hW in
private theorem roughGauge_regular_partial_zero_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt
        (physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 1 θ -
          Complex.I * m + deriv γ θ * physicalDrivenGaugeTerm γ E
            (roughVekuaRegularCorrection γ E W p m α) 1 (N + 1) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
              (roughVekuaRegularCorrection γ E W p m α) l θ -
          Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenPower γ 1 θ * p θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughGauge_regular_zero_ae_hasDerivAt hK hγ hW p m α,
      roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α 0] with θ h0 h1 hmem
    
    convert ((h0 hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ 0 θ).mul (h1 hmem))) using 1
    · funext s
      norm_num [physicalDrivenGaugePartial, Finset.sum_range_succ,
        physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
      simp [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow] ; ring
  | succ N ih =>
    filter_upwards [ih, roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α _]
      with θ hθ hd hmem
    let w₀ := roughVekuaRegularCorrection γ E W p m α
    have he : physicalDrivenGaugePartial γ E (w₀)
        0 (N + 2) = fun t =>
          physicalDrivenGaugePartial γ E (w₀) 0 (N + 1) t +
            physicalDrivenGaugeTerm γ E (w₀) 0 (N + 2) t := by
      funext t
      exact Finset.sum_range_succ _ _
    rw [show N + 1 + 1 = N + 2 by omega, he]
    have hsum :
        (∑ l ∈ Finset.range (N + 2), physicalDrivenShiftedGaugeTerm γ E
          (w₀) l θ) =
        (∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
          (w₀) l θ) +
          physicalDrivenShiftedGaugeTerm γ E
            (w₀) (N + 1) θ := by
      simp [Finset.sum_range_succ]
    have hweighted := congrArg
      (fun q : ℂ => physicalDrivenQ E ^ 2 * conj (deriv γ θ) * q) hsum
    
    convert (hθ hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ (N + 1) θ).mul (hd hmem)) using 1
    · rfl
    · rw [hweighted]
      simp only [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm,
        Nat.succ_ne_zero, if_false, zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      ring

private theorem roughGauge_regular_partial_at_initial_vector {θ : ℝ}
    (hv : roughVekuaRegularCorrection γ E W p m α θ = α • basisVec 0) :
    physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 N θ =
      vacuumWeight * α := by
  induction N with
  | zero => simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
      physicalDrivenScaledRow, physicalDrivenRow, hv, basisVec_coord]
  | succ N ih =>
    rw [physicalDrivenGaugePartial, Finset.sum_range_succ]
    change physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 N θ + _ = _
    simp [ih, physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow, hv, basisVec_coord]

include hK hγ hW in
private theorem roughGauge_regular_partial_zero_primitive {θ : ℝ} (hθ : θ ∈ angleInterval) :
    physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 1) θ =
      vacuumWeight * α +
      (∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 1 s -
          Complex.I * m - Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) *
            physicalDrivenPower γ 1 s * p s) +
      (∫ s in (0 : ℝ)..θ, deriv γ s * physicalDrivenGaugeTerm γ E
        (roughVekuaRegularCorrection γ E W p m α) 1 (N + 1) s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
          (roughVekuaRegularCorrection γ E W p m α) l s) := by
  let v := roughVekuaRegularCorrection γ E W p m α
  let a  := fun s => deriv γ s * physicalDrivenScaledRow E v 1 s - Complex.I * m -
    Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s
  let t  := fun s => deriv γ s * physicalDrivenGaugeTerm γ E v 1 (N + 1) s
  let b  := fun s => conj (deriv γ s) *
    ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have ha : MemLp a 2 μB := by
    
    
    refine ((memLp_angle_of_continuousOn (hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn v hv 1)))).sub (memLp_const _)).sub
      (rough_memLp_continuous_mul ?_ (Lp.memLp p))
    have hp' : Continuous (physicalDrivenPower γ 1) := ((hγ.continuous.sub continuous_const).neg.pow 1).div_const _
    fun_prop
  have ht  :=
    hγ.continuous_deriv_one.continuousOn.mul
      (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E v hv 1 (N + 1))
  have hb : ContinuousOn b angleInterval :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (continuousOn_finset_sum _ fun l _ =>
        physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)
  
  
  have hri : IntegrableOn (fun s => a s + t s + physicalDrivenQ E ^ 2 * b s)
      angleInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact ((ha.add (memLp_angle_of_continuousOn ht)).add
      ((memLp_angle_of_continuousOn hb).const_smul (physicalDrivenQ E ^ 2))).integrable (by norm_num)
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (roughGauge_regular_partial_ac hK hγ hW p m α 0 _) hri (by
      filter_upwards [roughGauge_regular_partial_zero_ae_hasDerivAt hK hγ hW p m α N]
        with s hs hmem
      convert hs hmem using 1
      · ring) θ hθ
  rw [roughGauge_regular_partial_at_initial_vector p m α (N + 1)
    (roughVekuaRegularCorrection_zero hW p m α)] at he
  have hsub : uIcc 0 θ ⊆ angleInterval := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have hai : IntervalIntegrable a volume 0 θ := by
    have hI : IntegrableOn a angleInterval := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact ha.integrable (by norm_num)
    exact (hI.mono_set hsub).intervalIntegrable
  have hti : IntervalIntegrable t volume 0 θ := (ht.mono hsub).intervalIntegrable
  
  rw [intervalIntegral.integral_add (hai.add hti) (((hb.mono hsub).intervalIntegrable).const_mul _),
    intervalIntegral.integral_add hai hti, intervalIntegral.integral_const_mul] at he
  simp [*] <;> ring

include hK hγ hW in
/-- The correction gauge is an actual primitive of the computed L2
derivative. The factorial tail and the shifted series are integrated
before taking their genuine limits. -/
theorem roughVekuaGauge_regular_primitive
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0 θ =
      vacuumWeight * α +
        ∫ s in (0 : ℝ)..θ, roughVekuaGaugeRegularDerivative γ E W p m α s := by
  classical
  let v := roughVekuaRegularCorrection γ E W p m α
  let a  := fun s => deriv γ s * physicalDrivenScaledRow E v 1 s - Complex.I * m -
    Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s
  let b  := fun s => conj (deriv γ s) * physicalDrivenShiftedGauge γ E v s
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  
  have ht := ((physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv 1
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)
  have hs := physicalDrivenShiftedGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv
    (fun s => conj (deriv γ s))
    (by fun_prop) hθ
  have hsub : uIcc 0 θ ⊆ angleInterval := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have he (N : ℕ) : (∫ s in 0..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s) =
      ∑ l ∈ Finset.range (N + 1), ∫ s in 0..θ,
        conj (deriv γ s) * physicalDrivenShiftedGaugeTerm γ E v l s := by
    simp_rw [Finset.mul_sum]
    apply intervalIntegral.integral_finset_sum
    intro l _
    exact (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)).mono hsub).intervalIntegrable
  have hb := (hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr' (Eventually.of_forall fun N => (he N).symm)
  have hr := ((tendsto_const_nhds (x := vacuumWeight * α + ∫ s in (0 : ℝ)..θ, a s)).add ht).add
        (hb.const_mul (physicalDrivenQ E ^ 2))
  simp only [add_zero, Function.comp_apply] at hr
  have hlim : physicalDrivenGauge γ E v 0 θ =
      (Real.sqrt 2) * α + (∫ s in 0..θ, a s) +
        physicalDrivenQ E ^ 2 * (∫ s in 0..θ, b s) :=
    tendsto_nhds_unique (((summable_norm_physicalDrivenGaugeTerm γ E v 0 θ).of_norm.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 2)) (hr.congr' (Eventually.of_forall fun N =>
      (roughGauge_regular_partial_zero_primitive hK hγ hW p m α N hθ).symm))
  have ha : MemLp a 2 μB := by
    
    
    refine ((memLp_angle_of_continuousOn (hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn v hv 1)))).sub (memLp_const _)).sub
      (rough_memLp_continuous_mul ?_ (Lp.memLp p))
    have hp' : Continuous (physicalDrivenPower γ 1) := ((hγ.continuous.sub continuous_const).neg.pow 1).div_const _
    fun_prop
  
  have hbi : IntervalIntegrable b volume 0 θ :=
    (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E v hv)).mono hsub).intervalIntegrable
  rw [hlim, ← intervalIntegral.integral_const_mul, add_assoc,
    ← intervalIntegral.integral_add (by
      have hI : IntegrableOn a angleInterval := by
        rw [integrableOn_Icc_iff_integrableOn_Ioc]
        exact ha.integrable (by norm_num)
      exact (hI.mono_set hsub).intervalIntegrable) (hbi.const_mul _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [a, b, roughVekuaGaugeRegularDerivative, physicalDrivenGaugeZeroContinuousPart, v]
  ring

include hK hγ hW in
theorem roughVekuaGauge_regular_absolutelyContinuous :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)
      0 anglePeriod := by
  
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => vacuumWeight * α) 0 anglePeriod := by
    simpa only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero] using
      tendsto_const_nhds
  
  apply driven_ac_congr
  exact hconst.add (absolutelyContinuousOnInterval_intervalIntegral_banach (intervalIntegrable_boundary_of_memLp _
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α))
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩))
  intro θ hθ
  exact (roughVekuaGauge_regular_primitive hK hγ hW p m α hθ).symm

include hK hγ hW in
theorem roughVekuaGauge_regular_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)
        (roughVekuaGaugeRegularDerivative γ E W p m α θ) θ := by
  
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le (intervalIntegrable_boundary_of_memLp _
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α))]
    with θ hθ hmem
  refine ((hθ hmem).const_add (vacuumWeight * α)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with t ht
  exact roughVekuaGauge_regular_primitive hK hγ hW p m α (Ioo_subset_Icc_self ht)

private theorem roughGauge_regular_at_initial_vector
    {θ : ℝ} (hv : roughVekuaRegularCorrection γ E W p m α θ = α • basisVec 0) :
    physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0 θ =
      vacuumWeight * α := by
  
  rw [physicalDrivenGauge, ((summable_norm_physicalDrivenGaugeTerm γ E
    (roughVekuaRegularCorrection γ E W p m α) 0 θ).of_norm).tsum_eq_zero_add]
  have ht : (fun l : ℕ => physicalDrivenGaugeTerm γ E
      (roughVekuaRegularCorrection γ E W p m α) 0 (l + 1) θ) = fun _ => 0 := by
    simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow, hv, basisVec_coord]
  simp [physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow,
    physicalDrivenRow, hv, basisVec_coord]

include hα in
include hK hγ hW in
/-- The regular factorial gauge has true H1 Fourier coefficients. Both
endpoints are sqrt(2) α by the computed vector endpoints; no endpoint or
derivative of the rough primitive is assumed. -/
theorem roughVekuaGauge_regular_isSobolevSeq_one :
    IsSobolevSeq 1 (angleCoeff
      (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)) := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (roughVekuaGauge_regular_absolutelyContinuous hK hγ hW p m α)
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
    (roughVekuaGauge_regular_ae_hasDerivAt hK hγ hW p m α)
    ((roughGauge_regular_at_initial_vector p m α (roughVekuaRegularCorrection_zero hW p m α)).trans (roughGauge_regular_at_initial_vector p m α hα).symm)

end

end GenuineGauge

end PolyaNeumann

end
