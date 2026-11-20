module

public import RequestProject.RoughVekuaTransport

/-! The exponential gauge applies to the regular correction of the rough driven vector.
Only the zeroth input row is rough; the same positive-row equations give the moments. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
local notation "κ" => -(Complex.I / (Real.sqrt 2 : ℂ))

section
variable {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) (hW : IsTransport γ E W)
    (p : BoundaryL2) (m α : ℂ)

local notation "u" => roughVekuaRegularCorrection γ E W p m α
local notation "y" => roughVekuaDrivenVector γ E W p m α
local notation "G" => physicalDrivenGauge γ E

private theorem roughVekuaDrivenVector_eq : y = fun t => u t + (κ * p t) • basisVec 0 := by
  funext t
  exact add_comm _ _

theorem roughVekuaGauge_zero_split (t : ℝ) :
    G y 0 t = -Complex.I * p t + G u 0 t := by
  rw [roughVekuaDrivenVector_eq p m α, physicalDrivenGauge_add_basisVec_zero]
  simp only [if_true]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  field_simp [hs]
  ring

private theorem roughVekuaGauge_succ_eq (j : ℕ) (t : ℝ) : G u (j + 1) t = G y (j + 1) t := by
  rw [roughVekuaDrivenVector_eq p m α, physicalDrivenGauge_add_basisVec_zero]
  simp

include hK hγ hW in
theorem roughVekuaGauge_regular_memLp (j : ℕ) : MemLp (G u j) 2 μB :=
  (physicalDrivenGauge_continuousOn γ hγ.continuous E u
    (roughVekuaRegularCorrection_continuousOn hγ hW p m α) j).memLp_Ioc

include hK hγ hW in
theorem roughVekuaGauge_zero_memLp : MemLp (G y 0) 2 μB := by
  simp_rw [show G y 0 = _ from funext (roughVekuaGauge_zero_split p m α)]
  exact ((Lp.memLp p).const_smul (-Complex.I)).add (roughVekuaGauge_regular_memLp hK hγ hW p m α 0)

include hK hγ hW in
private theorem roughGauge_derivative_input : ∀ᵐ t, t ∈ Ioo 0 (2 * Real.pi) →
    HasDerivAt u (transportCoeff γ E t (u t + (κ * p t) • basisVec 0) + (κ * m) • basisVec 0) t := by
  filter_upwards [roughVekuaRegularCorrection_ae_hasDerivAt hK hγ hW p m α] with t ht hi
  have h := ht hi
  rw [roughVekuaRegularCorrection_derivative_eq_transportCoeff p m α t,
    roughVekuaDrivenVector_eq p m α] at h
  exact h

include hK hγ hW in
theorem roughVekuaGauge_physicalMoment_eq_zero (hE : 0 < E)
    (hα : u (2 * Real.pi) = α • basisVec 0) (j k : ℕ) :
    physicalDrivenMoment γ E y j k = 0 := by
  have h0 := roughVekuaRegularCorrection_zero hW p m α
  refine physicalDrivenMoment_eq_zero hγ hE u y
    (roughVekuaRegularCorrection_absolutelyContinuous hK hγ hW p m α) ?_
    (roughVekuaGauge_succ_eq p m α) ?_ (fun l => ?_) j k
  · intro l
    cases l with
    | zero => exact roughVekuaGauge_zero_memLp hK hγ hW p m α
    | succ l =>
      rw [← funext (roughVekuaGauge_succ_eq p m α l)]
      exact roughVekuaGauge_regular_memLp hK hγ hW p m α (l + 1)
  · intro l
    filter_upwards [roughGauge_derivative_input hK hγ hW p m α] with t ht hi
    have h := hasDerivAt_physicalDrivenGauge_succ (hγ.differentiable_one t) (ht hi) l
    convert h using 1
    rw [roughVekuaDrivenVector_eq p m α]
    rfl
  · simp [physicalDrivenGauge_of_eq_smul_basisVec_zero γ E h0,
      physicalDrivenGauge_of_eq_smul_basisVec_zero γ E hα]

local notation "dG" => (fun t => physicalDrivenGaugeZeroContinuousPart γ E u t +
  physicalDrivenGaugeZeroCoeff γ E t * (κ * p t) + (Real.sqrt 2 : ℂ) * (κ * m))

include hK hγ hW in
theorem roughVekuaGauge_regular_isSobolevSeq_one (hα : u (2 * Real.pi) = α • basisVec 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (G u 0)) := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E u
    (roughVekuaRegularCorrection_continuousOn hγ hW p m α)
  have hd : MemLp dG 2 μB :=
    (hc.memLp_Ioc.add ((physicalDrivenGaugeZeroCoeff_continuous hγ E).continuousOn.mul_memLp_Ioc
      ((Lp.memLp p).const_smul κ))).add (memLp_const _)
  apply isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalDrivenGauge_absolutelyContinuous hγ
      (roughVekuaRegularCorrection_absolutelyContinuous hK hγ hW p m α) E 0) hd
  · filter_upwards [roughGauge_derivative_input hK hγ hW p m α] with t ht hi
    exact hasDerivAt_physicalDrivenGauge_zero (hγ.differentiable_one t) (ht hi)
  · rw [physicalDrivenGauge_of_eq_smul_basisVec_zero γ E (roughVekuaRegularCorrection_zero hW p m α),
      physicalDrivenGauge_of_eq_smul_basisVec_zero γ E hα]

end
end PolyaNeumann
end
