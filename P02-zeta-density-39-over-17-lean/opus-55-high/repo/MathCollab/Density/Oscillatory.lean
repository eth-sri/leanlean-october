module
/-
Adapted from Scott McColm, RiemannZeta/GuthMaynard/LargeValuesReflection.lean,
commit 2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be (MIT).
See ../../../third_party/mccolm/LICENSE and THIRD_PARTY_NOTICES.md.
Only the oscillatory endpoint dependency slice is ported here.
-/
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex MeasureTheory Real Set

namespace MathCollab.Density

/-- The common logarithmic oscillatory integral after the source change of
variables `v = m N u`. -/
noncomputable def gmReflectionIntegral (tau A B : ℝ) : ℂ :=
  ∫ v in A..B,
    (v : ℂ)⁻¹ * Complex.exp
      ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

/-- The unit-modulus primitive used for integration by parts away from the
stationary point. -/
noncomputable def gmReflectionPrimitive (tau v : ℝ) : ℂ :=
  I⁻¹ * Complex.exp
    ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

/-- The quotient of the reflection amplitude by the derivative of its phase.
The only pole is the stationary point `tau/(2π)`. -/
noncomputable def gmReflectionRatio (tau v : ℝ) : ℂ :=
  ((tau - 2 * Real.pi * v : ℝ) : ℂ)⁻¹

/-- Real form of the integration-by-parts quotient. -/
noncomputable def gmReflectionRatioReal (tau v : ℝ) : ℝ :=
  (tau - 2 * Real.pi * v)⁻¹

theorem hasDerivAt_gmReflectionPrimitive {tau v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (gmReflectionPrimitive tau)
      (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
        Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) v := by
  have hReal : HasDerivAt
      (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x)
      (tau / v - 2 * Real.pi) v := by
    convert ((Real.hasDerivAt_log hv).const_mul tau).sub
      ((hasDerivAt_id v).const_mul (2 * Real.pi)) using 1
    · rfl
    grind
  pm_1432
  · rfl
  · field_simp [Complex.I_ne_zero]

section
variable {tau v : ℝ} (hv : tau - 2 * Real.pi * v ≠ 0)
include tau v hv
theorem hasDerivAt_gmReflectionRatio :
    HasDerivAt (gmReflectionRatio tau)
      (((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) v := by
  pm_4281
  pm_950
  grind

theorem hasDerivAt_gmReflectionRatioReal :
    HasDerivAt (gmReflectionRatioReal tau)
      (2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2) v := by
  pm_4281
  pm_828
end

/-- Pointwise factorization of the reflection integrand as a smooth quotient
times the derivative of a unit-modulus primitive. -/
theorem gmReflectionRatio_mul_primitiveDeriv {tau v : ℝ}
    (hv : v ≠ 0) (hstat : tau - 2 * Real.pi * v ≠ 0) :
    gmReflectionRatio tau v *
        (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
          Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
      (v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
  unfold gmReflectionRatio
  pm_115 hvC v Complex.ofReal_ne_zero.mpr hv
  have hstatC : ((tau - 2 * Real.pi * v : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hstat
  have hDerivative : ((tau / v - 2 * Real.pi : ℝ) : ℂ) =
      ((tau - 2 * Real.pi * v : ℝ) : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    grind
  rw [hDerivative]
  grind

/-- Exact integration-by-parts identity on an interval which does not meet
the stationary point. -/
theorem gmReflectionIntegral_eq_parts {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a)
    (hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0) :
    gmReflectionIntegral tau a b =
      gmReflectionRatio tau b * gmReflectionPrimitive tau b -
        gmReflectionRatio tau a * gmReflectionPrimitive tau a -
          ∫ v in a..b,
            ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v := by
  have hpos : ∀ v ∈ Set.Icc a b, 0 < v := fun v hv => ha.trans_le hv.1
  have hRatioDeriv : ∀ v ∈ Set.Icc a b,
      HasDerivAt (gmReflectionRatio tau)
        (((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) v :=
    fun v hv => hasDerivAt_gmReflectionRatio (hstat v hv)
  have hPrimitiveDeriv : ∀ v ∈ Set.Icc a b,
      HasDerivAt (gmReflectionPrimitive tau)
        (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
          Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) v :=
    fun v hv => hasDerivAt_gmReflectionPrimitive (hpos v hv).ne'
  have hRatioDerivU : ∀ v ∈ Set.uIcc a b,
      HasDerivAt (gmReflectionRatio tau)
        (((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) v := by
    simpa only [uIcc_of_le hab] using hRatioDeriv
  have hPrimitiveDerivU : ∀ v ∈ Set.uIcc a b,
      HasDerivAt (gmReflectionPrimitive tau)
        (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
          Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) v := by
    simpa only [uIcc_of_le hab] using hPrimitiveDeriv
  have hRatioInt : IntervalIntegrable
      (fun v : ℝ => ((2 * Real.pi /
        (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) volume a b :=
    (continuousOn_of_forall_continuousAt fun v hv => by
      pm_4282
      have hden : tau - 2 * Real.pi * v ≠ 0 := hstat v hvIcc
      exact Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div
          ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)
          (pow_ne_zero 2 hden))).intervalIntegrable
  have hPrimitiveInt : IntervalIntegrable
      (fun v : ℝ => ((tau / v - 2 * Real.pi : ℝ) : ℂ) *
        Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) volume a b :=
    (continuousOn_of_forall_continuousAt fun v hv => by
      pm_4282
      have hvNe : v ≠ 0 := (hpos v hvIcc).ne'
      have hFirst : ContinuousAt (fun x : ℝ => tau / x - 2 * Real.pi) v :=
        continuousAt_const.div continuousAt_id hvNe |>.sub continuousAt_const
      pm_876 hvNe
      exact (Complex.continuous_ofReal.continuousAt.comp hFirst).mul
        ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
          continuousAt_const).cexp).intervalIntegrable
  have hParts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hRatioDerivU hPrimitiveDerivU hRatioInt hPrimitiveInt
  unfold gmReflectionIntegral
  rw [← hParts]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hv
  exact (gmReflectionRatio_mul_primitiveDeriv (hpos v hvIcc).ne'
    (hstat v hvIcc)).symm

theorem norm_gmReflectionPrimitive (tau v : ℝ) :
    ‖gmReflectionPrimitive tau v‖ = 1 := by
  simp [gmReflectionPrimitive, Complex.norm_exp]

theorem norm_gmReflectionRatio (tau v : ℝ) :
    ‖gmReflectionRatio tau v‖ = |tau - 2 * Real.pi * v|⁻¹ := by
  rw [gmReflectionRatio, norm_inv, Complex.norm_real]
  rw [Real.norm_eq_abs]

/-- On the positive axis, the rescaled reflection integrand has norm `1/v`.
This is the amplitude estimate used both near and away from its stationary
point. -/
theorem norm_gmReflectionIntegrand {tau v : ℝ} (hv : 0 < v) :
    ‖(v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))‖ = v⁻¹ := by
  rw [norm_mul, norm_inv]
  simp [Real.norm_eq_abs, abs_of_pos hv, Complex.norm_exp]

/-- Quantitative integration-by-parts bound on an interval avoiding the
stationary point.  The last term is the exact total variation of the phase
quotient. -/
theorem norm_gmReflectionIntegral_le_endpoint_variation {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a)
    (hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0) :
    ‖gmReflectionIntegral tau a b‖ ≤
      |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
        |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
  rw [gmReflectionIntegral_eq_parts hab ha hstat]
  have hDerivU : ∀ v ∈ Set.uIcc a b,
      HasDerivAt (gmReflectionRatioReal tau)
        (2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2) v := by
    intro v hv
    apply hasDerivAt_gmReflectionRatioReal
    apply hstat v
    simpa only [uIcc_of_le hab] using hv
  have hDerivContinuous : ContinuousOn
      (fun v : ℝ => 2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2)
      (Set.uIcc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro v hv
    pm_4282
    exact continuousAt_const.div
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)
      (pow_ne_zero 2 (hstat v hvIcc))
  have hDerivativeIntegral :
      (∫ v in a..b, 2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2) =
        gmReflectionRatioReal tau b - gmReflectionRatioReal tau a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hDerivU
      hDerivContinuous.intervalIntegrable
  have hVariation :
      ‖∫ v in a..b,
          ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
            gmReflectionPrimitive tau v‖ ≤
        |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
    have hNormIntegralEq :
        (∫ v in a..b,
            ‖((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v‖) =
          ∫ v in a..b, 2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v hv
      change ‖((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
          gmReflectionPrimitive tau v‖ =
        2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2
      rw [norm_mul, norm_gmReflectionPrimitive, mul_one, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg (by positivity) (sq_nonneg _)
    calc
      ‖∫ v in a..b,
          ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
            gmReflectionPrimitive tau v‖ ≤
          |∫ v in a..b,
            ‖((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      _ = |∫ v in a..b,
          2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2| := by
        rw [hNormIntegralEq]
      _ = |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
        rw [hDerivativeIntegral]
  calc
    ‖gmReflectionRatio tau b * gmReflectionPrimitive tau b -
        gmReflectionRatio tau a * gmReflectionPrimitive tau a -
          ∫ v in a..b,
            ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v‖ ≤
        ‖gmReflectionRatio tau b * gmReflectionPrimitive tau b -
          gmReflectionRatio tau a * gmReflectionPrimitive tau a‖ +
            ‖∫ v in a..b,
              ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
                gmReflectionPrimitive tau v‖ := norm_sub_le _ _
    _ ≤ (‖gmReflectionRatio tau b * gmReflectionPrimitive tau b‖ +
          ‖gmReflectionRatio tau a * gmReflectionPrimitive tau a‖) +
            |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| :=
      add_le_add (norm_sub_le _ _) hVariation
    _ = |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
          |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
      rw [norm_mul, norm_mul, norm_gmReflectionRatio, norm_gmReflectionRatio,
        norm_gmReflectionPrimitive, norm_gmReflectionPrimitive, mul_one, mul_one]

section
variable {tau a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
include tau a b hab ha
/-- First-derivative bound on an interval strictly to the left of the
stationary point. -/
theorem norm_gmReflectionIntegral_le_left (hleft : 2 * Real.pi * b < tau) :
    ‖gmReflectionIntegral tau a b‖ ≤ 2 / (tau - 2 * Real.pi * b) := by
  pm_4284 hdb b
  have hda : 0 < tau - 2 * Real.pi * a := by
    pm_4283
  have hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0 := by
    intro v hv
    have := mul_le_mul_of_nonneg_left hv.2 (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hBase := norm_gmReflectionIntegral_le_endpoint_variation hab ha hstat
  have hInvOrder : (tau - 2 * Real.pi * a)⁻¹ ≤
      (tau - 2 * Real.pi * b)⁻¹ := by
    apply (inv_le_inv₀ hda hdb).2
    pm_4283
  pm_1584
  calc
    ‖gmReflectionIntegral tau a b‖ ≤
        |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
          |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := hBase
    _ = 2 / (tau - 2 * Real.pi * b) := by
      pm_8714 abs_of_pos
      ring

/-- First-derivative bound on an interval strictly to the right of the
stationary point. -/
theorem norm_gmReflectionIntegral_le_right (hright : tau < 2 * Real.pi * a) :
    ‖gmReflectionIntegral tau a b‖ ≤ 2 / (2 * Real.pi * a - tau) := by
  have hda : tau - 2 * Real.pi * a < 0 := by linarith
  have hdb : tau - 2 * Real.pi * b < 0 := by
    pm_4283
  have hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0 := by
    intro v hv
    have := mul_le_mul_of_nonneg_left hv.1 (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hBase := norm_gmReflectionIntegral_le_endpoint_variation hab ha hstat
  have hInvOrder : (tau - 2 * Real.pi * a)⁻¹ ≤
      (tau - 2 * Real.pi * b)⁻¹ := by
    apply (inv_le_inv_of_neg hda hdb).2
    pm_4283
  pm_1584
  calc
    ‖gmReflectionIntegral tau a b‖ ≤
        |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
          |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := hBase
    _ = 2 / (2 * Real.pi * a - tau) := by
      pm_8714 abs_of_neg
      pm_615 hNegInv a
      pm_615 hNegInvB b
      rw [hNegInv, hNegInvB]
      ring
end

/-- Trivial amplitude bound on a positive interval. -/
theorem norm_gmReflectionIntegral_le_length_div {tau a b L : ℝ}
    (hab : a ≤ b) (hL : 0 < L) (hLa : L ≤ a) :
    ‖gmReflectionIntegral tau a b‖ ≤ (b - a) / L := by
  unfold gmReflectionIntegral
  have hBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := L⁻¹)
    (f := fun v : ℝ => (v : ℂ)⁻¹ * Complex.exp
      ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
    (fun v hv => by
      rw [uIoc_of_le hab] at hv
      have hLv : L ≤ v := hLa.trans (le_of_lt hv.1)
      have hvPos : 0 < v := hL.trans_le hLv
      rw [norm_gmReflectionIntegrand hvPos]
      exact (inv_le_inv₀ hvPos hL).2 hLv)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hBound
  calc
    ‖∫ v in a..b,
        (v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))‖ ≤
        L⁻¹ * (b - a) := hBound
    _ = (b - a) / L := by ring

theorem intervalIntegrable_gmReflectionIntegrand {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) :
    IntervalIntegrable
      (fun v : ℝ => (v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro v hv
  pm_4282
  have hvPos : 0 < v := ha.trans_le hvIcc.1
  pm_876 hvPos.ne'
  exact (Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
      (Complex.ofReal_ne_zero.mpr hvPos.ne') |>.mul
    ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul continuousAt_const).cexp


end MathCollab.Density
