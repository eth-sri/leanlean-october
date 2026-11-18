module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDistribution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Reverse-time distributional derivative kernel

This module proves that an integrable scalar function on the literal
reverse-time interval with vanishing pairings against all test derivatives is
almost everywhere constant.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Function MeasureTheory Set
open scoped ENNReal Interval

private def reverseTimeTestPrimitive {T : ℝ} (psi : ReverseTimeScalarTest T) : ℝ → ℝ :=
  fun t => ∫ x in (0 : ℝ)..t, psi x




private theorem integrable_mul_reverseTimeScalarTest
    {T : ℝ} {f : ℝ → ℝ}
    (hf : Integrable f (reverseTimeVolume T)) (eta : ReverseTimeScalarTest T) :
    Integrable (fun t => f t * eta t) (reverseTimeVolume T) := by
  obtain ⟨C, hC⟩ := eta.exists_norm_le
  apply hf.mul_bdd eta.contDiff.continuous.aestronglyMeasurable
  filter_upwards with t
  exact hC t

/-- An integrable scalar function on the reverse-time interval with zero
pairing against every test derivative is almost everywhere constant. -/
theorem exists_ae_eq_const_of_integral_deriv_eq_zero
    (T : ℝ) (hT : 0 < T) {f : ℝ → ℝ}
    (hf : MeasureTheory.Integrable f (reverseTimeVolume T))
    (hzero : ∀ eta : ReverseTimeScalarTest T,
      (∫ tau, f tau * eta.deriv tau ∂reverseTimeVolume T) = 0) :
    ∃ c : ℝ, f =ᵐ[reverseTimeVolume T] fun _ => c    := by
  have integral_reverseTime_eq_integral_of_tsupport_subset {T : ℝ} {g : ℝ → ℝ} (hg : tsupport g ⊆ reverseTimeOpenInterval T) :
      (∫ t, g t ∂reverseTimeVolume T) = ∫ t, g t := by
    change (∫ t in Ioo 0 T, g t) = ∫ t, g t
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    exact fun htg => ht (hg htg)
  have exists_primitive_reverseTimeScalarTest_of_integral_eq_zero (psi : ReverseTimeScalarTest T) (hpsi : (∫ t, psi t ∂reverseTimeVolume T) = 0) :
      ∃ eta : ReverseTimeScalarTest T, eta.deriv = (psi : ℝ → ℝ) := by
    by_cases hsupport : (tsupport (psi : ℝ → ℝ)).Nonempty
    · obtain ⟨a, ha, haMin⟩ :=
        psi.hasCompactSupport.exists_isMinOn hsupport continuousOn_id
      obtain ⟨b, hb, hbMax⟩ :=
        psi.hasCompactSupport.exists_isMaxOn hsupport continuousOn_id
      have hmeanAmbient : (∫ t, psi t) = 0 := by
        rw [← integral_reverseTime_eq_integral_of_tsupport_subset psi.tsupport_subset]
        exact hpsi
      have hleft : ∀ {t : ℝ}, t < a → reverseTimeTestPrimitive psi t = 0 := by
        intro t hta
        by_cases ht : t ≤ 0
        · rw [reverseTimeTestPrimitive, intervalIntegral.integral_of_ge ht]
          apply neg_eq_zero.mpr
          apply integral_eq_zero_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          apply image_eq_zero_of_notMem_tsupport
          intro hxSupport
          have hxIoo := psi.tsupport_subset hxSupport
          exact (not_lt_of_ge (mem_Ioc.mp hx).2) hxIoo.1
        · have ht0 : 0 < t := lt_of_not_ge ht
          rw [reverseTimeTestPrimitive, intervalIntegral.integral_of_le ht0.le]
          apply integral_eq_zero_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          apply image_eq_zero_of_notMem_tsupport
          intro hxSupport
          exact (not_le_of_gt hta) ((haMin hxSupport).trans (mem_Ioc.mp hx).2)
      have hright : ∀ {t : ℝ}, b < t → reverseTimeTestPrimitive psi t = 0 := by
        intro t hbt
        rw [reverseTimeTestPrimitive,
          intervalIntegral.integral_eq_integral_of_support_subset]
        · exact hmeanAmbient
        · intro x hxSupport
          have hxTsupport :=
            (subset_tsupport (psi : ℝ → ℝ)) hxSupport
          exact ⟨(psi.tsupport_subset hxTsupport).1, le_of_lt ((hbMax hxTsupport).trans_lt hbt)⟩
      have hprimitiveSupport : support (reverseTimeTestPrimitive psi) ⊆ Icc a b := by
        intro t ht
        by_contra htIcc
        rcases lt_or_ge t a with hta | hta
        · exact ht (hleft hta)
        · have hbt : b < t := by
            apply lt_of_not_ge
            exact fun htb => htIcc ⟨hta, htb⟩
          exact ht (hright hbt)
      have hprimitiveTsupport : tsupport (reverseTimeTestPrimitive psi) ⊆ Icc a b := by
        rw [tsupport]
        exact closure_minimal hprimitiveSupport isClosed_Icc
      let eta : ReverseTimeScalarTest T :=
        { toFun := reverseTimeTestPrimitive psi
          contDiff' := by
            apply contDiff_infty_iff_deriv.mpr
            constructor
            · intro t
              exact (psi.contDiff.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt
            · rw [show _root_.deriv (reverseTimeTestPrimitive psi) = (psi : ℝ → ℝ) by
                  funext t
                  exact psi.contDiff.continuous.deriv_integral _ 0 t]
              exact psi.contDiff
          hasCompactSupport' := by
            exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
              hprimitiveTsupport
          tsupport_subset' := by
            intro t ht
            have htIcc := hprimitiveTsupport ht
            constructor
            · exact lt_of_lt_of_le (psi.tsupport_subset ha).1 htIcc.1
            · exact lt_of_le_of_lt htIcc.2 (psi.tsupport_subset hb).2 }
      refine ⟨eta, ?_⟩
      funext t
      exact psi.contDiff.continuous.deriv_integral _ 0 t
    · have hpsiZero : (psi : ℝ → ℝ) = 0 := by
        funext t
        apply image_eq_zero_of_notMem_tsupport
        exact fun ht => hsupport ⟨t, ht⟩
      refine ⟨0, ?_⟩
      rw [hpsiZero]
      funext t
      change _root_.deriv 0 t = 0
      rw [deriv_zero]
      rfl
  have exists_normalized_reverseTimeScalarTest :
      ∃ rho : ReverseTimeScalarTest T,
      (∫ tau, rho tau ∂reverseTimeVolume T) = 1 := by
    let raw : ContDiffBump (T / 2) :=
      { rIn := T / 8
        rOut := T / 4
        rIn_pos := by linarith
        rIn_lt_rOut := by linarith }
    let rho : ReverseTimeScalarTest T :=
      { toFun := raw.normed volume
        contDiff' := raw.contDiff_normed
        hasCompactSupport' := raw.hasCompactSupport_normed
        tsupport_subset' := by
          rw [raw.tsupport_normed_eq]
          intro t ht
          rw [Metric.mem_closedBall] at ht
          rw [Real.dist_eq] at ht
          change |t - T / 2| ≤ T / 4 at ht
          constructor <;> linarith [abs_le.mp ht] }
    refine ⟨rho, ?_⟩
    rw [integral_reverseTime_eq_integral_of_tsupport_subset rho.tsupport_subset]
    exact raw.integral_normed
  obtain ⟨rho, hrho⟩ := exists_normalized_reverseTimeScalarTest
  let c : ℝ := ∫ t, f t * rho t ∂reverseTimeVolume T
  have hpairing : ∀ phi : ReverseTimeScalarTest T,
      (∫ t, f t * phi t ∂reverseTimeVolume T) = c * (∫ t, phi t ∂reverseTimeVolume T) := by
    intro phi
    let a : ℝ := ∫ t, phi t ∂reverseTimeVolume T
    let psi := phi - a • rho
    have hpsiMean : (∫ t, psi t ∂reverseTimeVolume T) = 0 := by
      change (∫ t, phi t - a * rho t ∂reverseTimeVolume T) = 0
      rw [integral_sub phi.integrable (rho.integrable.const_mul a)]
      rw [integral_const_mul, hrho]
      simp
      ring
    obtain ⟨eta, heta⟩ :=
      exists_primitive_reverseTimeScalarTest_of_integral_eq_zero psi hpsiMean
    have hzeroEta := hzero eta
    rw [heta] at hzeroEta
    have hfp :=
      integrable_mul_reverseTimeScalarTest hf phi
    have hfar :=
      (integrable_mul_reverseTimeScalarTest hf rho).const_mul a
    have hzeroExpanded :
        (∫ t, f t * phi t ∂reverseTimeVolume T) -
          a * (∫ t, f t * rho t ∂reverseTimeVolume T) = 0 := by
      calc
        (∫ t, f t * phi t ∂reverseTimeVolume T) -
            a * (∫ t, f t * rho t ∂reverseTimeVolume T) =
            ∫ t, (f t * phi t - a * (f t * rho t)) ∂reverseTimeVolume T := by
              rw [integral_sub hfp hfar, integral_const_mul]
        _ = ∫ t, f t * psi t ∂reverseTimeVolume T := by
              apply integral_congr_ae
              filter_upwards with t
              change f t * phi t - a * (f t * rho t) =
                f t * (phi t - a * rho t)
              ring
        _ = 0 := hzeroEta
    calc
      (∫ t, f t * phi t ∂reverseTimeVolume T) =
          a * (∫ t, f t * rho t ∂reverseTimeVolume T) := by
            linarith
      _ = (∫ t, f t * rho t ∂reverseTimeVolume T) * a := mul_comm _ _
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  have hconst : Integrable (fun _ => c) (reverseTimeVolume T) := integrable_const _
  have hzeroSub : ∀ phi : ReverseTimeScalarTest T,
      (∫ t, (f t - c) * phi t ∂reverseTimeVolume T) = 0 := by
    intro phi
    calc
      (∫ t, (f t - c) * phi t ∂reverseTimeVolume T) =
          (∫ t, f t * phi t ∂reverseTimeVolume T) -
            ∫ t, c * phi t ∂reverseTimeVolume T := by
              rw [← integral_sub (integrable_mul_reverseTimeScalarTest hf phi) (phi.integrable.const_mul c)]
              apply integral_congr_ae
              filter_upwards with t
              ring
      _ = (∫ t, f t * phi t ∂reverseTimeVolume T) -
            c * (∫ t, phi t ∂reverseTimeVolume T) := by
              rw [integral_const_mul]
      _ = 0 := by rw [hpairing phi]; ring
  refine ⟨c, ?_⟩
  filter_upwards [(ae_eq_zero_of_integral_reverseTimeScalarTest T (hf.sub hconst) hzeroSub)] with t ht
  change f t - c = 0 at ht
  linarith

end HypoellipticAleksandrov.Parabolic.Dirichlet
