module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4TauIntegral

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

noncomputable def fourierEll (lam : ℝ) (x : ℝ) : ℝ :=
  fourierP lam (Bethe.kInv lam x)

noncomputable def fourierEllPrime (lam : ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    fourierPPrime lam (Bethe.kInv lam x) / Bethe.Xi lam (Bethe.kInv lam x)

noncomputable def fourierTauAlphaCont (lam α : ℝ) : ℝ :=
  Bethe.TcontFn lam α / (2 * π)

noncomputable def fourierTauXCont (lam x : ℝ) : ℝ :=
  fourierTauAlphaCont lam (Bethe.kInv lam x)

noncomputable def fourierEllTauCont (lam x : ℝ) : ℝ :=
  fourierEllPrime lam x * fourierTauXCont lam x

private theorem continuous_fourierTauAlphaCont {lam : ℝ} (hlam : 0 < lam) :
    Continuous (fourierTauAlphaCont lam) :=
  (Bethe.continuous_TcontFn hlam).div_const (2 * π)

private theorem continuous_fourierTauXCont {lam : ℝ} (hlam : 0 < lam) :
    Continuous (fourierTauXCont lam) :=
  (continuous_fourierTauAlphaCont hlam).comp (Bethe.continuous_kInv hlam)

private theorem kInv_mem_Ioo {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) : Bethe.kInv lam x ∈ Ioo (-π) π := by
  have hIcc := Bethe.kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  refine ⟨lt_of_le_of_ne hIcc.1 (Ne.symm fun h => ?_), lt_of_le_of_ne hIcc.2 fun h => ?_⟩
  · have hx' := Bethe.kMap_kInv hlam x; rw [h, Bethe.kMap_neg_pi] at hx'; linarith [hx.1]
  · have hx' := Bethe.kMap_kInv hlam x; rw [h, Bethe.kMap_pi] at hx'; linarith [hx.2]

private theorem kInv_ne_zero {lam x : ℝ} (hlam : 0 < lam) (hx : x ≠ 0) :
    Bethe.kInv lam x ≠ 0 := fun h => by
  have := Bethe.kMap_kInv hlam x
  rw [h, Bethe.kMap_zero] at this
  exact hx this.symm

private theorem hasDerivAt_kInv_of_kMap {lam x : ℝ} (hlam : 0 < lam) :
    HasDerivAt (Bethe.kInv lam)
      ((Bethe.Xi lam (Bethe.kInv lam x))⁻¹) x := by
  let α := Bethe.kInv lam x
  have hki : DifferentiableAt ℝ (Bethe.kInv lam) x :=
    (Bethe.analyticAt_kInv hlam x).differentiableAt
  have hc := (Bethe.hasDerivAt_kMap hlam α).comp x hki.hasDerivAt
  have hcomp : HasDerivAt (fun y : ℝ => y) (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) x := by
    have hfun : (fun y : ℝ => Bethe.kMap lam (Bethe.kInv lam y)) = fun y => y :=
      funext (Bethe.kMap_kInv hlam)
    change HasDerivAt (fun y : ℝ => Bethe.kMap lam (Bethe.kInv lam y))
      (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) x at hc
    simpa only [← hfun] using hc
  have hprod : Bethe.Xi lam α * deriv (Bethe.kInv lam) x = 1 := by simpa using hcomp.deriv.symm
  have hXi : Bethe.Xi lam α ≠ 0 := (Bethe.Xi_pos hlam α).ne'
  refine hki.hasDerivAt.congr_deriv ?_
  calc deriv (Bethe.kInv lam) x
    _ = (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) * (Bethe.Xi lam α)⁻¹ := by
      rw [mul_comm (Bethe.Xi lam α), mul_assoc, mul_inv_cancel₀ hXi, mul_one]
    _ = (Bethe.Xi lam α)⁻¹ := by rw [hprod, one_mul]

theorem fourierEll_hasDerivAt {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    HasDerivAt (fourierEll lam) (fourierEllPrime lam x) x := by
  have hcomp := (fourierP_hasDerivAt hlam (kInv_mem_Ioo hlam hx) (kInv_ne_zero hlam hx0)).comp x
    (hasDerivAt_kInv_of_kMap hlam)
  exact hcomp.congr_deriv (by simp [fourierEllPrime, hx0, div_eq_mul_inv])

theorem fourierEll_eq_log_norm {lam c x : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hx : x ∈ Ioo (-π) π)
    (hx0 : x ≠ 0) :
    fourierEll lam x = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hcos : Real.cos (Bethe.kInv lam x) < 1 :=
    lt_of_le_of_ne (Real.cos_le_one _) fun h => hα0 <| by
      have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hα.1])
        (by linarith [Real.pi_pos, hα.2])).mp h
      omega
  unfold fourierEll
  rw [fourierP_eq_log_norm hlam hc hcos, Bethe.kMap_kInv hlam]

private theorem continuousAt_fourierPPrime_of_mem_Ioo {lam α : ℝ}
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    ContinuousAt (fourierPPrime lam) α := by
  have hcos : Real.cos α < 1 :=
    lt_of_le_of_ne (Real.cos_le_one α) fun h => hα0 <| by
      have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hα.1])
        (by linarith [Real.pi_pos, hα.2])).mp h
      omega
  have hden1 : 0 < Real.cosh (2 * lam) - Real.cos α := by
    linarith [Real.one_le_cosh (2 * lam), Real.cos_le_one α]
  have hden2 : 0 < 1 - Real.cos α := by linarith
  have hq : ContinuousAt (fun x => (1 / 2 : ℝ) *
      (Real.sin x / (Real.cosh (2 * lam) - Real.cos x) - Real.sin x / (1 - Real.cos x))) α :=
    continuousAt_const.mul
      ((Real.continuous_sin.continuousAt.div
          (continuousAt_const.sub Real.continuous_cos.continuousAt) hden1.ne').sub
        (Real.continuous_sin.continuousAt.div
          (continuousAt_const.sub Real.continuous_cos.continuousAt) hden2.ne'))
  refine hq.congr ?_
  filter_upwards [eventually_ne_nhds hα0] with x hx
  simp [fourierPPrime, hx]

private theorem continuous_Xi_lambda {lam : ℝ} (hlam : 0 < lam) :
    Continuous (Bethe.Xi lam) := by
  unfold Bethe.Xi
  refine continuous_const.div (continuous_const.sub Real.continuous_cos) fun α => ?_
  linarith [Real.one_lt_cosh.mpr hlam.ne', Real.cos_le_one α]

private theorem measurable_fourierEllPrime {lam : ℝ} (hlam : 0 < lam) :
    Measurable (fourierEllPrime lam) := by
  have hprime : Measurable (fourierPPrime lam) := by
    unfold fourierPPrime
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  unfold fourierEllPrime
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((hprime.comp (Bethe.continuous_kInv hlam).measurable).div
      ((continuous_Xi_lambda hlam).measurable.comp (Bethe.continuous_kInv hlam).measurable))

private theorem continuousAt_fourierEllTauCont {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    ContinuousAt (fourierEllTauCont lam) x := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hquot : ContinuousAt
      (fun y => fourierPPrime lam (Bethe.kInv lam y) / Bethe.Xi lam (Bethe.kInv lam y)) x :=
    ((continuousAt_fourierPPrime_of_mem_Ioo hα hα0).comp
      (Bethe.continuous_kInv hlam).continuousAt).div
      ((continuous_Xi_lambda hlam).continuousAt.comp
        (Bethe.continuous_kInv hlam).continuousAt) (Bethe.Xi_pos hlam _).ne'
  have hprime : ContinuousAt (fourierEllPrime lam) x := by
    refine hquot.congr ?_
    filter_upwards [eventually_ne_nhds hx0] with y hy
    simp [fourierEllPrime, hy]
  exact hprime.mul (continuous_fourierTauXCont hlam).continuousAt

noncomputable def fourierXiLower (lam : ℝ) : ℝ :=
  Real.sinh lam / (Real.cosh lam + 1)

private theorem fourierXiLower_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < fourierXiLower lam :=
  div_pos (Real.sinh_pos_iff.mpr hlam) (by positivity)

private theorem fourierEllTauCont_bound {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) :
    |fourierEllTauCont lam x| ≤
      fourierTauProductControl lam / fourierXiLower lam := by
  have hC0 := fourierTauProductControl_nonneg hlam
  by_cases hx0 : x = 0
  · subst x; simp [fourierEllTauCont, fourierEllPrime]
    exact div_nonneg hC0 (fourierXiLower_pos hlam).le
  have hα := kInv_mem_Ioo hlam hx
  have htaueq := Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩)
  have hxiPos := Bethe.Xi_pos hlam (Bethe.kInv lam x)
  have hrewrite :
      fourierEllTauCont lam x =
        (fourierPPrime lam (Bethe.kInv lam x) * Bethe.tauSeries lam (Bethe.kInv lam x)) /
          Bethe.Xi lam (Bethe.kInv lam x) := by
    simp [fourierEllTauCont, fourierEllPrime, fourierTauXCont,
      fourierTauAlphaCont, hx0, ← htaueq, div_mul_eq_mul_div]
  rw [hrewrite, abs_div, abs_of_pos hxiPos]
  exact (div_le_div_of_nonneg_right
    (fourierPPrime_tauSeries_abs_bound hlam (Ioo_subset_Icc_self hα)) hxiPos.le).trans
    (div_le_div_of_nonneg_left hC0 (fourierXiLower_pos hlam)
      (Bethe.Xi_bounds hlam (Bethe.kInv lam x)).1)

private theorem kMap_mem_Ioo {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) : Bethe.kMap lam α ∈ Ioo (-π) π := by
  have hIcc := Bethe.mapsTo_kMap hlam (Ioo_subset_Icc_self hα)
  have hinj := (Bethe.strictMono_kMap hlam).injective
  refine ⟨lt_of_le_of_ne hIcc.1 (Ne.symm fun h => ?_), lt_of_le_of_ne hIcc.2 fun h => ?_⟩
  · rw [← Bethe.kMap_neg_pi lam] at h; linarith [hinj h, hα.1]
  · rw [← Bethe.kMap_pi lam] at h; linarith [hinj h, hα.2]

private theorem fourierEllTauCont_comp_mul_Xi {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α =
      fourierPPrime lam α * Bethe.tauSeries lam α := by
  have hk0 : Bethe.kMap lam α ≠ 0 := fun h => hα0 <|
    (Bethe.strictMono_kMap hlam).injective (by rw [Bethe.kMap_zero]; exact h)
  have htaueq := Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩)
  unfold fourierEllTauCont fourierEllPrime fourierTauXCont fourierTauAlphaCont
  rw [ite_eq_right hk0, Bethe.kInv_kMap hlam, ← htaueq]
  field_simp [(Bethe.Xi_pos hlam α).ne']

private theorem fourierAlphaSourceIntegrand_ae {lam : ℝ} (hlam : 0 < lam) :
    (fun α => fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α) =ᵐ[
      volume.restrict (Icc (-π) π)]
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume π),
    ae_restrict_of_ae (Measure.ae_ne volume (-π)),
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hαp hαm hα0
  exact fourierEllTauCont_comp_mul_Xi hlam
    ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩ hα0

private theorem fourierAlphaSourceIntegrand_integrableOnIcc {lam : ℝ}
    (hlam : 0 < lam) :
    IntegrableOn (fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
      (Icc (-π) π) volume := by
  have hprime : Measurable (fourierPPrime lam) := by
    unfold fourierPPrime
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  have hcont : Measurable (fun α => fourierPPrime lam α * fourierTauAlphaCont lam α) :=
    hprime.mul (continuous_fourierTauAlphaCont hlam).measurable
  have hae : (fun α => fourierPPrime lam α * fourierTauAlphaCont lam α) =ᵐ[
      volume.restrict (Icc (-π) π)]
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume π),
      ae_restrict_of_ae (Measure.ae_ne volume (-π))] with α hα hαp hαm
    rw [Bethe.tauSeries_eq hlam (abs_lt.mpr
      ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩), fourierTauAlphaCont]
  refine (Measure.integrableOn_of_bounded (M := fourierTauProductControl lam) (by simp)
    hcont.aestronglyMeasurable ?_).congr_fun_ae hae
  filter_upwards [ae_restrict_mem measurableSet_Icc, hae] with α hα hαeq
  rw [hαeq, Real.norm_eq_abs]
  exact fourierPPrime_tauSeries_abs_bound hlam hα

private theorem fourierEllTauCont_integrableOnIcc {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume := by
  refine Measure.integrableOn_of_bounded
    (M := fourierTauProductControl lam / fourierXiLower lam) (by simp)
    ((measurable_fourierEllPrime hlam).mul
      (continuous_fourierTauXCont hlam).measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume π),
    ae_restrict_of_ae (Measure.ae_ne volume (-π))] with x hx hxp hxm
  rw [Real.norm_eq_abs]
  exact fourierEllTauCont_bound hlam
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxm), lt_of_le_of_ne hx.2 hxp⟩

private theorem fourierSourceIntegrand_ae {lam : ℝ} (hlam : 0 < lam) :
    (fun x => fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =ᵐ[
      volume.restrict (uIoc (-π) π)] (fourierEllTauCont lam) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume π)] with x hx hxp
  have hxIoc : x ∈ Ioc (-π) π := by
    simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hx
  have hxIoo : x ∈ Ioo (-π) π := ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxp⟩
  have hα := kInv_mem_Ioo hlam hxIoo
  have hparam : Bethe.lamOf (-Real.cosh lam) = lam := (Bethe.eq_lamOf hlam (by simp)).symm
  change fourierEllPrime lam x * Bethe.tauSeries (Bethe.lamOf (-Real.cosh lam))
    (Bethe.kInv (Bethe.lamOf (-Real.cosh lam)) x) = _
  rw [hparam, Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩)]
  rfl

private theorem fourier_source_substitution {lam a b : ℝ} (hlam : 0 < lam)
    (hab : a ≤ b) (hsub : Icc a b ⊆ Icc (-π) π) (h0 : (0 : ℝ) ∉ Ioo a b)
    (hg : IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume)
    (hqInt : IntegrableOn
      (fun α => (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α)
      (Icc (-π) π) volume) :
    ∫ α in a..b, (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α =
      ∫ x in Bethe.kMap lam a..Bethe.kMap lam b, fourierEllTauCont lam x := by
  have hf : ContinuousOn (Bethe.kMap lam) (uIcc a b) :=
    (Bethe.continuous_kMap hlam).continuousOn
  have hff' : ∀ α ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt (Bethe.kMap lam) (Bethe.Xi lam α) (Ioi α) α :=
    fun α _ => (Bethe.hasDerivAt_kMap hlam α).hasDerivWithinAt
  have hgcont : ContinuousOn (fourierEllTauCont lam)
      (Bethe.kMap lam '' Ioo (min a b) (max a b)) := by
    rintro _ ⟨α, hα, rfl⟩
    have hαab : α ∈ Ioo a b := by simpa [min_eq_left hab, max_eq_right hab] using hα
    have hαfull : α ∈ Ioo (-π) π :=
      ⟨lt_of_le_of_lt (hsub ⟨le_rfl, hab⟩).1 hαab.1,
        lt_of_lt_of_le hαab.2 (hsub ⟨hab, le_rfl⟩).2⟩
    have hx0 : Bethe.kMap lam α ≠ 0 := fun h => h0 <| by
      have := (Bethe.strictMono_kMap hlam).injective (h.trans (Bethe.kMap_zero lam).symm)
      rwa [← this]
    exact (continuousAt_fourierEllTauCont hlam (kMap_mem_Ioo hlam hαfull) hx0).continuousWithinAt
  have hG1 : IntegrableOn (fourierEllTauCont lam) (Bethe.kMap lam '' uIcc a b) volume := by
    refine hg.mono_set ?_
    rintro _ ⟨α, hα, rfl⟩
    rw [uIcc_of_le hab] at hα
    exact Bethe.mapsTo_kMap hlam (hsub hα)
  have hG2 : IntegrableOn
      (fun α => (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α)
      (uIcc a b) volume := by
    rw [uIcc_of_le hab]; exact hqInt.mono_set hsub
  exact intervalIntegral.integral_comp_mul_deriv''' hf hff' hgcont hG1 hG2

private theorem fourierEllPrime_tau_integral_eq_fourierPPrime {lam : ℝ} (hlam : 0 < lam) :
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
      ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := by
  let q : ℝ → ℝ := fun α =>
    (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α
  have hqf : q =ᵐ[volume.restrict (Icc (-π) π)]
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) :=
    fourierAlphaSourceIntegrand_ae hlam
  have hqInt : IntegrableOn q (Icc (-π) π) volume :=
    (fourierAlphaSourceIntegrand_integrableOnIcc hlam).congr_fun_ae hqf.symm
  have hgInt := fourierEllTauCont_integrableOnIcc hlam
  have hpi : (0 : ℝ) ≤ π := Real.pi_pos.le
  have hnpi : (-π : ℝ) ≤ 0 := by linarith
  have hsubL : Icc (-π) 0 ⊆ Icc (-π) π := fun _ h => ⟨h.1, h.2.trans hpi⟩
  have hsubR : Icc 0 π ⊆ Icc (-π) π := fun _ h => ⟨hnpi.trans h.1, h.2⟩
  have hL := fourier_source_substitution hlam hnpi hsubL (by simp) hgInt hqInt
  have hR := fourier_source_substitution hlam hpi hsubR (by simp) hgInt hqInt
  rw [Bethe.kMap_neg_pi, Bethe.kMap_zero] at hL
  rw [Bethe.kMap_zero, Bethe.kMap_pi] at hR
  have hqL : IntervalIntegrable q volume (-π) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hnpi]
    exact hqInt.mono_set (Ioc_subset_Icc_self.trans hsubL)
  have hqR : IntervalIntegrable q volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
    exact hqInt.mono_set (Ioc_subset_Icc_self.trans hsubR)
  have hgL : IntervalIntegrable (fourierEllTauCont lam) volume (-π) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hnpi]
    exact hgInt.mono_set (Ioc_subset_Icc_self.trans hsubL)
  have hgR : IntervalIntegrable (fourierEllTauCont lam) volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
    exact hgInt.mono_set (Ioc_subset_Icc_self.trans hsubR)
  have hqAlpha : ∫ α in (-π)..π, q α =
      ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (neg_le_self hpi)]
    exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hqf
  calc
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
        ∫ x in (-π)..π, fourierEllTauCont lam x :=
      intervalIntegral.integral_congr_ae_restrict (fourierSourceIntegrand_ae hlam)
    _ = (∫ x in (-π)..0, fourierEllTauCont lam x) +
        ∫ x in 0..π, fourierEllTauCont lam x :=
      (intervalIntegral.integral_add_adjacent_intervals hgL hgR).symm
    _ = (∫ α in (-π)..0, q α) + ∫ α in 0..π, q α := by rw [← hL, ← hR]
    _ = ∫ α in (-π)..π, q α := intervalIntegral.integral_add_adjacent_intervals hqL hqR
    _ = ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := hqAlpha

theorem fourierRatioExponent {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      -r * Real.log (abs (-Real.cosh lam)) +
          r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        -r * (lam + 2 * S) := by
  obtain ⟨S, hS, hCorr⟩ := fourierPPrime_tauSeries_integral hlam
  obtain ⟨S', hS', hIdentity⟩ := identity43 lam hlam
  have hSS' : S = S' := tendsto_nhds_unique hS hS'
  have hEq := tendsto_nhds_unique
    ((tendsto_const_nhds (x := Real.log (Real.cosh lam))).sub hCorr) hIdentity
  rw [← hSS'] at hEq
  refine ⟨S, hS, ?_⟩
  rw [fourierEllPrime_tau_integral_eq_fourierPPrime hlam, abs_neg,
    abs_of_pos (Real.cosh_pos lam)]
  linear_combination -r * hEq

end PottsDiscontinuity
