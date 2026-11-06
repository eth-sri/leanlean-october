module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4TauIntegral

/-!
# The source-coordinate logarithmic derivative integral

This file transports the Abel-summed Fourier computation from the `α` coordinate to the
source coordinate `x = k(α)`.  The logarithmic point is handled by splitting the substitution
at zero; the literal and continuous representatives of `τ` agree almost everywhere.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-- The source profile `ℓ(x) = log |M(e^{ix})|`, pulled back from the explicit `P` profile. -/
noncomputable def fourierEll (lam x : ℝ)  :=
  fourierP lam (Bethe.kInv lam x)

/-- The source derivative representative obtained by differentiating `P = ℓ ∘ k` away from zero.
Its value at the logarithmic point is immaterial to interval integrals. -/
noncomputable def fourierEllPrime (lam x : ℝ)  :=
  if x = 0 then 0 else
    fourierPPrime lam (Bethe.kInv lam x) / Bethe.Xi lam (Bethe.kInv lam x)

/-- The ordered partial sums of the explicit Section 4 series for `τ(k(α))`. -/
noncomputable def fourierTauPartial (lam α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
      Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
      Real.sin (((n + 1 : ℕ) : ℝ) * α)

/-- The literal ordered series for `τ(k(α))`, expressed as the limit of its partial sums. -/
noncomputable def fourierTauSeries (lam α : ℝ) : ℝ :=
  limUnder atTop (fourierTauPartial lam α)



/-- The continuous representative of τ(k(α)) on the circle. -/
noncomputable def fourierTauAlphaCont (lam α : ℝ) : ℝ :=
  Bethe.TcontFn lam α / (2 * π)

/-- The continuous representative of source τ(x), expressed through k⁻¹. -/
noncomputable def fourierTauXCont (lam x : ℝ)  :=
  fourierTauAlphaCont lam (Bethe.kInv lam x)

/-- The actual ordered series representative of source τ(x). -/
noncomputable def fourierTauXSeries (lam x : ℝ)  :=
  fourierTauSeries lam (Bethe.kInv lam x)

/-- The continuous source-coordinate integrand used at the single removable point. -/
noncomputable def fourierEllTauCont (lam x : ℝ)  :=
  fourierEllPrime lam x * fourierTauXCont lam x

private theorem continuous_fourierTauAlphaCont {lam : ℝ} (hlam : 0 < lam) :
    Continuous (fourierTauAlphaCont lam) := Continuous.div_const (Bethe.continuous_TcontFn hlam) (2 * π)

private theorem continuous_fourierTauXCont {lam : ℝ} (hlam : 0 < lam) :
    Continuous (fourierTauXCont lam) := (continuous_fourierTauAlphaCont hlam).comp (Bethe.continuous_kInv hlam)

section

variable {lam x : ℝ} (hlam : 0 < lam)
include hlam

private theorem kInv_mem_Ioo 
    (hx : x ∈ Ioo (-π) π) : Bethe.kInv lam x ∈ Ioo (-π) π := by
  have hIcc := Bethe.kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  
  
  exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm (by
                                           intro h
                                           have hx' := Bethe.kMap_kInv hlam x
                                           rw [h, Bethe.kMap_neg_pi] at hx'
                                           linarith [hx.1])),
    lt_of_le_of_ne hIcc.2 (by
                             intro h
                             have hx' := Bethe.kMap_kInv hlam x
                             rw [h, Bethe.kMap_pi] at hx'
                             linarith [hx.2])⟩

private theorem fourierTauXSeries_eq_cont 
    (hx : x ∈ Ioo (-π) π) : fourierTauXSeries lam x = fourierTauXCont lam x := Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨
                                                                           (kInv_mem_Ioo hlam hx).1, (kInv_mem_Ioo hlam hx).2⟩)

private theorem kInv_ne_zero  (hx : x ≠ 0) :
    Bethe.kInv lam x ≠ 0 := by
  intro h
  have := Bethe.kMap_kInv hlam x
  rw [h, Bethe.kMap_zero] at this
  exact hx this.symm

/-- The inverse map has derivative `1 / Ξ_λ(k⁻¹(x))`. -/
private theorem hasDerivAt_kInv_of_kMap  :
    HasDerivAt (Bethe.kInv lam)
       (Bethe.Xi lam (Bethe.kInv lam x))⁻¹  x := by
  let α := Bethe.kInv lam x
  
  
  have hki  :=
    (Bethe.analyticAt_kInv hlam x).differentiableAt
  have hc := (Bethe.hasDerivAt_kMap hlam α).comp x  hki.hasDerivAt 
  have hcomp : HasDerivAt (fun y  => y)
      (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) x := by
    have hfun  :=
      funext (Bethe.kMap_kInv hlam)
    change HasDerivAt (fun y  => Bethe.kMap lam (Bethe.kInv lam y))
      (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) x at hc
    simp_all
  have hprod : Bethe.Xi lam α * deriv (Bethe.kInv lam) x = 1 := by
    have := hcomp.deriv
    simpa using this.symm
  
  have hderiv : deriv (Bethe.kInv lam) x = (Bethe.Xi lam α)⁻¹ := by
    grind
  convert hki.hasDerivAt.congr_deriv hderiv using 1

/-- Away from the logarithmic singularity, `fourierEll` has the source derivative. -/
theorem fourierEll_hasDerivAt 
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    HasDerivAt (fourierEll lam) (fourierEllPrime lam x) x := by
  
  
  
  
  have hcomp := (fourierP_hasDerivAt hlam (kInv_mem_Ioo hlam hx) (kInv_ne_zero hlam hx0)).comp x (hasDerivAt_kInv_of_kMap (lam := lam) (x := x) hlam)
  have hderiv : fourierPPrime lam (Bethe.kInv lam x) *
      (Bethe.Xi lam (Bethe.kInv lam x))⁻¹ = fourierEllPrime lam x := by
    simp [fourierEllPrime, hx0, div_eq_mul_inv]
  aesop

end

/-- The profile fourierEll is the source logarithm log |M(e^(ix))| on the punctured
fundamental interval, with c² = 2 - 2Δ = 2 + 2 cosh λ. -/
theorem fourierEll_eq_log_norm {lam c x : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hx : x ∈ Ioo (-π) π)
    (hx0 : x ≠ 0) :
    fourierEll lam x = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
  have hα := kInv_mem_Ioo hlam hx
  
  
  calc
    fourierEll lam x = fourierP lam (Bethe.kInv lam x) := rfl
    _ = Real.log ‖BetheAnsatz.M c
        (Complex.exp (I *  Bethe.kMap lam (Bethe.kInv lam x) ))‖ :=
      fourierP_eq_log_norm hlam hc (by
                                      
                                      exact lt_of_le_of_ne (Real.cos_le_one _) (by
                                                                                  intro h
                                                                                  have hαbounds : -(2 * π) < Bethe.kInv lam x ∧ Bethe.kInv lam x < 2 * π := by
                                                                                    grind
                                                                                  have hperiod := (Real.cos_eq_one_iff_of_lt_of_lt hαbounds.1 hαbounds.2).mp h
                                                                                  exact (kInv_ne_zero hlam hx0) (by omega)))
    _ = Real.log ‖BetheAnsatz.M c (Complex.exp (I *  x ))‖ := by
      rw [Bethe.kMap_kInv hlam]

private theorem fourier_cos_lt_one_of_mem_Ioo {α : ℝ} (hα : α ∈ Ioo (-π) π)
    (hα0 : α ≠ 0) : Real.cos α < 1 := lt_of_le_of_ne (Real.cos_le_one α) (by
                                                                            intro h
                                                                            have hbounds : -(2 * π) < α ∧ α < 2 * π := by
                                                                              grind
                                                                            have hperiod := (Real.cos_eq_one_iff_of_lt_of_lt hbounds.1 hbounds.2).mp h
                                                                            exact hα0 (by omega))

private theorem continuousAt_fourierPPrime_of_mem_Ioo {lam α : ℝ}
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    ContinuousAt (fourierPPrime lam) α := by
  have hcos := fourier_cos_lt_one_of_mem_Ioo hα hα0
  have hden1 : 0 < Real.cosh (2 * lam) - Real.cos α := by
    have hcosh : 1 ≤ Real.cosh (2 * lam) := Real.one_le_cosh _
    linarith 
  have hden2 : 0 < 1 - Real.cos α := by linarith
  let q  := fun x =>  1 / 2  *
    (Real.sin x / (Real.cosh (2 * lam) - Real.cos x) -
      Real.sin x / (1 - Real.cos x))
  have hq : ContinuousAt q α := by
    
    
    exact continuousAt_const.mul ((Real.continuous_sin.continuousAt.div
                                     (continuousAt_const.sub Real.continuous_cos.continuousAt) hden1.ne').sub (Real.continuous_sin.continuousAt.div
                                             (continuousAt_const.sub Real.continuous_cos.continuousAt) hden2.ne'))
  have hEq : fourierPPrime lam =ᶠ[𝓝 α] q := by
    filter_upwards [eventually_ne_nhds hα0] with x hx
    simp [fourierPPrime, q, hx]
  exact hq.congr hEq.symm

private theorem continuous_Xi_lambda {lam : ℝ} (hlam : 0 < lam) :
    Continuous (Bethe.Xi lam) := by
  
  refine continuous_const.div (continuous_const.sub Real.continuous_cos) ?_
  intro α
  have hcosh  := Real.one_lt_cosh.mpr hlam.ne'
  linarith [Real.cos_le_one α]

private theorem measurable_fourierEllPrime {lam : ℝ} (hlam : 0 < lam) :
    Measurable (fourierEllPrime lam) := by
  have hprime : Measurable (fourierPPrime lam) := by
    
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Measurable.div (hprime.comp (Bethe.continuous_kInv hlam).measurable)
      ((continuous_Xi_lambda hlam).measurable.comp
        (Bethe.continuous_kInv hlam).measurable))

section

variable {lam x : ℝ} (hlam : 0 < lam) (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0)
include hlam hx hx0

private theorem continuousAt_fourierEllPrime  :
    ContinuousAt (fourierEllPrime lam) x := by
  
  
  
  
  
  
  have hEq : fourierEllPrime lam =ᶠ[𝓝 x]
       fun y => fourierPPrime lam (Bethe.kInv lam y) /
        Bethe.Xi lam (Bethe.kInv lam y)  := by
    filter_upwards [eventually_ne_nhds hx0] with y hy
    simp [fourierEllPrime, hy]
  exact (((continuousAt_fourierPPrime_of_mem_Ioo (kInv_mem_Ioo hlam hx) (kInv_ne_zero hlam hx0)).comp
              (Bethe.continuous_kInv hlam).continuousAt).div ((continuous_Xi_lambda hlam).continuousAt.comp
                                      (Bethe.continuous_kInv hlam).continuousAt)  (Bethe.Xi_pos hlam _).ne' ).congr hEq.symm

private theorem continuousAt_fourierEllTauCont  :
    ContinuousAt (fourierEllTauCont lam) x := ContinuousAt.mul (continuousAt_fourierEllPrime hlam hx hx0) (Continuous.continuousAt (continuous_fourierTauXCont hlam))

end

noncomputable def fourierXiLower (lam : ℝ) : ℝ :=
  Real.sinh lam / (Real.cosh lam + 1)

private theorem fourierXiLower_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < fourierXiLower lam := div_pos (Real.sinh_pos_iff.mpr hlam) (by positivity)

private theorem fourierEllTauCont_bound {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) :
    |fourierEllTauCont lam x| ≤
      fourierTauProductControl lam / fourierXiLower lam := by
  have hC0 := fourierTauProductControl_nonneg hlam
  by_cases hx0 : x = 0
  · subst x
    simp [fourierEllTauCont, fourierEllPrime]
    exact div_nonneg hC0 (fourierXiLower_pos hlam).le
  have hα := kInv_mem_Ioo hlam hx
  
  
  have htaueq := Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩)
  have hxiPos := Bethe.Xi_pos hlam (Bethe.kInv lam x)
  
  have hrewrite :
      fourierEllTauCont lam x =
         fourierPPrime lam (Bethe.kInv lam x) /
          Bethe.Xi lam (Bethe.kInv lam x)  *
          Bethe.tauSeries lam (Bethe.kInv lam x) := by
    grind +locals
  rw [hrewrite]
  
  have hdiv :
      |(fourierPPrime lam (Bethe.kInv lam x) /
          Bethe.Xi lam (Bethe.kInv lam x)) *
          Bethe.tauSeries lam (Bethe.kInv lam x)| =
        |fourierPPrime lam (Bethe.kInv lam x) *
          Bethe.tauSeries lam (Bethe.kInv lam x)| /
          Bethe.Xi lam (Bethe.kInv lam x) := by
    have heq :  fourierPPrime lam (Bethe.kInv lam x) /
        Bethe.Xi lam (Bethe.kInv lam x)  *
        Bethe.tauSeries lam (Bethe.kInv lam x) =
         fourierPPrime lam (Bethe.kInv lam x) *
          Bethe.tauSeries lam (Bethe.kInv lam x)  /
          Bethe.Xi lam (Bethe.kInv lam x) := by
      field_simp 
    rw [heq, abs_div, abs_of_pos hxiPos]
  rw [hdiv]
  calc
    |fourierPPrime lam (Bethe.kInv lam x) *
        Bethe.tauSeries lam (Bethe.kInv lam x)| /
        Bethe.Xi lam (Bethe.kInv lam x) ≤ fourierTauProductControl lam /
          Bethe.Xi lam (Bethe.kInv lam x) :=
      div_le_div_of_nonneg_right (fourierPPrime_tauSeries_abs_bound hlam (Ioo_subset_Icc_self hα)) hxiPos.le
    _ ≤ fourierTauProductControl lam / fourierXiLower lam :=
      div_le_div_of_nonneg_left hC0 (fourierXiLower_pos hlam)  (Bethe.Xi_bounds hlam (Bethe.kInv lam x)).1 

section

variable {lam α : ℝ} (hlam : 0 < lam) (hα : α ∈ Ioo (-π) π)
include hlam hα

private theorem kMap_mem_Ioo  : Bethe.kMap lam α ∈ Ioo (-π) π := by
  have hIcc := Bethe.mapsTo_kMap hlam (Ioo_subset_Icc_self hα)
  have hinj := (Bethe.strictMono_kMap hlam).injective
  
  
  exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm (by
                                           intro h
                                           have heq : Bethe.kMap lam α = Bethe.kMap lam (-π) := by rw [Bethe.kMap_neg_pi]; exact h
                                           grind)),
    lt_of_le_of_ne hIcc.2 (by
                             intro h
                             have heq : Bethe.kMap lam α = Bethe.kMap lam π := by rw [Bethe.kMap_pi]; exact h
                             grind)⟩

private theorem fourierEllTauCont_comp_mul_Xi  (hα0 : α ≠ 0) :
    fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α =
      fourierPPrime lam α * Bethe.tauSeries lam α := by
  
  
  unfold fourierEllTauCont fourierEllPrime fourierTauXCont fourierTauAlphaCont
  rw [ite_eq_right  fun h =>
                      hα0
                        (StrictMono.injective (Bethe.strictMono_kMap hlam)
                          (Eq.mpr (congrArg (Eq (Bethe.kMap lam α)) (Bethe.kMap_zero lam)) h)) , Bethe.kInv_kMap hlam, ←  Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩) ]
  field_simp [(Bethe.Xi_pos hlam α).ne']

end

private theorem measurable_fourierPPrime {lam : ℝ} :
    Measurable (fourierPPrime lam) := Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private theorem fourierTauAlphaCont_ae {lam : ℝ} (hlam : 0 < lam) :
    Bethe.tauSeries lam =ᵐ[volume.restrict (Icc (-π) π)]
      fourierTauAlphaCont lam := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume π),
    ae_restrict_of_ae (Measure.ae_ne volume (-π))] with α hα hαp hαm
  have hαoo : α ∈ Ioo (-π) π :=
    by
      grind
  exact Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hαoo.1, hαoo.2⟩)

private theorem fourierSourceTau_eq_cont {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) :
    Bethe.tau (-Real.cosh lam) x = fourierTauXCont lam x := by
  
  change Bethe.tauSeries (Bethe.lamOf (-Real.cosh lam))
    (Bethe.kInv (Bethe.lamOf (-Real.cosh lam)) x) = _
  rw [ (Bethe.eq_lamOf hlam (by simp)).symm ]
  exact fourierTauXSeries_eq_cont hlam hx

section

variable {lam : ℝ} (hlam : 0 < lam)
include hlam

private theorem fourierAlphaSourceIntegrand_ae  :
    (fun α => fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α) =ᵐ[
      volume.restrict (Icc (-π) π)]
       fun α => fourierPPrime lam α * Bethe.tauSeries lam α  := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume π),
    ae_restrict_of_ae (Measure.ae_ne volume (-π)),
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hαp hαm hα0
  
  exact fourierEllTauCont_comp_mul_Xi hlam  ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩  hα0

private theorem fourierAlphaSourceIntegrand_integrableOnIcc  :
    IntegrableOn (fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
      (Icc (-π) π) volume := by
  let C := fourierTauProductControl lam
  
  have hC : ∀ α ∈ Icc (-π) π,
      |fourierPPrime lam α * Bethe.tauSeries lam α| ≤ C := fun α => fourierPPrime_tauSeries_abs_bound hlam
  let μ  := volume.restrict (Icc (-π) π)
  
  
  have hbound : ∀ᵐ α ∂μ,
      ‖fourierPPrime lam α * Bethe.tauSeries lam α‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with α hα
    simp_all
  
  
  have hIntUniv : IntegrableOn
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) univ μ := Measure.integrableOn_of_bounded (by simp ) (AEStronglyMeasurable.congr (Measurable.aestronglyMeasurable ((measurable_fourierPPrime (lam := lam)).mul
                                                                                                                                                                                       (continuous_fourierTauAlphaCont hlam).measurable))
                                                                                                                        (EventuallyEq.symm
                                                                                                                          (Eventually.mono (fourierTauAlphaCont_ae hlam) fun α => congrArg (HMul.hMul (fourierPPrime lam α))))) (by
                                                                                                                        simpa only [Measure.restrict_univ] using hbound)
  
  exact  by
           aesop 

private theorem fourierEllTauCont_integrableOnIcc  :
    IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume := by
  have hfinite : volume (Icc (-π) π) ≠ ⊤ := by simp
  
  
  
  exact (Measure.integrableOn_of_bounded hfinite ((measurable_fourierEllPrime hlam).mul
                                                        (continuous_fourierTauXCont hlam).measurable).aestronglyMeasurable (by
                                                                                 filter_upwards [ae_restrict_mem measurableSet_Icc,
                                                                                   ae_restrict_of_ae (Measure.ae_ne volume π),
                                                                                   ae_restrict_of_ae (Measure.ae_ne volume (-π))] with x hx hxp hxm
                                                                                 
                                                                                 
                                                                                 exact fourierEllTauCont_bound hlam (⟨lt_of_le_of_ne hx.1 (Ne.symm hxm), lt_of_le_of_ne hx.2 hxp⟩)))

private theorem fourierSourceIntegrand_ae  :
    (fun x => fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =ᵐ[
      volume.restrict (uIoc (-π) π)]  fourierEllTauCont lam  := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume π)] with x hx hxp
  have hxIoc : x ∈ Ioc (-π) π := by
    simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hx
  
  
  exact congrArg (fun y => fourierEllPrime lam x * y) (fourierSourceTau_eq_cont hlam  ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxp⟩ )

private theorem kMap_left_image_subset  :
    Bethe.kMap lam '' Icc (-π) 0 ⊆ Icc (-π) π := by
  intro x hx
  rcases hx with ⟨α, hα, rfl⟩
  apply Bethe.mapsTo_kMap hlam
  grind

private theorem kMap_right_image_subset  :
    Bethe.kMap lam '' Icc 0 π ⊆ Icc (-π) π := by
  intro x hx
  rcases hx with ⟨α, hα, rfl⟩
  apply Bethe.mapsTo_kMap hlam
  grind

section

variable (q : ℝ → ℝ) (hq : ∀ α, q α =
      fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α) (hg : IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume) (hqInt : IntegrableOn q (Icc (-π) π) volume)
include hq hg hqInt

private theorem fourier_source_substitution_left 
     :
    ∫ α in (-π)..0, q α = ∫ x in Bethe.kMap lam (-π)..0, fourierEllTauCont lam x := by
  have hle :  -π  ≤ 0 := by linarith [Real.pi_pos]
  
  
  
  
  
  have hsub := intervalIntegral.integral_comp_mul_deriv'''
    (a := -π) (b := 0) (f := Bethe.kMap lam) (f' := Bethe.Xi lam)
    (g := fourierEllTauCont lam) ((Bethe.continuous_kMap hlam).continuousOn.mono (Set.subset_univ _)) (fun α hα => HasDerivAt.hasDerivWithinAt (Bethe.hasDerivAt_kMap hlam α)) (by
                                            intro x hx
                                            rcases hx with ⟨α, hα, rfl⟩
                                            have hαleft : α ∈ Ioo (-π) 0 := by
                                              simp_all
                                            have hαfull : α ∈ Ioo (-π) π := by
                                              grind
                                            
                                            
                                            exact (continuousAt_fourierEllTauCont hlam (kMap_mem_Ioo hlam hαfull) (by
                                                                                                                                   exact fun hx0 =>
                                                                                                                                           ne_of_lt hαleft.right
                                                                                                                                             (StrictMono.injective (Bethe.strictMono_kMap hlam)
                                                                                                                                               (Eq.mpr (congrArg (Eq (Bethe.kMap lam α)) (Bethe.kMap_zero lam)) hx0)))).continuousWithinAt) (by
                                                   have hG1' := hg.mono_set (kMap_left_image_subset hlam)
                                                   simp_all) (by
                                                       
                                                       
                                                       simpa [ funext hq , uIcc_of_le hle] using  hqInt.mono_set (by
                                                                                              grind) )
  
  
  
  exact (intervalIntegral.integral_congr  fun α _ => hq α ).trans (by
                           simpa [Bethe.kMap_zero] using hsub)

private theorem fourier_source_substitution_right 
     :
    ∫ α in 0..π, q α = ∫ x in 0..Bethe.kMap lam π, fourierEllTauCont lam x := by
  have hle :  0  ≤ π := by linarith [Real.pi_pos]
  
  
  
  
  
  have hsub := intervalIntegral.integral_comp_mul_deriv'''
    (a := 0) (b := π) (f := Bethe.kMap lam) (f' := Bethe.Xi lam)
    (g := fourierEllTauCont lam) ((Bethe.continuous_kMap hlam).continuousOn.mono (Set.subset_univ _)) (fun α hα => HasDerivAt.hasDerivWithinAt (Bethe.hasDerivAt_kMap hlam α)) (by
                                            intro x hx
                                            rcases hx with ⟨α, hα, rfl⟩
                                            have hαright : α ∈ Ioo 0 π := by
                                              simp_all
                                            have hαfull : α ∈ Ioo (-π) π := by
                                              grind
                                            
                                            
                                            exact (continuousAt_fourierEllTauCont hlam (kMap_mem_Ioo hlam hαfull) (by
                                                                                                                                   exact fun hx0 =>
                                                                                                                                           ne_of_gt hαright.left
                                                                                                                                             (StrictMono.injective (Bethe.strictMono_kMap hlam)
                                                                                                                                               (Eq.mpr (congrArg (Eq (Bethe.kMap lam α)) (Bethe.kMap_zero lam)) hx0)))).continuousWithinAt) (by
                                                   have hG1' := hg.mono_set (kMap_right_image_subset hlam)
                                                   simp_all) (by
                                                       
                                                       
                                                       simpa [ funext hq , uIcc_of_le hle] using  hqInt.mono_set (by
                                                                                              grind) )
  
  
  
  exact (intervalIntegral.integral_congr  fun α _ => hq α ).trans (by
                           simpa [Bethe.kMap_zero] using hsub)

end

/-- Change of variables from the source coordinate to α identifies the original integral
of ℓ′τ with the explicitly regularized α-integral.  The literal series values at the endpoints
are retained; replacing τ by its continuous representative changes the integrand only on a
null set. -/
theorem fourierEllPrime_tau_integral_eq_fourierPPrime  :
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
      ∫ α in (-π)..π, fourierPPrime lam α * fourierTauSeries lam α := by
  let q  := fun α =>
    fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α
  
  
  have hqf : q =ᵐ[volume.restrict (Icc (-π) π)]
       fun α => fourierPPrime lam α * Bethe.tauSeries lam α  := by
    grind [fourierAlphaSourceIntegrand_ae]
  have hqInt  :=
    (fourierAlphaSourceIntegrand_integrableOnIcc hlam).congr_fun_ae hqf.symm
  have hgInt := fourierEllTauCont_integrableOnIcc hlam
  
  
  
  
  have hgL : IntervalIntegrable (fourierEllTauCont lam) volume
      (Bethe.kMap lam (-π)) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by
      rw [Bethe.kMap_neg_pi]
      linarith [Real.pi_pos])]
    exact hgInt.mono_set  fun x hx => ⟨le_of_lt (by simpa only [Bethe.kMap_neg_pi] using hx.1),
                      le_trans hx.2 (by linarith [Real.pi_pos])⟩ 
  have hgR : IntervalIntegrable (fourierEllTauCont lam) volume
      0 (Bethe.kMap lam π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by
      rw [Bethe.kMap_pi]
      exact Real.pi_pos.le)]
    
    exact hgInt.mono_set (by
                            intro x hx
                            constructor
                            · linarith [hx.1, Real.pi_pos]
                            · simpa only [Bethe.kMap_pi] using hx.2)
  have hqAlphaAE : q =ᵐ[volume.restrict (uIoc (-π) π)]
       fun α => fourierPPrime lam α * Bethe.tauSeries lam α  := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume π),
      ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hαpi hα0
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    have hαfull : α ∈ Ioo (-π) π :=
      by
        grind
    simpa  using
      fourierEllTauCont_comp_mul_Xi hlam hαfull hα0
  have hqAlpha  :=
    intervalIntegral.integral_congr_ae_restrict hqAlphaAE
  have hgSplit := intervalIntegral.integral_add_adjacent_intervals hgL hgR
  
  calc
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
        ∫ x in (-π)..π, fourierEllTauCont lam x :=
      intervalIntegral.integral_congr_ae_restrict (fourierSourceIntegrand_ae hlam)
    _ = (∫ x in Bethe.kMap lam (-π)..0, fourierEllTauCont lam x) +
        ∫ x in 0..Bethe.kMap lam π, fourierEllTauCont lam x := by
      simpa only [Bethe.kMap_neg_pi, Bethe.kMap_pi] using hgSplit.symm
    _ = (∫ α in (-π)..0, q α) + ∫ α in 0..π, q α := by
      rw [←  fourier_source_substitution_left hlam q (by
                                                                      intro α
                                                                      rfl) hgInt hqInt , ←  fourier_source_substitution_right hlam q (by
                                                                                intro α
                                                                                rfl) hgInt hqInt ]
    _ = ∫ α in (-π)..π, q α :=  intervalIntegral.integral_add_adjacent_intervals (by
                                                                                    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
                                                                                    exact hqInt.mono_set (by
                                                                                      grind)) (by
                                                                                        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
                                                                                        exact hqInt.mono_set (by
                                                                                          grind)) 
    _ = ∫ α in (-π)..π, fourierPPrime lam α * fourierTauSeries lam α := by
      assumption

/-- The source-coordinate integral is exactly the correction term in (4.3), in the
ordered-partial-sum sense.  The limit `S` is the one from the alternating tanh series. -/
theorem fourierEllPrime_tau_integral_value  :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
       Real.log (abs (-Real.cosh lam)) -
         ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x  =
        lam + 2 * S  := by
  obtain ⟨S, hS, hCorr⟩ := fourierPPrime_tauSeries_integral hlam
  obtain ⟨S', hS', hIdentity⟩ := identity43 lam hlam
  
  refine ⟨S, hS, ?_⟩
  
  
  rw [ fourierEllPrime_tau_integral_eq_fourierPPrime hlam , (by
                                                               simp_all : Real.log (abs (-Real.cosh lam)) = Real.log (Real.cosh lam))]
  have hLocalInt :
      ∫ α in (-π)..π, fourierPPrime lam α * fourierTauSeries lam α =
        ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := rfl
  
  
  have hRight  := hIdentity
  have hEq := tendsto_nhds_unique (tendsto_const_nhds.sub hCorr) hRight
  rw [←  tendsto_nhds_unique hS hS' ] at hEq
  linarith

end

/-- The analytic exponent in the eigenvalue-ratio formula, with the source parameter
`Δ = -cosh λ` and positive real mode `r`. -/
theorem fourierRatioExponent {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      -r * Real.log (abs (-Real.cosh lam)) +
          r *  ∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x  =
        -r * (lam + 2 * S) := by
  grind [fourierEllPrime_tau_integral_value]

end PottsDiscontinuity
