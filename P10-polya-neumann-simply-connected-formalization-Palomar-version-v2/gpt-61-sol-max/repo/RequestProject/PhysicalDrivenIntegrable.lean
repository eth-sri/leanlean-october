module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.PhysicalDrivenMoments
public import RequestProject.Unitarity

/-!
# Genuine driven moments for integrable forcing

The actual variation-of-constants vector is constructed with merely
interval-integrable forcing. Banach-valued primitive absolute continuity
and the proved a.e. fundamental theorem give its actual driven equation.
The forcing cancels in every positive row. Those rows consequently have
pointwise continuous derivatives on the open interval, allowing the true
finite factorial gauge recurrence and its moment limit.

No absolute continuity, driven equation or approximation in an observation
kernel is postulated for the constructed vector.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate



/-- A Banach-valued primitive is genuinely absolutely continuous. This is
the norm-increment version of Mathlib's real-valued primitive proof. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_banach
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : ℝ → V}  (hf : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) => ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hlim  :=
    tendsto_setLIntegral_zero (ne_of_lt (intervalIntegrable_iff.mp hf).hasFiniteIntegral)
      (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have hlim' := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim
  refine squeeze_zero' ?_ ?_ hlim'
  · filter_upwards with E
    positivity
  simp only [Function.comp_apply]
  have hmem : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b := eventually_inf_principal.mpr (by simp)
  filter_upwards [hmem] with E hE
  obtain ⟨hE1, hE2⟩ := mem_setOf_eq ▸ hE
  rw [← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable_restrict_uIoc.restrict,
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hE2]
  · refine Finset.sum_le_sum (fun i hi => ?_)
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
      (by apply IntervalIntegrable.mono_set' hf; grind [uIoc, uIcc])
      (by apply IntervalIntegrable.mono_set' hf; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi))]
    simpa only [uIoc_comm] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := f)
        (a := (E.2 i).2) (b := (E.2 i).1))
  · intro i hi
    unfold IntegrableOn
    have hsub := uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsub]
    exact (IntegrableOn.mono_set hf.def'.norm hsub).integrable

/-- The actual a.e. primitive derivative, localized to a finite interval. -/
theorem ae_hasDerivAt_intervalIntegral_banach
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : ℝ → V}  (hL : 0 ≤ L) (hf : IntervalIntegrable f volume 0 L) :
    ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f x) x := by
  have hfi : IntegrableOn f (Icc 0 L) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp hf
  let G := (Icc 0 L).indicator f
  have hGi : Integrable G := hfi.integrable_indicator measurableSet_Icc
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable]
    with x hx hmem
  have hxc := Ioo_subset_Icc_self hmem
  have hd := hx 0
  rw [show G x = f x by simp [G, indicator_of_mem hxc]] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with y hy
  apply intervalIntegral.integral_congr
  intro t ht
  have htc : t ∈ Icc 0 L := by
    rw [uIcc_of_le hy.1.le] at ht
    exact ⟨ht.1, ht.2.trans hy.2.le⟩
  simp [G, indicator_of_mem htc]

/-- True Banach-valued FTC from absolute continuity and the actual a.e.
derivative, without a bounded-derivative or Lipschitz hypothesis. -/
theorem eq_add_intervalIntegral_of_ac_ae_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f g : ℝ → V}  (hL : 0 ≤ L)
    (hf : AbsolutelyContinuousOnInterval f 0 L) (hg : IntegrableOn g (Icc 0 L))
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in (0 : ℝ)..θ, g s := by
  let G := (Icc 0 L).indicator g
  have hGi  := hg.integrable_indicator measurableSet_Icc
  let P  := fun x => ∫ s in (0)..x, G s
  have hP  :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hGi.intervalIntegrable
      (by rw [uIcc_of_le hL]; exact ⟨le_rfl, hL⟩)
  have hPeq (θ : ℝ) (hθ : θ ∈ Icc 0 L) : P θ = ∫ s in (0 : ℝ)..θ, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsc : s ∈ Icc 0 L := by
      rw [uIcc_of_le hθ.1] at hs
      exact ⟨hs.1, hs.2.trans hθ.2⟩
    simp [G, indicator_of_mem hsc]
  have hz : ∀ᵐ x, x ∈ uIcc 0 L → HasDerivAt (f - P) 0 x := by
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have h1 : ∀ᵐ x : ℝ, x ≠ L := by simp [ae_iff, measure_singleton]
    filter_upwards [hd, ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable,
      h0, h1] with x hx hxP hx0 hxL hxc
    rw [uIcc_of_le hL] at hxc
    have hxo : x ∈ Ioo 0 L :=
      ⟨lt_of_le_of_ne hxc.1 (Ne.symm hx0), lt_of_le_of_ne hxc.2 hxL⟩
    have h := (hx hxo).sub (hxP 0)
    simpa only [indicator_of_mem hxc, sub_self] using h
  obtain ⟨c, hc⟩ := (hf.sub hP).const_of_ae_hasDerivAt_zero hz
  intro θ hθ
  have hc0 := hc 0 (by norm_num)
  have hcθ := hc θ (by rw [uIcc_of_le hL]; exact hθ)
  simp only [Pi.sub_apply,  intervalIntegral.integral_same, sub_zero] at hc0
  change f θ - P θ = c at hcθ
  grind

/-- A bounded linear image of a genuine absolutely continuous function. -/
theorem absolutelyContinuousOnInterval_clm_comp
    {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (A : V →L[ℂ] Z) {f } {a b }
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => A (f x)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  have hlim : Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range E.1,
        ‖A‖ * dist (f (E.2 i).1) (f (E.2 i).2))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) := by
    simpa  [Finset.mul_sum] using hf.const_mul ‖A‖
  apply squeeze_zero (fun E => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun E => ?_) hlim
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact A.le_opNorm _

/-- Actual operator evaluation preserves absolute continuity. Its increment
estimate uses the genuine operator norm inequality, not a scalar norm equality. -/
theorem absolutelyContinuousOnInterval_clm_apply
    {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {A : ℝ → V →L[ℂ] Z} {f } {a b }
    (hA : AbsolutelyContinuousOnInterval A a b) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => A x (f x)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hf.exists_bound
  unfold AbsolutelyContinuousOnInterval at hA hf ⊢
  have hlim : Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range E.1,
        (C * dist (f (E.2 i).1) (f (E.2 i).2) +
          D * dist (A (E.2 i).1) (A (E.2 i).2)))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) := by
    simpa only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_zero, add_zero] using
      (hf.const_mul C).add (hA.const_mul D)
  apply squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall (fun E => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  rw [eventually_inf_principal]
  filter_upwards with E hE
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hxi := (hE.1 i hi).1
  have hyi := (hE.1 i hi).2
  let x := (E.2 i).1
  let y := (E.2 i).2
  have he : A x (f x) - A y (f y) = A x (f x - f y) + (A x - A y) (f y) := by
    norm_num
  calc
    _ = ‖A x (f x - f y) + (A x - A y) (f y)‖ := by rw [dist_eq_norm, he]
    _ ≤ ‖A x‖ * ‖f x - f y‖ + ‖A x - A y‖ * ‖f y‖ :=
      (norm_add_le _ _).trans (add_le_add ((A x).le_opNorm _) ((A x - A y).le_opNorm _))
    _ ≤ C * dist (f x) (f y) + D * dist (A x) (A y) := by
      rw [dist_eq_norm, dist_eq_norm]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hC x hxi) (norm_nonneg _))
        (by rw [mul_comm D]; exact mul_le_mul_of_nonneg_left (hD y hyi) (norm_nonneg _))

section
variable {W : ℝ → ComplexEnd Ell2} (hW : ContinuousOn W boundaryInterval) (g : ComplexCurve) (hg : IntervalIntegrable g volume 0 circlePeriod)
include W hW g hg

/-- The actual variation-of-constants integrand is integrable for an
integrable load and the genuine continuous transport. -/
theorem physicalDrivenIntegrand_integrableOn :
    IntegrableOn (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      boundaryInterval := by
  have hgi : IntegrableOn g boundaryInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  have hr := continuousOn_adjoint_apply hW (basisVec 0)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  have hm : ∀ᵐ s ∂volume.restrict boundaryInterval,
      ‖ContinuousLinearMap.adjoint (W s) (basisVec 0)‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hM s hs
  exact hgi.smul_bdd M (hr.aestronglyMeasurable measurableSet_Icc) hm

theorem physicalDrivenIntegrand_intervalIntegrable :
    IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 circlePeriod := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact (physicalDrivenIntegrand_integrableOn hW g hg).mono_set Ioc_subset_Icc_self

/-- The actual driven vector is continuous even though its forcing need
only be integrable. -/
theorem physicalDrivenVector_continuousOn_of_intervalIntegrable :
    ContinuousOn (physicalDrivenVector W g) boundaryInterval := by
  have hi : IntegrableOn
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
        (uIcc (0 : ℝ) circlePeriod) := by
    rw [uIcc_of_le Real.two_pi_pos.le]
    exact physicalDrivenIntegrand_integrableOn hW g hg
  have hP := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le Real.two_pi_pos.le] at hP
  exact (hW.clm_apply hP).const_smul (-(Complex.I / (Real.sqrt 2)))

end


/-- Absolute continuity of the actual driven vector follows from its
integral construction and the genuine Lipschitz transport. -/
theorem physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable
      (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W)
    g (hg : IntervalIntegrable g volume 0 circlePeriod) :
    AbsolutelyContinuousOnInterval (physicalDrivenVector W g) 0 circlePeriod := by
  obtain ⟨L, hL⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  have hWA : AbsolutelyContinuousOnInterval W 0 circlePeriod := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa  [uIcc_of_le Real.two_pi_pos.le] using hL
  have hP := absolutelyContinuousOnInterval_intervalIntegral_banach
    (physicalDrivenIntegrand_intervalIntegrable hW.1 g hg)
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  exact (absolutelyContinuousOnInterval_clm_apply hWA hP).const_smul
    (-(Complex.I / (Real.sqrt 2)))

section
variable {γ } {K } (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E } {W } (hW : IsTransport γ E W) (g : ComplexCurve) (hg : IntervalIntegrable g volume 0 circlePeriod)
include γ K hK hγ E W hW g hg

/-- The actual driven differential equation holds a.e. for integrable
forcing, derived from the genuine primitive and actual transport. -/
theorem physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt (physicalDrivenVector W g)
        (transportCoeff γ E θ (physicalDrivenVector W g θ) +
          (-(Complex.I / (Real.sqrt 2 : ℂ)) * g θ) • basisVec 0) θ := by
  let A  := fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)
  have hdA := ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (physicalDrivenIntegrand_intervalIntegrable hW.1 g hg)
  filter_upwards [hdA] with θ hA hθ
  have hc := Ioo_subset_Icc_self hθ
  have hdW := (hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW hc).hasDerivAt
    (Icc_mem_nhds hθ.1 hθ.2)
  have hd := (hasDerivAt_clm_apply_real hdW (hA hθ)).const_smul
    (-(Complex.I / (Real.sqrt 2)))
  have hu := transport_mul_adjoint hK hW hc
  have hWA : W θ (A θ) = g θ • basisVec 0 := by
    rw [map_smul, ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]
  convert hd using 1
  · rfl
  dsimp only [physicalDrivenVector]
  rw [ContinuousLinearMap.mul_apply, hWA, map_smul, smul_add, smul_smul]

/-- The actual driven vector satisfies the genuine integral equation for
integrable forcing. This is derived from its AC construction and a.e.
driven derivative, including its true zero initial value. -/
theorem physicalDrivenVector_integral_eq_of_intervalIntegrable
    {θ : ℝ} (hθ : θ ∈ boundaryInterval) :
    physicalDrivenVector W g θ = ∫ s in (0 : ℝ)..θ,
      transportCoeff γ E s (physicalDrivenVector W g s) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0 := by
  have hC : Continuous (transportCoeff γ E) := by
    have hd := hγ.continuous_deriv_one
    unfold transportCoeff
    fun_prop
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hCY : IntegrableOn
      (fun s : ℝ => transportCoeff γ E s (physicalDrivenVector W g s))
      boundaryInterval volume :=
    (hC.continuousOn.clm_apply hy).integrableOn_Icc
  have hgi : IntegrableOn g boundaryInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  have hforce := (hgi.const_mul (-(Complex.I / (Real.sqrt 2)))).smul_const (basisVec 0)
  have heq := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
    (hCY.add hforce)
    (physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg)
  simp_all

end


section
variable {γ } {K } (hK : LipschitzWith K γ) {E } {W } (hW : IsTransport γ E W) (g : ComplexCurve) (hg : IntervalIntegrable g volume 0 circlePeriod) (n : ℕ)
include γ K hK E W hW g hg n

/-- Every actual row, including the specially normalized zeroth row, is
absolutely continuous for integrable forcing. -/
theorem physicalDrivenRow_absolutelyContinuous_of_intervalIntegrable :
    AbsolutelyContinuousOnInterval (physicalDrivenRow (physicalDrivenVector W g) n)
      0 circlePeriod := by
  have hac := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec n))
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
  by_cases hn : n = 0
  · subst n
    have h := hac.const_smul (Real.sqrt 2)
    simp  [inner_basisVec] at h
    assumption
  · have he : physicalDrivenRow (physicalDrivenVector W g) n =
        fun s : ℝ => (physicalDrivenVector W g s : ComplexSeq) n := by
      grind only [physicalDrivenRow]
    rw [he]
    simpa  [inner_basisVec] using hac

theorem physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable :
    AbsolutelyContinuousOnInterval (physicalDrivenScaledRow E (physicalDrivenVector W g) n)
      0 circlePeriod := (const_smul (physicalDrivenQ E ^ n) (physicalDrivenRow_absolutelyContinuous_of_intervalIntegrable hK hW g hg n))

/-- Positive physical scaled rows are absolutely continuous images of the
constructed vector. This retains the actual sqrt(2) zeroth-row normalization. -/
theorem physicalDrivenScaledRow_succ_absolutelyContinuous_of_intervalIntegrable :
    AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 1)) 0 circlePeriod := by
  have hac := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec (n + 1)))
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
  have h := hac.const_smul (physicalDrivenQ E ^ (n + 1))
  simp  [inner_basisVec] at h
  assumption

end


section
variable {γ } {K } (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E } {W } (hW : IsTransport γ E W) (g : ComplexCurve) (hg : IntervalIntegrable g volume 0 circlePeriod)
local notation "vectorFixed" => physicalDrivenVector W g

include γ K hK hγ E W hW g hg

/-- The direct forcing cancels in the positive rows. Their a.e. derivative
has an actual continuous right-hand side. -/
theorem physicalDrivenScaledRow_succ_ae_hasDerivAt_of_intervalIntegrable n :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt (physicalDrivenScaledRow E vectorFixed (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E vectorFixed (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            physicalDrivenScaledRow E vectorFixed n θ) θ := by
  filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg]
    with θ hθ hmem
  exact physicalDrivenScaledRow_hasDerivAt_succ γ E g _ (hθ hmem) n

/-- Actual pointwise derivatives of positive rows despite merely integrable
forcing. The a.e. identity is first integrated by the genuine AC FTC. -/
theorem physicalDrivenScaledRow_hasDerivAt_succ_of_intervalIntegrable n
     (hθ : θ ∈ Ioo 0 circlePeriod) :
    HasDerivAt (physicalDrivenScaledRow E vectorFixed (n + 1))
      (deriv γ θ * physicalDrivenScaledRow E vectorFixed (n + 2) θ +
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenScaledRow E vectorFixed n θ) θ := by
  let y := vectorFixed
  let d  := fun t => deriv γ t * physicalDrivenScaledRow E y (n + 2) t +
    physicalDrivenQ E ^ 2 * conj (deriv γ t) * physicalDrivenScaledRow E y n t
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hc (k : ℕ) : ContinuousOn (physicalDrivenScaledRow E y k) boundaryInterval :=
    continuousOn_const.mul (physicalDrivenRow_continuousOn y hy k)
  have hd : ContinuousOn d boundaryInterval :=
    (hγ.continuous_deriv_one.continuousOn.mul (hc (n + 2))).add
      ((continuousOn_const.mul
        (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn).mul (hc n))
  have heq := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenScaledRow_succ_absolutelyContinuous_of_intervalIntegrable hK hW g hg n)
    hd.integrableOn_Icc
    (physicalDrivenScaledRow_succ_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg n)
  have htc := Ioo_subset_Icc_self hθ
  have hsub : uIcc 0 θ ⊆ boundaryInterval := by
    rw [uIcc_of_le htc.1]
    exact Icc_subset_Icc le_rfl htc.2
  haveI : Fact (θ ∈ boundaryInterval) := ⟨htc⟩
  have hprim := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc 0 circlePeriod) (t := Icc 0 circlePeriod)
    ((hd.mono hsub).intervalIntegrable)
    (hd.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc θ) (hd θ htc)
  have hder := (hprim.hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)).const_add
    (physicalDrivenScaledRow E y (n + 1) 0)
  refine hder.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  exact heq t (Ioo_subset_Icc_self ht)

/-- The actual finite factorial gauge derivative follows from the positive
row equations. Integrable forcing contributes no pointwise forcing term. -/
theorem physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable
     (hθ : θ ∈ Ioo 0 circlePeriod) j N :
    HasDerivAt (physicalDrivenGaugePartial γ E vectorFixed (j + 1) N)
      (physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenGaugePartial γ E vectorFixed j N θ +
        deriv γ θ * physicalDrivenPower γ N θ *
          physicalDrivenScaledRow E vectorFixed (N + j + 2) θ) θ := by
  induction N with
  | zero =>
    have he (k : ℕ) : physicalDrivenGaugePartial γ E vectorFixed k 0 =
        physicalDrivenScaledRow E vectorFixed k := by
      funext s
      simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower]
    rw [he (j + 1), he j]
    simpa [physicalDrivenPower, add_comm] using
      physicalDrivenScaledRow_hasDerivAt_succ_of_intervalIntegrable hK hγ hW g hg j hθ
  | succ N ih =>
    have hp := physicalDrivenPower_hasDerivAt_succ hγ N θ
    have hd := physicalDrivenScaledRow_hasDerivAt_succ_of_intervalIntegrable hK hγ hW g hg
      (N + j + 1) hθ
    have ht := hp.mul hd
    have he (k : ℕ) : physicalDrivenGaugePartial γ E vectorFixed k (N + 1) =
        fun s => physicalDrivenGaugePartial γ E vectorFixed k N s +
          physicalDrivenGaugeTerm γ E vectorFixed k (N + 1) s := by
      funext s
      exact Finset.sum_range_succ _ _
    rw [he]
    convert ih.add ht using 1
    · funext s
      simp  [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_left_comm]
    · rw [he]
      simp only [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      ring

theorem physicalDrivenMomentPartial_recurrence_of_intervalIntegrable (hO : observationAdj W g = 0) j N m :
    physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E vectorFixed j N m +
      (m : ℂ) * physicalDrivenMomentPartial γ E vectorFixed (j + 1) N (m - 1) =
        -physicalDrivenTailMoment γ E vectorFixed j N m := by
  let y := vectorFixed
  let z  := fun θ => conj (physicalDrivenCentered γ θ)
  let p := physicalDrivenGaugePartial γ E y (j + 1) N
  let a  := fun θ => conj (deriv γ θ) * physicalDrivenGaugePartial γ E y j N θ * z θ ^ m
  let b  := fun θ => conj (deriv γ θ) * p θ * z θ ^ (m - 1)
  let t  := fun θ => deriv γ θ * physicalDrivenPower γ N θ *
    physicalDrivenScaledRow E y (N + j + 2) θ * z θ ^ m
  let r  := fun θ => physicalDrivenQ E ^ 2 * a θ + m * b θ + t θ
  have hy  := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hz : Continuous z := Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)
  have hp := physicalDrivenGaugePartial_continuousOn γ hγ.continuous E y hy (j + 1) N
  have ha  :=
    ((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E y hy j N)).mul
        (hz.pow m).continuousOn
  have hb  :=
    ((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul hp).mul
      (hz.pow (m - 1)).continuousOn
  have hpower : Continuous (physicalDrivenPower γ N) := by
    unfold physicalDrivenPower physicalDrivenCentered
    fun_prop
  have ht : ContinuousOn t boundaryInterval :=
    ((hγ.continuous_deriv_one.mul hpower).continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy (N + j + 2)))).mul
        (hz.pow m).continuousOn
  have hr : ContinuousOn r boundaryInterval :=
    ((continuousOn_const.mul ha).add (continuousOn_const.mul hb)).add ht
  have hd (θ : ℝ) (hθ : θ ∈ Ioo 0 circlePeriod) :
      HasDerivAt (fun s => p s * z s ^ m) (r θ) θ := by
    have hdp := physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable hK hγ hW g hg hθ j N
    have hdz : HasDerivAt z (conj (deriv γ θ)) θ := by
      simpa only [z, physicalDrivenCentered, Complex.star_def] using
        ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
    convert hdp.mul (hdz.pow m) using 1
    simp only [r, a, b, t, p, Pi.pow_apply]
    ring
  have hsub : uIcc (0 : ℝ) circlePeriod ⊆ boundaryInterval := by
    rw [uIcc_of_le Real.two_pi_pos.le]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.two_pi_pos.le
    (hp.mul (hz.pow m).continuousOn) hd (hr.mono hsub).intervalIntegrable
  have hp0 : p 0 = 0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
    (physicalDrivenVector_zero W g)
  have hpL : p circlePeriod = 0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
    (physicalDrivenVector_endpoint W g hO)
  change (∫ θ in (0)..circlePeriod, r θ) =
    p circlePeriod * z circlePeriod ^ m - p 0 * z 0 ^ m at hi
  simp only [hp0, hpL, zero_mul, sub_self] at hi
  have hia : IntervalIntegrable a volume 0 circlePeriod :=
    (ha.mono hsub).intervalIntegrable
  have hib : IntervalIntegrable b volume 0 circlePeriod :=
    (hb.mono hsub).intervalIntegrable
  have hit : IntervalIntegrable t volume 0 circlePeriod :=
    (ht.mono hsub).intervalIntegrable
  rw [intervalIntegral.integral_add ((hia.const_mul _).add (hib.const_mul _)) hit,
    intervalIntegral.integral_add (hia.const_mul _) (hib.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  exact eq_neg_of_add_eq_zero_left hi

theorem physicalDrivenMoment_recurrence_of_intervalIntegrable (hO : observationAdj W g = 0) j m :
    physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E vectorFixed j m +
      (m : ℂ) * physicalDrivenMoment γ E vectorFixed (j + 1) (m - 1) = 0 := by
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hj := physicalDrivenMomentPartial_tendsto γ hγ E _ hy j m
  have hj' := physicalDrivenMomentPartial_tendsto γ hγ E _ hy (j + 1) (m - 1)
  have ht := physicalDrivenTailMoment_tendsto_zero γ hγ E _ hy j m
  have hl : Tendsto (fun N => physicalDrivenQ E ^ 2 *
      physicalDrivenMomentPartial γ E vectorFixed j N m + (m : ℂ) *
        physicalDrivenMomentPartial γ E vectorFixed (j + 1) N (m - 1))
      atTop (𝓝 (physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E vectorFixed j m +
        (m : ℂ) * physicalDrivenMoment γ E vectorFixed (j + 1) (m - 1))) :=
    (tendsto_const_nhds.mul hj).add (tendsto_const_nhds.mul hj')
  have hr : Tendsto (fun N => physicalDrivenQ E ^ 2 *
      physicalDrivenMomentPartial γ E vectorFixed j N m + (m : ℂ) *
        physicalDrivenMomentPartial γ E vectorFixed (j + 1) N (m - 1))
      atTop (𝓝 0) := by
    simpa  [physicalDrivenMomentPartial_recurrence_of_intervalIntegrable hK hγ hW g hg hO] using ht.neg
  exact tendsto_nhds_unique hl hr

end


theorem physicalDrivenMoment_eq_zero_of_intervalIntegrable
      (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
     (hE : 0 < E)  (hW : IsTransport γ E W)
    g (hg : IntervalIntegrable g volume 0 circlePeriod) (hO : observationAdj W g = 0) j m :
    physicalDrivenMoment γ E (physicalDrivenVector W g) j m = 0 := by
  induction m generalizing j with
  | zero =>
      have h := physicalDrivenMoment_recurrence_of_intervalIntegrable hK hγ hW g hg hO j 0
      simp only [Nat.cast_zero, zero_mul, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)
  | succ m ih =>
      have h := physicalDrivenMoment_recurrence_of_intervalIntegrable hK hγ hW g hg hO j (m + 1)
      rw [Nat.add_sub_cancel, ih (j + 1), mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)

theorem physicalDrivenPeriodicGauge_continuous_of_intervalIntegrable
    γ (hγ : Continuous γ) E
     (hW : ContinuousOn W boundaryInterval)
    g (hg : IntervalIntegrable g volume 0 circlePeriod) (hO : observationAdj W g = 0) j :
    Continuous (physicalDrivenPeriodicGauge γ E W g j) := by
  obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO j
  exact (AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
    (physicalDrivenGauge_continuousOn γ hγ E _
      (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) j)).comp (AddCircle.continuous_mk' _)

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω) {R } (hR : 1 < R) (F ) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F closedUnitDisk) (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) (himage : F '' unitDisk = Ω) {K } (hK : LipschitzWith K (physicalCircleTrace F)) {E } (hE : 0 < E) {W } (hW : IsTransport (physicalCircleTrace F) E W) (g : ComplexCurve)

include Ω hb hΩ R hR F hFs hhol hinj hnz himage K hK E hE W hW g in
theorem localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable (hg : IntervalIntegrable g volume 0 circlePeriod) (hO : observationAdj W g = 0) j :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenPeriodicGauge (physicalCircleTrace F) E W g j)) := by
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  apply localConformal_physicalMoments_nonpositive hb hΩ hR F hFs hhol hinj hnz himage
    (physicalDrivenPeriodicGauge (physicalCircleTrace F) E W g j)
    (physicalDrivenPeriodicGauge_continuous_of_intervalIntegrable _ hγ.continuous E hW.1 g hg hO j)
    (physicalDrivenPeriodicGauge_periodic _ E W g j)
  intro m
  have hm := physicalDrivenMoment_eq_zero_of_intervalIntegrable hK hγ hE hW g hg hO j m
  calc
    _ = physicalDrivenMoment (physicalCircleTrace F) E (physicalDrivenVector W g) j m := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le Real.two_pi_pos.le] at hθ
      dsimp only
      rw [physicalDrivenPeriodicGauge_eqOn _ E W g hO j hθ]
      simp  [physicalDrivenCentered]
    _ = 0 := hm

/-- A genuine L² load on the physical parameter interval is integrable;
the interval has its actual finite Lebesgue measure. -/
theorem intervalIntegrable_boundary_of_memLp
    (g : ComplexCurve) (hg : MemLp g 2 (volume.restrict boundaryHalfOpenInterval)) :
    IntervalIntegrable g volume 0 circlePeriod := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact MemLp.integrable (by norm_num) hg

theorem intervalIntegrable_boundaryL2 (g : BoundaryL2) :
    IntervalIntegrable (g : ComplexCurve) volume 0 circlePeriod :=
  intervalIntegrable_boundary_of_memLp _ (Lp.memLp g)

include Ω hb hΩ R hR F hFs hhol hinj hnz himage K hK E hE W hW g in
/-- Actual L² forcing gives the original-H nonpositive Fourier support
criterion in the supplied conformal coordinates. -/
theorem localConformal_physicalDrivenGauge_nonpositive_of_memLp (hg : MemLp g 2 (volume.restrict boundaryHalfOpenInterval))
    (hO : observationAdj W g = 0) j :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenPeriodicGauge (physicalCircleTrace F) E W g j)) :=
  localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable hb hΩ hR F hFs
    hhol hinj hnz himage hK hE hW g (intervalIntegrable_boundary_of_memLp g hg) hO j

end


end PolyaNeumann

end
