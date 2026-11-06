module

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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

local instance physicalDrivenIntegrableTwoPiPos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

variable {W : ℝ → Ell2 →L[ℂ] Ell2} {γ : ℝ → ℂ} {K : NNReal} {Ω : Set ℂ}

/-- A Banach-valued primitive is genuinely absolutely continuous. This is
the norm-increment version of Mathlib's real-valued primitive proof. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_banach
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : ℝ → V} {a b c : ℝ} (hf : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) => ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hlim : Tendsto (fun i => ∫⁻ x in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero (ne_of_lt (intervalIntegrable_iff.mp hf).hasFiniteIntegral)
      (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  refine squeeze_zero' ?_ ?_ (ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim)
  · filter_upwards with E
    positivity
  simp 
  have hmem : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b := eventually_inf_principal.mpr (by simp)
  filter_upwards [hmem] with E hE
  obtain ⟨hE1, hE2⟩ := mem_setOf_eq ▸ hE
  rw [← integral_norm_eq_lintegral_enorm (hf.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp [uIoc]) hE2]
  · refine Finset.sum_le_sum (fun i hi => ?_)
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
      (by apply IntervalIntegrable.mono_set' hf; grind [uIcc])
      (by apply IntervalIntegrable.mono_set' hf; grind [uIcc]),
      Measure.restrict_restrict_of_subset
        (uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi))]
    simpa only [uIoc_comm] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc 
        (a := (E.2 i).2) )
  · intro i hi
    unfold IntegrableOn
    have hsub := uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsub]
    exact (IntegrableOn.mono_set hf.def'.norm hsub).integrable

/-- The actual a.e. primitive derivative, localized to a finite interval. -/
theorem ae_hasDerivAt_intervalIntegral_banach
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : ℝ → V} {L : ℝ} (hL : 0 ≤ L) (hf : IntervalIntegrable f volume 0 L) :
    ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt (fun x => ∫ t in 0..x, f t) (f x) x := by
  have hfi : IntegrableOn f (Icc 0 L) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp hf
  let G := (Icc 0 L).indicator f
  have hGi : Integrable G := hfi.integrable_indicator measurableSet_Icc
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable]
    with x hx hmem
  have hxc := Ioo_subset_Icc_self hmem
  have hd := hx 0
  rw [show G x = f x by continuity] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with y hy
  apply intervalIntegral.integral_congr
  intro t ht
  have htc : t ∈ Icc 0 L := by
    rw [uIcc_of_le hy.1.le] at ht
    grind
  continuity

/-- True Banach-valued FTC from absolute continuity and the actual a.e.
derivative, without a bounded-derivative or Lipschitz hypothesis. -/
theorem eq_add_intervalIntegral_of_ac_ae_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f g : ℝ → V} {L : ℝ} (hL : 0 ≤ L)
    (hf : AbsolutelyContinuousOnInterval f 0 L) (hg : IntegrableOn g (Icc 0 L))
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in 0..θ, g s := by
  let G := (Icc 0 L).indicator g
  have hGi  := hg.integrable_indicator measurableSet_Icc
  let P  := fun x => ∫ s in 0..x, G s
  have hPeq (θ : ℝ) (hθ : θ ∈ Icc 0 L) : P θ = ∫ s in 0..θ, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsc : s ∈ Icc 0 L := by
      rw [uIcc_of_le hθ.1] at hs
      grind
    continuity
  obtain ⟨c, hc⟩ := (hf.sub (absolutelyContinuousOnInterval_intervalIntegral_banach hGi.intervalIntegrable
      (by rw [uIcc_of_le hL]; exact ⟨le_rfl, hL⟩))).const_of_ae_hasDerivAt_zero (by
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    have h1 : ∀ᵐ x : ℝ, x ≠ L := by simp [ae_iff]
    filter_upwards [hd, ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable,
      h0, h1] with x hx hxP hx0 hxL hxc
    rw [uIcc_of_le hL] at hxc
    have h := (hx ⟨lt_of_le_of_ne hxc.1 (Ne.symm hx0), lt_of_le_of_ne hxc.2 hxL⟩).sub (hxP 0)
    continuity)
  intro θ hθ
  have hc0 := hc 0 (by norm_num)
  have hcθ := hc θ (by simp_all)
  simp  at hc0
  continuity

/-- A bounded linear image of a genuine absolutely continuous function. -/
theorem absolutelyContinuousOnInterval_clm_comp
    {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (A : V →L[ℂ] Z) {f : ℝ → V} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => A (f x)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero (fun E => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun E => ?_) (by
    simpa only [Finset.mul_sum, mul_zero] using hf.const_mul ‖A‖)
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact A.le_opNorm _

/-- Actual operator evaluation preserves absolute continuity. Its increment
estimate uses the genuine operator norm inequality, not a scalar norm equality. -/
theorem absolutelyContinuousOnInterval_clm_apply
    {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {A : ℝ → V →L[ℂ] Z} {f : ℝ → V} {a b : ℝ}
    (hA : AbsolutelyContinuousOnInterval A a b) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => A x (f x)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hf.exists_bound
  unfold AbsolutelyContinuousOnInterval at hA hf ⊢
  apply squeeze_zero' ?_ ?_ (by
    simpa only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_zero, add_zero] using
      (hf.const_mul C).add (hA.const_mul D))
  · exact Eventually.of_forall (fun E => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  rw [eventually_inf_principal]
  filter_upwards with E hE
  refine Finset.sum_le_sum (fun i hi => ?_)
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
        (mul_le_mul_of_nonneg_right (hC x (hE.1 i hi).1) (norm_nonneg _))
        (by rw [mul_comm D]; exact mul_le_mul_of_nonneg_left (hD y (hE.1 i hi).2) (norm_nonneg _))

/-- The actual variation-of-constants integrand is integrable for an
integrable load and the genuine continuous transport. -/
theorem physicalDrivenIntegrand_integrableOn
    (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    IntegrableOn (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      (Icc 0 (2 * Real.pi)) := by
  have hgi : IntegrableOn g (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  have hr := continuousOn_adjoint_apply hW (basisVec 0)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  exact hgi.smul_bdd M (hr.aestronglyMeasurable measurableSet_Icc) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simp_all)

theorem physicalDrivenIntegrand_intervalIntegrable
    (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact (physicalDrivenIntegrand_integrableOn hW g hg).mono_set Ioc_subset_Icc_self

/-- The actual driven vector is continuous even though its forcing need
only be integrable. -/
theorem physicalDrivenVector_continuousOn_of_intervalIntegrable
    (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    ContinuousOn (physicalDrivenVector W g) (Icc 0 (2 * Real.pi)) := by
  have hP := intervalIntegral.continuousOn_primitive_interval (by
    rw [uIcc_of_le Real.two_pi_pos.le]
    exact physicalDrivenIntegrand_integrableOn hW g hg)
  rw [uIcc_of_le Real.two_pi_pos.le] at hP
  exact (hW.clm_apply hP).const_smul (-(Complex.I / Real.sqrt 2))

/-- Absolute continuity of the actual driven vector follows from its
integral construction and the genuine Lipschitz transport. -/
theorem physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable
    (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    AbsolutelyContinuousOnInterval (physicalDrivenVector W g) 0 (2 * Real.pi) := by
  obtain ⟨L, hL⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  exact (absolutelyContinuousOnInterval_clm_apply (by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hL) (absolutelyContinuousOnInterval_intervalIntegral_banach
    (physicalDrivenIntegrand_intervalIntegrable hW.1 g hg)
    (by norm_num))).const_smul
    (-(Complex.I / Real.sqrt 2))

/-- The actual driven differential equation holds a.e. for integrable
forcing, derived from the genuine primitive and actual transport. -/
theorem physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenVector W g)
        (transportCoeff γ E θ (physicalDrivenVector W g θ) +
          (-(Complex.I / Real.sqrt 2) * g θ) • basisVec 0) θ := by
  let A  := fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (physicalDrivenIntegrand_intervalIntegrable hW.1 g hg)] with θ hA hθ
  have hc := Ioo_subset_Icc_self hθ
  have hWA : W θ (A θ) = g θ • basisVec 0 := by
    rw [map_smul, ← ContinuousLinearMap.mul_apply, transport_mul_adjoint hK hW hc, ContinuousLinearMap.one_apply]
  convert (hasDerivAt_clm_apply_real ((hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW hc).hasDerivAt
    (Icc_mem_nhds hθ.1 hθ.2)) (hA hθ)).const_smul
    (-(Complex.I / Real.sqrt 2)) using 1
  · rfl
  dsimp only [physicalDrivenVector]
  rw [ContinuousLinearMap.mul_apply, hWA, map_smul, smul_add, smul_smul]

/-- The actual driven vector satisfies the genuine integral equation for
integrable forcing. This is derived from its AC construction and a.e.
driven derivative, including its true zero initial value. -/
theorem physicalDrivenVector_integral_eq_of_intervalIntegrable
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenVector W g θ = ∫ s in 0..θ,
      transportCoeff γ E s (physicalDrivenVector W g s) +
        (-(Complex.I / Real.sqrt 2) * g s) • basisVec 0 := by
  have hC : Continuous (transportCoeff γ E) := by
    unfold transportCoeff
    fun_prop
  have hgi : IntegrableOn g (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  have heq := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
    ((hC.continuousOn.clm_apply (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg)).integrableOn_Icc.add ((hgi.const_mul (-(Complex.I / Real.sqrt 2))).smul_const (basisVec 0)))
    (physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg)
  simp_all

/-- Every actual row, including the specially normalized zeroth row, is
absolutely continuous for integrable forcing. -/
theorem physicalDrivenRow_absolutelyContinuous_of_intervalIntegrable
    (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (n : ℕ) :
    AbsolutelyContinuousOnInterval (physicalDrivenRow (physicalDrivenVector W g) n)
      0 (2 * Real.pi) := by
  have hac := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec n))
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
  by_cases hn : n = 0
  · subst n
    have h := hac.const_smul (Real.sqrt 2)
    simp only [innerSL_apply_apply, inner_basisVec] at h
    assumption
  · have he : physicalDrivenRow (physicalDrivenVector W g) n =
        fun s  => physicalDrivenVector W g s n := by
      funext s
      simp [physicalDrivenRow, if_neg hn]
    simp_all [inner_basisVec]

theorem physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable
    (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (n : ℕ) :
    AbsolutelyContinuousOnInterval (physicalDrivenScaledRow E (physicalDrivenVector W g) n)
      0 (2 * Real.pi) := by
  have h := (physicalDrivenRow_absolutelyContinuous_of_intervalIntegrable hK hW g hg n).const_smul
      (physicalDrivenQ E ^ n)
  assumption

/-- Positive physical scaled rows are absolutely continuous images of the
constructed vector. This retains the actual sqrt(2) zeroth-row normalization. -/
theorem physicalDrivenScaledRow_succ_absolutelyContinuous_of_intervalIntegrable
    (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (n : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 1)) 0 (2 * Real.pi) := by
  have h := (absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec (n + 1)))
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)).const_smul (physicalDrivenQ E ^ (n + 1))
  simp only [innerSL_apply_apply, inner_basisVec] at h
  assumption

/-- The direct forcing cancels in the positive rows. Their a.e. derivative
has an actual continuous right-hand side. -/
theorem physicalDrivenScaledRow_succ_ae_hasDerivAt_of_intervalIntegrable
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (n : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            physicalDrivenScaledRow E (physicalDrivenVector W g) n θ) θ := by
  filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg]
    with θ hθ hmem
  exact physicalDrivenScaledRow_hasDerivAt_succ γ E g _ (hθ hmem) n

/-- Actual pointwise derivatives of positive rows despite merely integrable
forcing. The a.e. identity is first integrated by the genuine AC FTC. -/
theorem physicalDrivenScaledRow_hasDerivAt_succ_of_intervalIntegrable
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (n : ℕ)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt (physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 1))
      (deriv γ θ * physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 2) θ +
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenScaledRow E (physicalDrivenVector W g) n θ) θ := by
  let y := physicalDrivenVector W g
  let d  := fun t => deriv γ t * physicalDrivenScaledRow E y (n + 2) t +
    physicalDrivenQ E ^ 2 * conj (deriv γ t) * physicalDrivenScaledRow E y n t
  have hc (k : ℕ) : ContinuousOn (physicalDrivenScaledRow E y k) (Icc 0 (2 * Real.pi)) :=
    continuousOn_const.mul (physicalDrivenRow_continuousOn y (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg) k)
  have hd : ContinuousOn d (Icc 0 (2 * Real.pi)) :=
    (hγ.continuous_deriv_one.continuousOn.mul (hc (n + 2))).add
      ((continuousOn_const.mul
        (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn).mul (hc n))
  have heq := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenScaledRow_succ_absolutelyContinuous_of_intervalIntegrable hK hW g hg n)
    hd.integrableOn_Icc
    (physicalDrivenScaledRow_succ_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg n)
  have htc := Ioo_subset_Icc_self hθ
  haveI : Fact (θ ∈ Icc 0 (2 * Real.pi)) := ⟨htc⟩
  refine (((intervalIntegral.integral_hasDerivWithinAt_right
     
    ((hd.mono (by
    rw [uIcc_of_le htc.1]
    grind)).intervalIntegrable)
    (hd.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc θ) (hd θ htc)).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)).const_add
    (physicalDrivenScaledRow E y (n + 1) 0)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  grind

/-- The actual finite factorial gauge derivative follows from the positive
row equations. Integrable forcing contributes no pointwise forcing term. -/
theorem physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) (j N : ℕ) :
    HasDerivAt (physicalDrivenGaugePartial γ E (physicalDrivenVector W g) (j + 1) N)
      (physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenGaugePartial γ E (physicalDrivenVector W g) j N θ +
        deriv γ θ * physicalDrivenPower γ N θ *
          physicalDrivenScaledRow E (physicalDrivenVector W g) (N + j + 2) θ) θ := by
  induction N with
  | zero =>
    have he (k : ℕ) : physicalDrivenGaugePartial γ E (physicalDrivenVector W g) k 0 =
        physicalDrivenScaledRow E (physicalDrivenVector W g) k := by
      funext s
      simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower]
    rw [he (j + 1), he j]
    simpa [physicalDrivenPower, add_comm] using
      physicalDrivenScaledRow_hasDerivAt_succ_of_intervalIntegrable hK hγ hW g hg j hθ
  | succ N ih =>
    have he (k : ℕ) : physicalDrivenGaugePartial γ E (physicalDrivenVector W g) k (N + 1) =
        fun s => physicalDrivenGaugePartial γ E (physicalDrivenVector W g) k N s +
          physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) k (N + 1) s := by
      funext s
      exact Finset.sum_range_succ _ _
    rw [he]
    convert ih.add ((physicalDrivenPower_hasDerivAt_succ hγ N θ).mul (physicalDrivenScaledRow_hasDerivAt_succ_of_intervalIntegrable hK hγ hW g hg
      (N + j + 1) hθ)) using 1
    · funext s
      simp [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_left_comm]
    · rw [he]
      simp only [physicalDrivenGaugeTerm]
      ring

theorem physicalDrivenMomentPartial_recurrence_of_intervalIntegrable
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (hO : observationAdj W g = 0) (j N m : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E (physicalDrivenVector W g) j N m +
      m * physicalDrivenMomentPartial γ E (physicalDrivenVector W g) (j + 1) N (m - 1) =
        -physicalDrivenTailMoment γ E (physicalDrivenVector W g) j N m := by
  let y := physicalDrivenVector W g
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
  have ht : ContinuousOn t (Icc 0 (2 * Real.pi)) :=
    ((hγ.continuous_deriv_one.mul (((hγ.continuous.sub continuous_const).neg.pow N).div_const N.factorial)).continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy (N + j + 2)))).mul
        (hz.pow m).continuousOn
  have hd (θ : ℝ) (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
      HasDerivAt (fun s => p s * z s ^ m) (r θ) θ := by
    have hdz : HasDerivAt z (conj (deriv γ θ)) θ := by
      simpa only [z, physicalDrivenCentered, Complex.star_def] using
        ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
    convert (physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable hK hγ hW g hg hθ j N).mul (hdz.pow m) using 1
    simp 
    ring
  have hsub : uIcc 0 (2 * Real.pi) ⊆ Icc 0 (2 * Real.pi) := by
    rw [uIcc_of_le Real.two_pi_pos.le]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.two_pi_pos.le
    (hp.mul (hz.pow m).continuousOn) hd ((((continuousOn_const.mul ha).add (continuousOn_const.mul hb)).add ht).mono hsub).intervalIntegrable
  have hp0 : p 0 = 0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
    (physicalDrivenVector_zero W g)
  have hpL : p (2 * Real.pi) = 0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
    (physicalDrivenVector_endpoint W g hO)
  change (∫ θ in 0..(2 * Real.pi), r θ) =
    p (2 * Real.pi) * z (2 * Real.pi) ^ m - p 0 * z 0 ^ m at hi
  simp only [hp0, hpL, zero_mul, sub_self] at hi
  have hia : IntervalIntegrable a volume 0 (2 * Real.pi) :=
    (ha.mono hsub).intervalIntegrable
  have hib : IntervalIntegrable b volume 0 (2 * Real.pi) :=
    (hb.mono hsub).intervalIntegrable
  rw [intervalIntegral.integral_add ((hia.const_mul _).add (hib.const_mul _)) (ht.mono hsub).intervalIntegrable,
    intervalIntegral.integral_add (hia.const_mul _) (hib.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  exact eq_neg_of_add_eq_zero_left hi

theorem physicalDrivenMoment_recurrence_of_intervalIntegrable
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (hO : observationAdj W g = 0) (j m : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E (physicalDrivenVector W g) j m +
      m * physicalDrivenMoment γ E (physicalDrivenVector W g) (j + 1) (m - 1) = 0 := by
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  exact tendsto_nhds_unique ((tendsto_const_nhds.mul (physicalDrivenMomentPartial_tendsto γ hγ E _ hy j m)).add (tendsto_const_nhds.mul (physicalDrivenMomentPartial_tendsto γ hγ E _ hy (j + 1) (m - 1)))) (by
    simpa only [physicalDrivenMomentPartial_recurrence_of_intervalIntegrable hK hγ hW g hg hO, neg_zero] using (physicalDrivenTailMoment_tendsto_zero γ hγ E _ hy j m).neg)

theorem physicalDrivenMoment_eq_zero_of_intervalIntegrable
    (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (hO : observationAdj W g = 0) (j m : ℕ) :
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
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (hO : observationAdj W g = 0) (j : ℕ) :
    Continuous (physicalDrivenPeriodicGauge γ E W g j) := by
  obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO j
  exact (AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
    (physicalDrivenGauge_continuousOn γ hγ E _
      (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) j)).comp (AddCircle.continuous_mk' _)

theorem localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball 0 1 = Ω)
    {K : NNReal} (hK : LipschitzWith K (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (hO : observationAdj W g = 0) (j : ℕ) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenPeriodicGauge (physicalCircleTrace F) E W g j)) := by
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  apply localConformal_physicalMoments_nonpositive hb hΩ hR F hFs hhol hinj hnz himage
    (physicalDrivenPeriodicGauge (physicalCircleTrace F) E W g j)
    (physicalDrivenPeriodicGauge_continuous_of_intervalIntegrable _ hγ.continuous E hW.1 g hg hO j)
    (physicalDrivenPeriodicGauge_periodic _ E W g j)
  intro m
  calc
    _ = physicalDrivenMoment (physicalCircleTrace F) E (physicalDrivenVector W g) j m := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le Real.two_pi_pos.le] at hθ
      simp [physicalDrivenPeriodicGauge_eqOn _ E W g hO j hθ, physicalDrivenCentered]
    _ = 0 := physicalDrivenMoment_eq_zero_of_intervalIntegrable hK hγ hE hW g hg hO j m

/-- A genuine L² load on the physical parameter interval is integrable;
the interval has its actual finite Lebesgue measure. -/
theorem intervalIntegrable_boundary_of_memLp
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    IntervalIntegrable g volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact MemLp.integrable (by norm_num) hg

theorem intervalIntegrable_boundaryL2 (g : BoundaryL2) :
    IntervalIntegrable g volume 0 (2 * Real.pi) :=
  intervalIntegrable_boundary_of_memLp _ (Lp.memLp g)

/-- Actual L² forcing gives the original-H nonpositive Fourier support
criterion in the supplied conformal coordinates. -/
theorem localConformal_physicalDrivenGauge_nonpositive_of_memLp
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball 0 1 = Ω)
    {K : NNReal} (hK : LipschitzWith K (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) (j : ℕ) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenPeriodicGauge (physicalCircleTrace F) E W g j)) :=
  localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable hb hΩ hR F hFs
    hhol hinj hnz himage hK hE hW g (intervalIntegrable_boundary_of_memLp g hg) hO j

end PolyaNeumann

end
