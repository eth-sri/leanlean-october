module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalDrivenMoments
public import RequestProject.Unitarity
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

/-- A bounded linear image of a genuine absolutely continuous function. -/
theorem absolutelyContinuousOnInterval_clm_comp
    {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (A : V →L[ℂ] Z) {f : ℝ → V} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => A (f x)) a b := A.lipschitz.comp_absolutelyContinuousOnInterval hf

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
  have hlim : Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range E.1,
        (C * dist (f (E.2 i).1) (f (E.2 i).2) +
          D * dist (A (E.2 i).1) (A (E.2 i).2)))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) := by
    simpa only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_zero, add_zero] using
      (hf.const_mul C).add (hA.const_mul D)
  apply squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall (fun E => Finset.sum_nonneg ((by norm_num)))
  rw [eventually_inf_principal]
  filter_upwards with E hE
  
  refine Finset.sum_le_sum (fun i hi => ?_)
  
  have hyi := (hE.1 i hi).2
  let x := (E.2 i).1
  let y := (E.2 i).2
  have he : A x (f x) - A y (f y) = A x (f x - f y) + (A x - A y) (f y) := by
    simp
  calc
    _ = ‖A x (f x - f y) + (A x - A y) (f y)‖ := by rw [dist_eq_norm, he]
    _ ≤ _ :=
      (norm_add_le _ _).trans (add_le_add ((A x).le_opNorm _) ((A x - A y).le_opNorm _))
    _ ≤ _ := by
      rw [dist_eq_norm, dist_eq_norm]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hC x ((hE.1 i hi).1)) (norm_nonneg _))
        (by rw [mul_comm D]; bound)

/-- The actual variation-of-constants integrand is integrable for an
integrable load and the genuine continuous transport. -/
theorem physicalDrivenIntegrand_integrableOn
    {W : TransportPath} (hW : ContinuousOn W angleInterval)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    IntegrableOn (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      angleInterval := by
  have hgi : IntegrableOn g angleInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  have hr := continuousOn_adjoint_apply hW (basisVec 0)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  
  apply hgi.smul_bdd M (hr.aestronglyMeasurable measurableSet_Icc)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hM s hs

theorem physicalDrivenIntegrand_intervalIntegrable
    {W : TransportPath} (hW : ContinuousOn W angleInterval)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 anglePeriod := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact (physicalDrivenIntegrand_integrableOn hW g hg).mono_set Ioc_subset_Icc_self

/-- The actual driven vector is continuous even though its forcing need
only be integrable. -/
theorem physicalDrivenVector_continuousOn_of_intervalIntegrable
    {W : TransportPath} (hW : ContinuousOn W angleInterval)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    ContinuousOn (physicalDrivenVector W g) angleInterval := by
  
  have hP := intervalIntegral.continuousOn_primitive_interval (by
    rw [uIcc_of_le Real.two_pi_pos.le]
    exact physicalDrivenIntegrand_integrableOn hW g hg)
  rw [uIcc_of_le Real.two_pi_pos.le] at hP
  exact (hW.clm_apply hP).const_smul (-(Complex.I / vacuumWeight))

/-- Absolute continuity of the actual driven vector follows from its
integral construction and the genuine Lipschitz transport. -/
theorem physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    AbsolutelyContinuousOnInterval (physicalDrivenVector W g) 0 anglePeriod := by
  obtain ⟨L, hL⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  
  have hP := absolutelyContinuousOnInterval_intervalIntegral_banach
    (physicalDrivenIntegrand_intervalIntegrable hW.1 g hg)
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  refine (absolutelyContinuousOnInterval_clm_apply ?_ hP).const_smul
    (-(Complex.I / vacuumWeight))
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le Real.two_pi_pos.le] using hL

/-- The actual driven differential equation holds a.e. for integrable
forcing, derived from the genuine primitive and actual transport. -/
theorem physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (physicalDrivenVector W g)
        (transportCoeff γ E θ (physicalDrivenVector W g θ) +
          (-(Complex.I / vacuumWeight) * g θ) • basisVec 0) θ := by
  let A  := fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)
  
  filter_upwards [(ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (physicalDrivenIntegrand_intervalIntegrable hW.1 g hg))] with θ hA hθ
  have hc := Ioo_subset_Icc_self hθ
  have hdW := (hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW hc).hasDerivAt
    (Icc_mem_nhds hθ.1 hθ.2)
  have hd := (hasDerivAt_clm_apply_real hdW (hA hθ)).const_smul
    (-(Complex.I / vacuumWeight))
  have hu := transport_mul_adjoint hK hW hc
  have hWA : W θ (A θ) = g θ • basisVec 0 := by
    rw [map_smul, ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]
  convert hd using 1
  · rfl
  dsimp [physicalDrivenVector]
  rw [ContinuousLinearMap.mul_apply, hWA, map_smul, smul_add, smul_smul]

/-- The actual driven vector satisfies the genuine integral equation for
integrable forcing. This is derived from its AC construction and a.e.
driven derivative, including its true zero initial value. -/
theorem physicalDrivenVector_integral_eq_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    physicalDrivenVector W g θ = ∫ s in (0 : ℝ)..θ,
      transportCoeff γ E s (physicalDrivenVector W g s) +
        (-(Complex.I / vacuumWeight) * g s) • basisVec 0 := by
  have hC : Continuous (transportCoeff γ E) := by
    
    
    unfold transportCoeff
    fun_prop
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  
  have hgi : IntegrableOn g angleInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  
  have heq := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
    (((hC.continuousOn.clm_apply hy).integrableOn_Icc).add ((hgi.const_mul (-(Complex.I / vacuumWeight))).smul_const (basisVec 0)))
    (physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg)
  simpa using heq θ hθ

/-- Every actual row, including the specially normalized zeroth row, is
absolutely continuous for integrable forcing. -/
theorem physicalDrivenRow_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (n : ℕ) :
    AbsolutelyContinuousOnInterval (physicalDrivenRow (physicalDrivenVector W g) n)
      0 anglePeriod := by
  have hac := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec n))
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
  by_cases hn : n = 0
  · subst n
    have h := hac.const_smul (Real.sqrt 2)
    simp [inner_basisVec, smul_eq_mul] at h
    
    exact h
  · have he : physicalDrivenRow (physicalDrivenVector W g) n =
        fun s : ℝ => (physicalDrivenVector W g s : ℕ → ℂ) n := by
      funext s
      simp only [physicalDrivenRow, if_neg hn]
    simpa [he, inner_basisVec] using hac

theorem physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (n : ℕ) :
    AbsolutelyContinuousOnInterval (physicalDrivenScaledRow E (physicalDrivenVector W g) n)
      0 anglePeriod := by
  
  exact (physicalDrivenRow_absolutelyContinuous_of_intervalIntegrable hK hW g hg n).const_smul
      (physicalDrivenQ E ^ n)

/-- Positive physical scaled rows are absolutely continuous images of the
constructed vector. This retains the actual sqrt(2) zeroth-row normalization. -/
theorem physicalDrivenScaledRow_succ_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (n : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 1)) 0 anglePeriod := by
  
  have h := (absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec (n + 1)))
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)).const_smul (physicalDrivenQ E ^ (n + 1))
  simp [inner_basisVec, smul_eq_mul] at h
  
  exact h

/-- The direct forcing cancels in the positive rows. Their a.e. derivative
has an actual continuous right-hand side. -/
theorem physicalDrivenScaledRow_succ_ae_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (n : ℕ) :
    ∀ᵐ θ, θ ∈ angleInterior →
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
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (n : ℕ)
    {θ : ℝ} (hθ : θ ∈ angleInterior) :
    HasDerivAt (physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 1))
      (deriv γ θ * physicalDrivenScaledRow E (physicalDrivenVector W g) (n + 2) θ +
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenScaledRow E (physicalDrivenVector W g) n θ) θ := by
  let y := physicalDrivenVector W g
  let d  := fun t => deriv γ t * physicalDrivenScaledRow E y (n + 2) t +
    physicalDrivenQ E ^ 2 * conj (deriv γ t) * physicalDrivenScaledRow E y n t
  
  have hc (k : ℕ) : ContinuousOn (physicalDrivenScaledRow E y k) angleInterval :=
    continuousOn_const.mul (physicalDrivenRow_continuousOn y (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg) k)
  have hd : ContinuousOn d angleInterval :=
    (by fun_prop)
  
  have htc := Ioo_subset_Icc_self hθ
  
  haveI : Fact (θ ∈ angleInterval) := ⟨htc⟩
  have hprim := intervalIntegral.integral_hasDerivWithinAt_right
    (s := angleInterval) 
    ((hd.mono (by
      rw [uIcc_of_le htc.1]
      exact Icc_subset_Icc le_rfl htc.2)).intervalIntegrable)
    (hd.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc θ) (hd θ htc)
  
  refine ((hprim.hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)).const_add
    (physicalDrivenScaledRow E y (n + 1) 0)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  exact (eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenScaledRow_succ_absolutelyContinuous_of_intervalIntegrable hK hW g hg n)
    hd.integrableOn_Icc
    (physicalDrivenScaledRow_succ_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg n)) t (Ioo_subset_Icc_self ht)

/-- The actual finite factorial gauge derivative follows from the positive
row equations. Integrable forcing contributes no pointwise forcing term. -/
theorem physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod)
    {θ : ℝ} (hθ : θ ∈ angleInterior) (j N : ℕ) :
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
    
    
    have ht := (physicalDrivenPower_hasDerivAt_succ hγ N θ).mul (physicalDrivenScaledRow_hasDerivAt_succ_of_intervalIntegrable hK hγ hW g hg
      (N + j + 1) hθ)
    have he (k : ℕ) : physicalDrivenGaugePartial γ E (physicalDrivenVector W g) k (N + 1) =
        fun s => physicalDrivenGaugePartial γ E (physicalDrivenVector W g) k N s +
          physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) k (N + 1) s := by
      funext s
      exact Finset.sum_range_succ _ _
    rw [he]
    convert ih.add ht using 1
    · funext s
      simp [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · rw [he]
      simp only [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      ring

theorem physicalDrivenMomentPartial_recurrence_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (hO : observationAdj W g = 0) (j N m : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E (physicalDrivenVector W g) j N m +
      (m : ℂ) * physicalDrivenMomentPartial γ E (physicalDrivenVector W g) (j + 1) N (m - 1) =
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
  have hpower : Continuous (physicalDrivenPower γ N) := by
    exact ((hγ.continuous.sub continuous_const).neg.pow N).div_const (N.factorial : ℂ)
  have ht : ContinuousOn t angleInterval :=
    ((hγ.continuous_deriv_one.mul hpower).continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy (N + j + 2)))).mul
        (by fun_prop)
  
  have hd (θ : ℝ) (hθ : θ ∈ angleInterior) :
      HasDerivAt (fun s => p s * z s ^ m) (r θ) θ := by
    
    have hdz : HasDerivAt z (conj (deriv γ θ)) θ := by
      simpa only [z, physicalDrivenCentered, Complex.star_def] using
        ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
    convert (physicalDrivenGaugePartial_hasDerivAt_of_intervalIntegrable hK hγ hW g hg hθ j N).mul (hdz.pow m) using 1
    simp <;> ring
  have hsub : uIcc 0 anglePeriod ⊆ angleInterval := by
    rw [uIcc_of_le Real.two_pi_pos.le]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.two_pi_pos.le
    ((by fun_prop)) hd ((((continuousOn_const.mul ha).add (continuousOn_const.mul hb)).add ht).mono hsub).intervalIntegrable
  have hp0 : p 0 = 0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
    (physicalDrivenVector_zero W g)
  have hpL : p anglePeriod = 0 := physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y _ _
    (physicalDrivenVector_endpoint W g hO)
  
  simp only [hp0, hpL, zero_mul, sub_self] at hi
  have hia : IntervalIntegrable a volume 0 anglePeriod :=
    (ha.mono hsub).intervalIntegrable
  have hib : IntervalIntegrable b volume 0 anglePeriod :=
    (hb.mono hsub).intervalIntegrable
  
  dsimp [r] at hi
  rw [intervalIntegral.integral_add ((hia.const_mul _).add (hib.const_mul _)) ((ht.mono hsub).intervalIntegrable),
    intervalIntegral.integral_add (hia.const_mul _) (hib.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  exact eq_neg_of_add_eq_zero_left hi

theorem physicalDrivenMoment_recurrence_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (hO : observationAdj W g = 0) (j m : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E (physicalDrivenVector W g) j m +
      (m : ℂ) * physicalDrivenMoment γ E (physicalDrivenVector W g) (j + 1) (m - 1) = 0 := by
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hj := physicalDrivenMomentPartial_tendsto γ hγ E _ hy j m
  have hj' := physicalDrivenMomentPartial_tendsto γ hγ E _ hy (j + 1) (m - 1)
  have ht := physicalDrivenTailMoment_tendsto_zero γ hγ E _ hy j m
  
  have hr : Tendsto (fun N => physicalDrivenQ E ^ 2 *
      physicalDrivenMomentPartial γ E (physicalDrivenVector W g) j N m + (m : ℂ) *
        physicalDrivenMomentPartial γ E (physicalDrivenVector W g) (j + 1) N (m - 1))
      atTop (𝓝 0) := by
    simpa only [physicalDrivenMomentPartial_recurrence_of_intervalIntegrable hK hγ hW g hg hO, neg_zero] using ht.neg
  exact tendsto_nhds_unique ((tendsto_const_nhds.mul hj).add (tendsto_const_nhds.mul hj')) hr

theorem physicalDrivenMoment_eq_zero_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} (hE : 0 < E) {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (hO : observationAdj W g = 0) (j m : ℕ) :
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
    {W : TransportPath} (hW : ContinuousOn W angleInterval)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (hO : observationAdj W g = 0) (j : ℕ) :
    Continuous (physicalDrivenPeriodicGauge γ E W g j) := by
  obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO j
  exact (AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
    (physicalDrivenGauge_continuousOn γ hγ E _
      (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) j)).comp (AddCircle.continuous_mk' _)

theorem localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω) (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (himage : Φ.domain = Ω) {K : NNReal}
    (hK : LipschitzWith K Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ)
    (hg : IntervalIntegrable g volume 0 anglePeriod) (hO : observationAdj W g = 0) (j : ℕ) :
    IsNonpositiveFourierSupport (angleCoeff
      (physicalDrivenPeriodicGauge Φ.boundary E W g j)) := by
  have hγ  :=
    Φ.boundaryC1
  apply localConformal_physicalMoments_nonpositive hb hΩ Φ hhol hinj hnz himage
    (physicalDrivenPeriodicGauge Φ.boundary E W g j)
    (physicalDrivenPeriodicGauge_continuous_of_intervalIntegrable _ hγ.continuous E hW.1 g hg hO j)
    (physicalDrivenPeriodicGauge_periodic _ E W g j)
  intro m
  
  calc
    _ = physicalDrivenMoment Φ.boundary E (physicalDrivenVector W g) j m := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le Real.two_pi_pos.le] at hθ
      dsimp only
      rw [physicalDrivenPeriodicGauge_eqOn _ E W g hO j hθ]
      simp [physicalDrivenCentered]
    _ = 0 := (physicalDrivenMoment_eq_zero_of_intervalIntegrable hK hγ hE hW g hg hO j m)

/-- A genuine L² load on the physical parameter interval is integrable;
the interval has its actual finite Lebesgue measure. -/
theorem intervalIntegrable_boundary_of_memLp
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure) :
    IntervalIntegrable g volume 0 anglePeriod := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact MemLp.integrable (by norm_num) hg

theorem intervalIntegrable_boundaryL2 (g : BoundaryL2) :
    IntervalIntegrable (g : ℝ → ℂ) volume 0 anglePeriod :=
  intervalIntegrable_boundary_of_memLp _ (Lp.memLp g)

/-- Actual L² forcing gives the original-H nonpositive Fourier support
criterion in the supplied conformal coordinates. -/
theorem localConformal_physicalDrivenGauge_nonpositive_of_memLp {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω) (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (himage : Φ.domain = Ω) {K : NNReal}
    (hK : LipschitzWith K Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) (j : ℕ) :
    IsNonpositiveFourierSupport (angleCoeff
      (physicalDrivenPeriodicGauge Φ.boundary E W g j)) :=
  localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable hb hΩ Φ hhol hinj hnz himage hK hE hW g (intervalIntegrable_boundary_of_memLp g hg) hO j

end PolyaNeumann

end
