module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.PhysicalDrivenReconstruction
public import RequestProject.FourierLipschitz
public import RequestProject.CutFourier
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import RequestProject.PlanarNotation

/-!
# Actual zeroth driven gauge with L² forcing

The exceptional zeroth row is differentiated with its true `sqrt 2`
normalization. Finite factorial gauges are integrated by the actual
Banach-valued absolutely-continuous FTC. Their genuine summable tails
then give an integral representation of the zeroth gauge with an L²
derivative. Complex Fourier integration by parts and averaged Parseval
give H¹ coefficients, and hence the half-order coefficients required by
the physical Hardy extension. No regularity of an unknown kernel vector
or approximation within that kernel is assumed.

This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate

section

variable (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ) (g : ℝ → ℂ) (y : ℝ → Ell2)
    (hy : ContinuousOn y angleInterval) (l : ℕ) (θ : ℝ)

/-- The exceptional physical row contains twice the positive-row coupling
and the actual unscaled forcing `-i g`. -/
theorem physicalDrivenScaledRow_hasDerivAt_zero {θ : ℝ}
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ) +
      (-(Complex.I / vacuumWeight) * g θ) • basisVec 0) θ) :
    HasDerivAt (physicalDrivenScaledRow E y 0)
      (2 * deriv γ θ * physicalDrivenScaledRow E y 1 θ - Complex.I * g θ) θ := by
  have hd := (((innerSL ℂ (basisVec 0)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    θ hy).const_mul vacuumWeight
  change HasDerivAt (fun s : ℝ => vacuumWeight * inner ℂ (basisVec 0) (y s))
    (vacuumWeight * inner ℂ (basisVec 0) (transportCoeff γ E θ (y θ) +
      (-(Complex.I / vacuumWeight) * g θ) • basisVec 0)) θ at hd
  simp only [inner_basisVec] at hd
  have hs : vacuumWeight ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : vacuumWeight ≠ 0 := by
    simp
  have hcoup (a b c : ℂ) :
      vacuumWeight * (a * (b * (vacuumWeight * c))) = 2 * b * (a * c) := calc
      _ = vacuumWeight ^ 2 * (b * (a * c)) := by ring
      _ = _ := by rw [hs]; ring
  have hforce : vacuumWeight * (-(Complex.I / vacuumWeight) * g θ) =
      -Complex.I * g θ := by
    field_simp [hs0]
  have he : physicalDrivenScaledRow E y 0 =
      fun s : ℝ => vacuumWeight * (y s : ℕ → ℂ) 0 := by
    funext s
    simp [physicalDrivenScaledRow, physicalDrivenRow, pow_zero, if_true]
  rw [he]
  apply hd.congr_deriv
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, if_true, mul_one]
  rw [transportCoeff_apply_coord, shiftN_apply_zero]
  simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_one, physicalDrivenQ,
    Nat.one_ne_zero, if_false, shiftWeight, if_true, mul_zero, add_zero]
  rw [mul_add, hcoup, hforce]
  ring

/-- The exceptional zeroth row has its actual a.e. forced derivative for
merely interval-integrable data. -/
theorem physicalDrivenScaledRow_zero_ae_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (physicalDrivenScaledRow E (physicalDrivenVector W g) 0)
        (2 * deriv γ θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ -
          Complex.I * g θ) θ := by
  filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg]
    with θ hθ hmem
  exact physicalDrivenScaledRow_hasDerivAt_zero γ E g _ (hθ hmem)

include E l y γ θ in
/-- The shifted factorial term occurring only in the exceptional gauge. -/
def physicalDrivenShiftedGaugeTerm : ℂ :=
  physicalDrivenPower γ (l + 1) θ * physicalDrivenScaledRow E y l θ

include E y γ θ in
def physicalDrivenShiftedGauge : ℂ :=
  ∑' l : ℕ, physicalDrivenShiftedGaugeTerm γ E y l θ

private theorem physicalDrivenShiftedGaugeTerm_mul_nat :
    physicalDrivenShiftedGaugeTerm γ E y l θ * ((l + 1 : ℕ) : ℂ) =
      -physicalDrivenCentered γ θ * physicalDrivenGaugeTerm γ E y 0 l θ := by
  simp only [physicalDrivenShiftedGaugeTerm, physicalDrivenGaugeTerm,
    Nat.add_zero, physicalDrivenPower, Nat.factorial_succ, pow_succ]
  
  
  push_cast
  field_simp [(by exact_mod_cast (by omega : l + 1 ≠ 0)), (by exact_mod_cast Nat.factorial_ne_zero l)]

theorem norm_physicalDrivenShiftedGaugeTerm_le :
    ‖physicalDrivenShiftedGaugeTerm γ E y l θ‖ ≤
      ‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenGaugeTerm γ E y 0 l θ‖ := by
  have h := congrArg norm (physicalDrivenShiftedGaugeTerm_mul_nat γ E y l θ)
  simp only [norm_mul, Complex.norm_natCast, norm_neg] at h
  have hn : (1 : ℝ) ≤ (l + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ l + 1)
  have ha := norm_nonneg (physicalDrivenShiftedGaugeTerm γ E y l θ)
  nlinarith

include hy hγ in
theorem physicalDrivenShiftedGaugeTerm_continuousOn :
    ContinuousOn (physicalDrivenShiftedGaugeTerm γ E y l) angleInterval := by
  have hp : Continuous (physicalDrivenPower γ (l + 1)) := by
    unfold physicalDrivenPower physicalDrivenCentered
    fun_prop
  exact hp.continuousOn.mul
    (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy l))

include hy hγ in
theorem exists_physicalDrivenShiftedGaugeTerm_majorant :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ l θ, θ ∈ angleInterval →
      ‖physicalDrivenShiftedGaugeTerm γ E y l θ‖ ≤ u l := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenGaugeTerm_majorant γ hγ E y hy 0
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.sub continuous_const : Continuous (physicalDrivenCentered γ)).continuousOn
  have hR0  := (norm_nonneg _).trans (hR 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  refine ⟨fun l => R * u l, hu.mul_left R, ?_⟩
  intro l θ hθ
  exact (norm_physicalDrivenShiftedGaugeTerm_le γ E y l θ).trans
    ((by bound))

include hy hγ in
theorem physicalDrivenShiftedGauge_continuousOn :
    ContinuousOn (physicalDrivenShiftedGauge γ E y) angleInterval := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenShiftedGaugeTerm_majorant γ hγ E y hy
  
  apply (HasSumUniformlyOn.of_norm_le_summable hu hbd).tendstoUniformlyOn.continuousOn
  exact (Eventually.of_forall fun s : Finset ℕ => continuousOn_finset_sum s
    (fun l _ => physicalDrivenShiftedGaugeTerm_continuousOn γ hγ E y hy l)).frequently

include hy hγ in
theorem physicalDrivenShiftedGauge_weightedIntegral_hasSum_to (w : ℝ → ℂ)
    (hw : ContinuousOn w angleInterval) {θ : ℝ}
    (hθ : θ ∈ angleInterval) :
    HasSum (fun l : ℕ => ∫ s in (0 : ℝ)..θ,
      w s * physicalDrivenShiftedGaugeTerm γ E y l s)
      (∫ s in (0 : ℝ)..θ, w s * physicalDrivenShiftedGauge γ E y s) := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenShiftedGaugeTerm_majorant γ hγ E y hy
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hC0  := (norm_nonneg _).trans (hC 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hsub : uIoc 0 θ ⊆ angleInterval := by
    rw [uIoc_of_le hθ.1]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hθ.2)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
     (bound := fun l _ => C * u l) ?_ ?_ ?_ intervalIntegrable_const ?_
  · intro l
    exact ((hw.mul (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ E y hy l)).mono
      hsub).aestronglyMeasurable measurableSet_uIoc
  · intro l
    exact Eventually.of_forall fun s hs => by
      rw [norm_mul]
      exact mul_le_mul (hC s (hsub hs)) (hbd l s (hsub hs)) (norm_nonneg _) hC0
  · exact Eventually.of_forall fun _ _ => hu.mul_left C
  · refine Eventually.of_forall fun s hs => ?_
    
    exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => hbd l s (hsub hs)) hu).of_norm.hasSum.mul_left (w s)

theorem driven_c1_absolutelyContinuous {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    AbsolutelyContinuousOnInterval f 0 anglePeriod := hf.contDiffOn.absolutelyContinuousOnInterval

theorem driven_ac_congr {f h : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 anglePeriod)
    (he : EqOn f h angleInterval) :
    AbsolutelyContinuousOnInterval h 0 anglePeriod := hf.congr (by simpa only [uIcc_of_le Real.two_pi_pos.le] using he)

theorem physicalDrivenGaugePartial_zero_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) (N : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 N) 0 anglePeriod := by
  have ht (l : ℕ) : AbsolutelyContinuousOnInterval
      (physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 0 l) 0 anglePeriod := by
    have hp : ContDiff ℝ 1 (physicalDrivenPower γ l) := by
      exact ((hγ.sub contDiff_const).neg.pow l).div_const _
    have h_simpa := (driven_c1_absolutelyContinuous hp).smul
      (physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable hK hW g hg l)
    exact h_simpa
  induction N with
  | zero =>
      have he : physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 0 =
          physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 0 0 := by
        exact Finset.sum_range_one _
      simp [*]
  | succ N ih =>
      have he : physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 (N + 1) =
          fun s => physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 N s +
            physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 0 (N + 1) s := by
        funext s
        exact Finset.sum_range_succ _ _
      rw [he]
      exact ih.add (ht (N + 1))

/-- Finite exceptional-gauge cancellation, retaining its true tail and
the forcing at frequency zero. -/
theorem physicalDrivenGaugePartial_zero_hasDerivAt
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (E : ℝ) (g : ℝ → ℂ) (y : ℝ → Ell2)
    {θ : ℝ} (hy : HasDerivAt y (transportCoeff γ E θ (y θ) +
      (-(Complex.I / vacuumWeight) * g θ) • basisVec 0) θ) (N : ℕ) :
    HasDerivAt (physicalDrivenGaugePartial γ E y 0 N)
      (deriv γ θ * physicalDrivenScaledRow E y 1 θ - Complex.I * g θ +
        deriv γ θ * physicalDrivenGaugeTerm γ E y 1 N θ +
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l θ) θ := by
  induction N with
  | zero =>
      have he : physicalDrivenGaugePartial γ E y 0 0 = physicalDrivenScaledRow E y 0 := by
        funext s
        simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower]
      rw [he]
      apply (physicalDrivenScaledRow_hasDerivAt_zero γ E g y hy).congr_deriv
      simp [Finset.range_zero, Finset.sum_empty, mul_zero, physicalDrivenGaugeTerm, physicalDrivenPower, pow_zero, Nat.factorial_zero, div_one, Nat.zero_add]
      ring
  | succ N ih =>
      
      
      have he : physicalDrivenGaugePartial γ E y 0 (N + 1) =
          fun s => physicalDrivenGaugePartial γ E y 0 N s +
            physicalDrivenGaugeTerm γ E y 0 (N + 1) s := by
        funext s
        exact Finset.sum_range_succ _ _
      have hf : (fun s => physicalDrivenGaugePartial γ E y 0 N s +
          physicalDrivenGaugeTerm γ E y 0 (N + 1) s) =
          physicalDrivenGaugePartial γ E y 0 N +
            physicalDrivenPower γ (N + 1) * physicalDrivenScaledRow E y (N + 1) := by
        rfl
      rw [he, hf]
      apply (ih.add ((physicalDrivenPower_hasDerivAt_succ hγ N θ).mul (physicalDrivenScaledRow_hasDerivAt_succ γ E g y hy N))).congr_deriv
      rw [Finset.sum_range_succ]
      simp only [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm]
      ring

include E y γ θ in
/-- The continuous part of the actual derivative of gauge zero. -/
def physicalDrivenGaugeZeroContinuousPart : ℂ :=
  deriv γ θ * physicalDrivenScaledRow E y 1 θ +
    physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenShiftedGauge γ E y θ

end

theorem physicalDrivenGaugeZeroContinuousPart_continuousOn
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y angleInterval) :
    ContinuousOn (physicalDrivenGaugeZeroContinuousPart γ E y) angleInterval := (hγ.continuous_deriv_one.continuousOn.mul
    (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy 1))).add
      ((continuousOn_const.mul
        (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn).mul
        (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E y hy))

theorem memLp_angle_of_continuousOn {f : ℝ → ℂ}
    (hf : ContinuousOn f angleInterval) :
    MemLp f 2 angleMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    C ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc (by grind)

private theorem physicalDrivenGaugePartial_zero_primitive
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod)
    (N : ℕ) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    physicalDrivenGaugePartial γ E (physicalDrivenVector W g) 0 N θ =
      (∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 s - Complex.I * g s) +
      (∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenGaugeTerm γ E (physicalDrivenVector W g) 1 N s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ,
        conj (deriv γ s) *
          ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E (physicalDrivenVector W g) l s) := by
  classical
  let y := physicalDrivenVector W g
  let a  := fun s => deriv γ s * physicalDrivenScaledRow E y 1 s - Complex.I * g s
  let t  := fun s => deriv γ s * physicalDrivenGaugeTerm γ E y 1 N s
  let b  := fun s => conj (deriv γ s) *
    ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l s
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  
  have hgi : IntegrableOn g angleInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
  have ha : IntegrableOn a angleInterval :=
    (hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy 1))).integrableOn_Icc.sub (hgi.const_mul Complex.I)
  have ht : ContinuousOn t angleInterval := hγ.continuous_deriv_one.continuousOn.mul
    (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E y hy 1 N)
  have hb : ContinuousOn b angleInterval :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (continuousOn_finset_sum _ fun l _ =>
        physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E y hy l)
  
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (physicalDrivenGaugePartial_zero_absolutelyContinuous_of_intervalIntegrable hK hγ hW g hg N)
    ((ha.add ht.integrableOn_Icc).add (hb.integrableOn_Icc.const_mul (physicalDrivenQ E ^ 2))) (by
      filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg]
        with s hs hmem
      simpa [a, t, b, mul_assoc] using physicalDrivenGaugePartial_zero_hasDerivAt hγ E g y (hs hmem) N) θ hθ
  
  rw [(physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero γ E y 0 N
    (physicalDrivenVector_zero W g)), zero_add] at he
  have hsub : uIcc 0 θ ⊆ angleInterval := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have hia  := (ha.mono_set hsub).intervalIntegrable
  have hit : IntervalIntegrable t volume 0 θ := (ht.mono hsub).intervalIntegrable
  
  simp at he
  rw [intervalIntegral.integral_add (hia.add hit) (((hb.mono hsub).intervalIntegrable).const_mul _),
    intervalIntegral.integral_add hia hit, intervalIntegral.integral_const_mul] at he
  exact he

/-- Actual integral representation of gauge zero. The continuous term is
constructed from the genuine rows; the forcing remains `-i g`. -/
theorem physicalDrivenGauge_zero_primitive_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    physicalDrivenGauge γ E (physicalDrivenVector W g) 0 θ =
      ∫ s in (0 : ℝ)..θ,
        physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) s - Complex.I * g s := by
  classical
  let y := physicalDrivenVector W g
  let a  := fun s => deriv γ s * physicalDrivenScaledRow E y 1 s - Complex.I * g s
  let b  := fun s => conj (deriv γ s) * physicalDrivenShiftedGauge γ E y s
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg
  have hp : Tendsto (fun N : ℕ => physicalDrivenGaugePartial γ E y 0 N θ) atTop
      (𝓝 (physicalDrivenGauge γ E y 0 θ)) := by
    have h_simpa := ((summable_norm_physicalDrivenGaugeTerm γ E y 0 θ).of_norm.hasSum.tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)
    exact h_simpa
  have ht := (physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E y hy 1
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero
  have hs := physicalDrivenShiftedGauge_weightedIntegral_hasSum_to γ hγ.continuous E y hy
    (fun s => conj (deriv γ s))
    (by fun_prop) hθ
  have hsub : uIcc 0 θ ⊆ angleInterval := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have he (N : ℕ) : (∫ s in 0..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l s) =
      ∑ l ∈ Finset.range N, ∫ s in 0..θ,
        conj (deriv γ s) * physicalDrivenShiftedGaugeTerm γ E y l s := by
    simp_rw [Finset.mul_sum]
    apply intervalIntegral.integral_finset_sum
    intro l _
    exact (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E y hy l)).mono
        hsub).intervalIntegrable
  have hb  :=
    hs.tendsto_sum_nat.congr' (Eventually.of_forall fun N => (he N).symm)
  have hr : Tendsto (fun N : ℕ => (∫ s in (0 : ℝ)..θ, a s) +
      (∫ s in (0 : ℝ)..θ, deriv γ s * physicalDrivenGaugeTerm γ E y 1 N s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        ∑ l ∈ Finset.range N, physicalDrivenShiftedGaugeTerm γ E y l s)) atTop
      (𝓝 ((∫ s in (0 : ℝ)..θ, a s) + physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, b s))) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := ∫ s in (0 : ℝ)..θ, a s)).add ht).add
        (hb.const_mul (physicalDrivenQ E ^ 2))
  have hlim  :=
    tendsto_nhds_unique hp (hr.congr' (Eventually.of_forall fun N =>
      (physicalDrivenGaugePartial_zero_primitive hK hγ hW g hg N hθ).symm))
  have ha : IntervalIntegrable a volume 0 θ := by
    
    have hgt  := hg.mono_set (by
      simpa only [uIcc_of_le Real.two_pi_pos.le] using hsub)
    exact (((hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy 1))).mono hsub).intervalIntegrable).sub (hgt.const_mul Complex.I)
  have hbi : IntervalIntegrable b volume 0 θ :=
    (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E y hy)).mono
        hsub).intervalIntegrable
  rw [hlim, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ha (hbi.const_mul _)]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [a, b, physicalDrivenGaugeZeroContinuousPart]
  ring

theorem physicalDrivenGauge_zero_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) 0 anglePeriod := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg)
  
  apply driven_ac_congr (absolutelyContinuousOnInterval_intervalIntegral_banach (by
    have hcc : ContinuousOn (physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g))
        (uIcc 0 anglePeriod) := by simpa only [uIcc_of_le Real.two_pi_pos.le] using hc
    exact hcc.intervalIntegrable.sub (hg.const_mul Complex.I))
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩))
  intro θ hθ
  exact (physicalDrivenGauge_zero_primitive_of_intervalIntegrable hK hγ hW g hg hθ).symm

theorem physicalDrivenGauge_zero_ae_hasDerivAt_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 anglePeriod) :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (physicalDrivenGauge γ E (physicalDrivenVector W g) 0)
        (physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) θ -
          Complex.I * g θ) θ := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg)
  
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le (by
    have hcc : ContinuousOn (physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g))
        (uIcc 0 anglePeriod) := by simpa only [uIcc_of_le Real.two_pi_pos.le] using hc
    exact hcc.intervalIntegrable.sub (hg.const_mul Complex.I))]
    with θ hθ hmem
  refine (hθ hmem).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs
  exact physicalDrivenGauge_zero_primitive_of_intervalIntegrable hK hγ hW g hg
    (Ioo_subset_Icc_self hs)

/-- The derivative of the actual zeroth gauge is L² for actual L² forcing. -/
theorem physicalDrivenGauge_zero_derivative_memLp
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure) :
    MemLp (fun θ => physicalDrivenGaugeZeroContinuousPart γ E (physicalDrivenVector W g) θ -
      Complex.I * g θ) 2 angleMeasure := by
  
  exact (memLp_angle_of_continuousOn (physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g
      (intervalIntegrable_boundary_of_memLp g hg)))).sub (hg.const_smul Complex.I)

/-- Genuine complex Fourier integration by parts for an absolutely
continuous function and its actual a.e. derivative. This includes mode
zero and uses the averaged Fourier normalization. -/
theorem fourierCoeffOn_of_ac_ae_hasDerivAt
    {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 anglePeriod)
    (hf' : MemLp f' 2 angleMeasure)
    (hd : ∀ᵐ θ, θ ∈ angleInterior → HasDerivAt f (f' θ) θ)
    (hp : f 0 = f anglePeriod) (n : ℤ) :
    angleCoeff f' n =
      (Complex.I * (n : ℂ)) * angleCoeff f n := by
  let e : ℝ → ℂ := fun θ => fourier (-n) (θ : ParamCircle)
  let α  := -(Complex.I * n)
  have hec : Continuous e := (by fun_prop)
  have hen (θ : ℝ)  := norm_fourier_coe (-n) θ
  have he1 : ContDiff ℝ 1 e := by
    dsimp only [e]
    simp_rw [hardy_fourier_exp]
    
    exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp
  have heD (θ : ℝ) : HasDerivAt e (α * e θ) θ := by
    have hα : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) /
        ((anglePeriod : ℝ) : ℂ) = α := by
      dsimp only [α]
      push_cast
      field_simp [Real.pi_ne_zero]
    simpa only [hα] using hasDerivAt_fourier_neg anglePeriod n θ
  have hfC : ContinuousOn f angleInterval := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  
  have hf'i : IntegrableOn f' angleInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact MemLp.integrable (by norm_num) hf'
  have hfe : IntegrableOn (fun θ => f θ * e θ) angleInterval :=
    hfC.integrableOn_Icc.mul_bdd hec.aestronglyMeasurable.restrict
      (Eventually.of_forall fun θ => (hen θ).le)
  have hf'e : IntegrableOn (fun θ => f' θ * e θ) angleInterval :=
    hf'i.mul_bdd hec.aestronglyMeasurable.restrict
      (Eventually.of_forall fun θ => (hen θ).le)
  
  have hprodD : ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (fun θ => f θ * e θ) (f' θ * e θ + α * (f θ * e θ)) θ := by
    filter_upwards [hd] with θ hθ hmem
    convert (hθ hmem).mul (heD θ) using 1; ring
  have hprodI : IntegrableOn (fun θ => f' θ * e θ + α * (f θ * e θ))
      angleInterval := hf'e.add (hfe.const_mul α)
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (by
      exact hf.smul (driven_c1_absolutelyContinuous he1)) hprodI hprodD anglePeriod ⟨Real.two_pi_pos.le, le_rfl⟩
  have he0 : e 0 = 1 := by
    change fourier (-n) ((0 : ℝ) : ParamCircle) = 1
    simp
  have heL : e anglePeriod = 1 := by
    have hper : ((anglePeriod : ℝ) : ParamCircle) = 0 := by
      simp
    change fourier (-n) ((anglePeriod : ℝ) : ParamCircle) = 1
    simp [*]
  have hi0 : (∫ₚ θ,
      f' θ * e θ + α * (f θ * e θ)) = 0 := by
    rw [he0, heL, mul_one, mul_one, ← hp] at hFTC
    exact add_left_cancel (show f 0 + (∫ₚ θ,
      f' θ * e θ + α * (f θ * e θ)) = f 0 + 0 from by
        simpa only [add_zero] using hFTC.symm)
  have hife : IntervalIntegrable (fun θ => f θ * e θ) volume 0 anglePeriod := by
    apply IntegrableOn.intervalIntegrable
    simpa [uIcc_of_le Real.two_pi_pos.le] using hfe
  
  rw [intervalIntegral.integral_add (by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf'e) (hife.const_mul α),
    intervalIntegral.integral_const_mul] at hi0
  have hi : (∫ₚ θ, f' θ * e θ) =
      (Complex.I * (n : ℂ)) * (∫ₚ θ, f θ * e θ) := by
    dsimp only [α] at hi0
    exact eq_of_sub_eq_zero (by simpa only [neg_mul, ← sub_eq_add_neg] using hi0)
  have hi' : (∫ₚ θ, e θ * f' θ) =
      (Complex.I * (n : ℂ)) * (∫ₚ θ, e θ * f θ) := by
    simpa only [mul_comm] using hi
  simp only [e, fourier_coe_apply] at hi'
  simp only [fourierCoeffOn_eq_integral, smul_eq_mul, Complex.real_smul,
    fourier_coe_apply, sub_zero]
  rw [hi']
  ring

/-- Actual AC and an L² a.e. derivative give the project's true Fourier
H¹ sequence, using Parseval for both value and derivative. -/
theorem isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    {f f' : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 anglePeriod)
    (hf' : MemLp f' 2 angleMeasure)
    (hd : ∀ᵐ θ, θ ∈ angleInterior → HasDerivAt f (f' θ) θ)
    (hp : f 0 = f anglePeriod) :
    IsSobolevSeq 1 (angleCoeff f) := by
  have hfC : ContinuousOn f angleInterval := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hf.continuousOn
  
  
  have hdn (n : ℤ) : ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ 2 =
      n ^ 2 * ‖fourierCoeffOn Real.two_pi_pos f n‖ ^ 2 := by
    rw [fourierCoeffOn_of_ac_ae_hasDerivAt hf hf' hd hp n]
    simp [mul_pow]
  
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((((hasSum_sq_fourierCoeffOn Real.two_pi_pos
      (memLp_angle_of_continuousOn hfC)).summable).mul_left 2).add (((hasSum_sq_fourierCoeffOn Real.two_pi_pos hf').summable).mul_left 2))
  rw [hdn]
  simp only [sobWeight, Real.rpow_one]
  
  
  have hsq := sq_nonneg ((|(n : ℝ)| - 1) * ‖fourierCoeffOn Real.two_pi_pos f n‖)
  rw [← sq_abs (n : ℝ)]
  nlinarith

/-- The actual zeroth gauge of an L² driven observation-kernel vector has
H¹ coefficients. No Sobolev premise on that vector is needed. -/
theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_one
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    IsSobolevSeq 1 (angleCoeff (physicalDrivenPeriodicGauge γ E W g 0)) := by
  have hgi := intervalIntegrable_boundary_of_memLp g hg
  have hends := physicalDrivenGauge_actual_endpoints γ E W g hO 0
  have hreg := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalDrivenGauge_zero_absolutelyContinuous_of_intervalIntegrable hK hγ hW g hgi)
    (physicalDrivenGauge_zero_derivative_memLp hγ hW g hg)
    (physicalDrivenGauge_zero_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hgi)
    (hends.1.trans hends.2.symm)
  have hc (n : ℤ) : angleCoeff (physicalDrivenPeriodicGauge γ E W g 0) n =
      angleCoeff (physicalDrivenGauge γ E (physicalDrivenVector W g) 0) n := by
    simp only [fourierCoeffOn_eq_integral, sub_zero]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    dsimp only
    rw [physicalDrivenPeriodicGauge_eqOn γ E W g hO 0 hθ]
  exact hreg.congr fun n => by simp [*]

theorem physicalDrivenPeriodicGauge_zero_isSobolevSeq_half
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    IsSobolevSeq halfOrder
      (angleCoeff (physicalDrivenPeriodicGauge γ E W g 0)) :=
  (sobNormSq_mono (by norm_num)
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hK hγ hW g hg hO)).1

end PolyaNeumann

end
