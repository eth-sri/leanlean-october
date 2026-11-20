module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.PhysicalMomentHardyCriterion
public import RequestProject.CorrectedKernelSmooth
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import RequestProject.PlanarNotation

/-!
# Actual driven rows and their factorial boundary gauge

The zeroth physical row is `sqrt 2 * y₀`; every positive row is `yₙ`.
For `q = -i sqrt(E)/2`, the actual scaled positive rows satisfy
`dₙ' = γ' dₙ₊₁ + q² conj(γ') dₙ₋₁`.  This file proves that identity
from the genuine driven equation and proves the finite factorial gauge
cancellation, including its actual tail.  Absolute convergence and the
zero endpoint of the gauge are derived from actual Hilbert-space bounds
and the observation-adjoint kernel, respectively.

These are prerequisites for the physical moment criterion.  They do not
postulate the infinite gauge differential identity.  Dominated convergence
passes the finite moment recurrence to the actual factorial series; the
tail vanishes because its integral coefficients form a genuinely summable
series.  Induction then proves every physical antiholomorphic moment.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Topology

/-- The actual wave-number scalar in the transport coefficient. -/
def physicalDrivenQ (E : ℝ) : ℂ := -(Complex.I * (Real.sqrt E : ℂ)) / 2

theorem physicalDrivenQ_ne_zero {E : ℝ} (hE : 0 < E) : physicalDrivenQ E ≠ 0 := by
  
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (by positivity)))) (by norm_num)

theorem physicalDrivenQ_sq_ne_zero {E : ℝ} (hE : 0 < E) : physicalDrivenQ E ^ 2 ≠ 0 :=
  pow_ne_zero _ (physicalDrivenQ_ne_zero hE)

section

variable (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ) (W : TransportPath) (g : ℝ → ℂ)
    (hO : observationAdj W g = 0) (y : ℝ → Ell2) (hy : ContinuousOn y angleInterval)
    (n j ℓ N : ℕ) (θ : ℝ)

include W g θ in
/-- The actual driven vector with zero initial value, given by variation
of constants.  No terminal value is built into this definition. -/
def physicalDrivenVector : Ell2 :=
  (-(Complex.I / vacuumWeight)) •
    W θ (∫ s in (0 : ℝ)..θ, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))

@[simp] theorem physicalDrivenVector_zero :
    physicalDrivenVector W g 0 = 0 := by
  simp [physicalDrivenVector]

include hO in
/-- The terminal zero is a consequence of the actual adjoint observation
kernel, rather than an imposed periodic endpoint condition. -/
theorem physicalDrivenVector_endpoint : physicalDrivenVector W g anglePeriod = 0 := by
  change (-(Complex.I / vacuumWeight)) • W anglePeriod (observationAdj W g) = 0
  simp [hO]

include n y θ in
/-- The physical zeroth trace has its actual sqrt(2) normalization. -/
def physicalDrivenRow : ℂ :=
  if n = 0 then vacuumWeight * (y θ : ℕ → ℂ) 0 else (y θ : ℕ → ℂ) n

include E n y θ in
/-- Genuine scaled derivative data. -/
def physicalDrivenScaledRow : ℂ :=
  physicalDrivenQ E ^ n * physicalDrivenRow y n θ

/-- Positive driven rows, including the n=1 coupling to sqrt(2)y₀. -/
theorem physicalDrivenRow_hasDerivAt_succ {θ : ℝ}
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ) +
      (-(Complex.I / vacuumWeight) * g θ) • basisVec 0) θ) (n : ℕ) :
    HasDerivAt (physicalDrivenRow y (n + 1))
      (physicalDrivenQ E * (deriv γ θ * physicalDrivenRow y (n + 2) θ +
        conj (deriv γ θ) * physicalDrivenRow y n θ)) θ := by
  have hd := ((innerSL ℂ (basisVec (n + 1))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    θ hy
  change HasDerivAt (fun s : ℝ => inner ℂ (basisVec (n + 1)) (y s))
    (inner ℂ (basisVec (n + 1)) (transportCoeff γ E θ (y θ) +
      (-(Complex.I / vacuumWeight) * g θ) • basisVec 0)) θ at hd
  simp only [inner_basisVec] at hd
  have he : physicalDrivenRow y (n + 1) = fun s : ℝ => (y s : ℕ → ℂ) (n + 1) := by
    rfl
  rw [he]
  apply hd.congr_deriv
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    basisVec_coord, Nat.succ_ne_zero, if_false, mul_zero, add_zero]
  rw [transportCoeff_apply_coord, shiftN_apply_succ]
  cases n with
  | zero => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight]
  | succ n => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight]

/-- The exact recurrence used by the factorial cancellation. -/
theorem physicalDrivenScaledRow_hasDerivAt_succ {θ : ℝ}
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ) +
      (-(Complex.I / vacuumWeight) * g θ) • basisVec 0) θ) (n : ℕ) :
    HasDerivAt (physicalDrivenScaledRow E y (n + 1))
      (deriv γ θ * physicalDrivenScaledRow E y (n + 2) θ +
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenScaledRow E y n θ) θ := by
  convert (physicalDrivenRow_hasDerivAt_succ γ E g y hy n).const_mul
    (physicalDrivenQ E ^ (n + 1)) using 1
  · rfl
  simp [physicalDrivenScaledRow]
  ring

theorem norm_physicalDrivenRow_le :
    ‖physicalDrivenRow y n θ‖ ≤ 2 * ‖y θ‖ := by
  have hc (k : ℕ) := lp.norm_apply_le_norm (p := 2) (by norm_num) (y θ) k
  unfold physicalDrivenRow
  split_ifs
  · rw [norm_mul]
    
    refine mul_le_mul ?_ (hc 0) (norm_nonneg _) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp
  · exact (hc n).trans (by nlinarith [norm_nonneg (y θ)])

theorem norm_physicalDrivenScaledRow_le :
    ‖physicalDrivenScaledRow E y n θ‖ ≤ ‖physicalDrivenQ E‖ ^ n * (2 * ‖y θ‖) := by
  rw [physicalDrivenScaledRow, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (norm_physicalDrivenRow_le y n θ) (by positivity)

include γ θ in
/-- The actual centered physical coordinate, with no mean-zero assertion. -/
def physicalDrivenCentered : ℂ := γ θ - γ 0

include γ θ ℓ in
def physicalDrivenPower : ℂ :=
  (-physicalDrivenCentered γ θ) ^ ℓ / (ℓ.factorial : ℂ)

include E j y γ θ ℓ in
def physicalDrivenGaugeTerm : ℂ :=
  physicalDrivenPower γ ℓ θ * physicalDrivenScaledRow E y (ℓ + j) θ

include E j y γ θ in
/-- The actual boundary factorial series. -/
def physicalDrivenGauge : ℂ :=
  ∑' ℓ : ℕ, physicalDrivenGaugeTerm γ E y j ℓ θ

include E N j y γ θ in
/-- Finite sums contain indices 0,...,N, making the uncancelled tail explicit. -/
def physicalDrivenGaugePartial : ℂ :=
  ∑ ℓ ∈ Finset.range (N + 1), physicalDrivenGaugeTerm γ E y j ℓ θ

theorem physicalDrivenPower_hasDerivAt_succ
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (ℓ : ℕ) (θ : ℝ) :
    HasDerivAt (physicalDrivenPower γ (ℓ + 1))
      (-deriv γ θ * physicalDrivenPower γ ℓ θ) θ := by
  have hd := (((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).neg.pow
    (ℓ + 1)).div_const (ℓ + 1).factorial
  convert hd using 1
  · rfl
  simp only [physicalDrivenPower, physicalDrivenCentered, Pi.neg_apply,
    Nat.add_sub_cancel]
  rw [Nat.factorial_succ]
  
  
  push_cast
  field_simp [(by exact_mod_cast (by omega : ℓ + 1 ≠ 0)), (by exact_mod_cast (Nat.factorial_ne_zero ℓ))]

theorem norm_physicalDrivenGaugeTerm_le :
    ‖physicalDrivenGaugeTerm γ E y j ℓ θ‖ ≤
      (2 * ‖y θ‖ * ‖physicalDrivenQ E‖ ^ j) *
        ((‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenQ E‖) ^ ℓ / (ℓ.factorial : ℝ)) := by
  unfold physicalDrivenGaugeTerm
  rw [norm_mul]
  calc
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (norm_physicalDrivenScaledRow_le E y (ℓ + j) θ)
        (norm_nonneg _)
    _ = _ := by
      simp [physicalDrivenPower, norm_div, norm_pow, norm_neg, Complex.norm_natCast, pow_add, mul_pow]
      ring

/-- The factorial series is genuinely absolutely convergent at every point
for every actual Hilbert-space vector; no assumed row summability is used. -/
theorem summable_norm_physicalDrivenGaugeTerm :
    Summable (fun ℓ : ℕ => ‖physicalDrivenGaugeTerm γ E y j ℓ θ‖) := Summable.of_nonneg_of_le ((by norm_num))
    (norm_physicalDrivenGaugeTerm_le γ E y j · θ)
    ((Real.summable_pow_div_factorial
      (‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenQ E‖)).mul_left
        (2 * ‖y θ‖ * ‖physicalDrivenQ E‖ ^ j))

include hy hγ in
/-- On the compact parameter interval the genuine row bound gives one
summable majorant for the entire factorial gauge, independently of θ. -/
theorem exists_physicalDrivenGaugeTerm_majorant :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ ℓ θ, θ ∈ angleInterval →
      ‖physicalDrivenGaugeTerm γ E y j ℓ θ‖ ≤ u ℓ := by
  have h0 : 0 ∈ angleInterval := ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.sub continuous_const).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0)
  
  refine ⟨fun ℓ => (2 * M * ‖physicalDrivenQ E‖ ^ j) *
    ((R * ‖physicalDrivenQ E‖) ^ ℓ / ℓ.factorial),
    (Real.summable_pow_div_factorial _).mul_left _, ?_⟩
  intro ℓ θ hθ
  apply (norm_physicalDrivenGaugeTerm_le γ E y j ℓ θ).trans
  change (2 * ‖y θ‖ * ‖physicalDrivenQ E‖ ^ j) *
      ((‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenQ E‖) ^ ℓ / ℓ.factorial) ≤
    (2 * M * ‖physicalDrivenQ E‖ ^ j) *
      ((R * ‖physicalDrivenQ E‖) ^ ℓ / ℓ.factorial)
  gcongr
  · exact hM θ hθ
  · exact hR θ hθ

include hy in
theorem physicalDrivenRow_continuousOn :
    ContinuousOn (physicalDrivenRow y n) angleInterval := by
  have hc (k : ℕ) : ContinuousOn (fun θ => (y θ) k)
      angleInterval := by
    have h := (innerSL ℂ (basisVec k)).continuous.comp_continuousOn hy
    change ContinuousOn (fun θ : ℝ => inner ℂ (basisVec k) (y θ))
      angleInterval at h
    simpa [inner_basisVec] using h
  unfold physicalDrivenRow
  split_ifs
  · fun_prop
  · exact hc n

include hy hγ in
theorem physicalDrivenGaugeTerm_continuousOn :
    ContinuousOn (physicalDrivenGaugeTerm γ E y j ℓ) angleInterval := by
  have hp : Continuous (physicalDrivenPower γ ℓ) := by
    unfold physicalDrivenPower physicalDrivenCentered
    fun_prop
  exact hp.continuousOn.mul
    (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy (ℓ + j)))

include hy hγ in
/-- Genuine uniform convergence of the factorial gauge, from the actual
Hilbert-space row majorant. -/
theorem physicalDrivenGauge_hasSumUniformlyOn :
    HasSumUniformlyOn (physicalDrivenGaugeTerm γ E y j)
      (physicalDrivenGauge γ E y j) angleInterval := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenGaugeTerm_majorant γ hγ E y hy j
  exact HasSumUniformlyOn.of_norm_le_summable hu hbd

include hy hγ in
/-- The actual factorial gauge has a genuine continuous representative on
the entire closed parameter interval, including its endpoint values. -/
theorem physicalDrivenGauge_continuousOn :
    ContinuousOn (physicalDrivenGauge γ E y j) angleInterval := by
  apply (physicalDrivenGauge_hasSumUniformlyOn γ hγ E y hy j).tendstoUniformlyOn.continuousOn
  exact (Eventually.of_forall fun s : Finset ℕ =>
    continuousOn_finset_sum s (fun ℓ _ =>
      physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j ℓ)).frequently

/-- The actual gauge vanishes whenever the actual driven vector does. -/
theorem physicalDrivenGauge_eq_zero_of_vector_eq_zero {θ : ℝ} (hy : y θ = 0) :
    physicalDrivenGauge γ E y j θ = 0 := by
  unfold physicalDrivenGauge
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow, hy]
    _ = 0 := tsum_zero

include hO in
theorem physicalDrivenGauge_actual_endpoints :
    physicalDrivenGauge γ E (physicalDrivenVector W g) j 0 = 0 ∧
      physicalDrivenGauge γ E (physicalDrivenVector W g) j anglePeriod = 0 :=
  ⟨physicalDrivenGauge_eq_zero_of_vector_eq_zero γ E _ j (physicalDrivenVector_zero W g),
    physicalDrivenGauge_eq_zero_of_vector_eq_zero γ E _ j (physicalDrivenVector_endpoint W g hO)⟩

include hy hγ in
theorem physicalDrivenGaugePartial_continuousOn :
    ContinuousOn (physicalDrivenGaugePartial γ E y j N) angleInterval :=
  continuousOn_finset_sum _ (fun ℓ _ =>
    physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j ℓ)

end

section

variable (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y angleInterval) (W : TransportPath) (g : ℝ → ℂ)
    (hO : observationAdj W g = 0) (j N m : ℕ)
include γ

theorem physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero {θ : ℝ} (hy : y θ = 0) :
    physicalDrivenGaugePartial γ E y j N θ = 0 := by
  apply Finset.sum_eq_zero
  simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow, hy]

include E N j m y in
/-- The finite physical antiholomorphic moment, with ordinary coordinate
measure and the actual centered physical coordinate. -/
def physicalDrivenMomentPartial : ℂ :=
  ∫ₚ θ, conj (deriv γ θ) *
    physicalDrivenGaugePartial γ E y j N θ * conj (physicalDrivenCentered γ θ) ^ m

include E N j m y in
/-- The actual uncancelled finite-sum tail, before a justified limit is taken. -/
def physicalDrivenTailMoment : ℂ :=
  ∫ₚ θ, deriv γ θ * physicalDrivenPower γ N θ *
    physicalDrivenScaledRow E y (N + j + 2) θ * conj (physicalDrivenCentered γ θ) ^ m

/-- A continuous weight can be integrated through the actual absolutely
convergent gauge series.  The dominating series is derived from genuine
Hilbert-space rows on the compact parameter interval. -/
theorem physicalDrivenGauge_weightedIntegral_hasSum (hγ : Continuous γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y angleInterval) (j : ℕ) (w : ℝ → ℂ)
    (hw : ContinuousOn w angleInterval) :
    HasSum (fun ℓ : ℕ => ∫ₚ θ,
      w θ * physicalDrivenGaugeTerm γ E y j ℓ θ)
      (∫ₚ θ, w θ * physicalDrivenGauge γ E y j θ) := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenGaugeTerm_majorant γ hγ E y hy j
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  
  have hC0  := (norm_nonneg _).trans (hC 0 (⟨le_rfl, Real.two_pi_pos.le⟩))
  have hsub : uIoc 0 anglePeriod ⊆ angleInterval := by
    rw [uIoc_of_le Real.two_pi_pos.le]
    exact Ioc_subset_Icc_self
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
     (bound := fun ℓ _ => C * u ℓ) ?_ ?_ ?_ intervalIntegrable_const ?_
  · intro ℓ
    exact ((hw.mul (physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j ℓ)).mono hsub).aestronglyMeasurable
      measurableSet_uIoc
  · intro ℓ
    exact Eventually.of_forall fun θ hθ => by
      rw [norm_mul]
      exact mul_le_mul (hC θ (hsub hθ)) (hbd ℓ θ (hsub hθ)) (norm_nonneg _) hC0
  · exact Eventually.of_forall fun _ _ => hu.mul_left C
  · exact Eventually.of_forall fun θ _ =>
      ((summable_norm_physicalDrivenGaugeTerm γ E y j θ).of_norm.hasSum).mul_left (w θ)

include E j m y in
/-- The infinite physical moment is the integral of the actual factorial
series, not a separately postulated Hardy function. -/
def physicalDrivenMoment : ℂ :=
  ∫ₚ θ, conj (deriv γ θ) *
    physicalDrivenGauge γ E y j θ * conj (physicalDrivenCentered γ θ) ^ m

include hy hγ in
theorem physicalDrivenMomentPartial_tendsto :
    Tendsto (fun N : ℕ => physicalDrivenMomentPartial γ E y j N m) atTop
      (𝓝 (physicalDrivenMoment γ E y j m)) := by
  let w  := fun θ => conj (deriv γ θ) * conj (physicalDrivenCentered γ θ) ^ m
  have hw : Continuous w :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
      ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow m)
  have hs := physicalDrivenGauge_weightedIntegral_hasSum γ hγ.continuous E y hy j w hw.continuousOn
  have hm : (∫ₚ θ, w θ * physicalDrivenGauge γ E y j θ) =
      physicalDrivenMoment γ E y j m := by
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hm] at hs
  have he (N : ℕ) : physicalDrivenMomentPartial γ E y j N m =
      ∑ ℓ ∈ Finset.range (N + 1), ∫ₚ θ,
        w θ * physicalDrivenGaugeTerm γ E y j ℓ θ := by
    calc
      _ = ∫ₚ θ, ∑ ℓ ∈ Finset.range (N + 1),
          w θ * physicalDrivenGaugeTerm γ E y j ℓ θ := by
        unfold physicalDrivenMomentPartial physicalDrivenGaugePartial
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ℓ _
        ring
      _ = _ := intervalIntegral.integral_finset_sum (fun ℓ _ =>
        ((hw.continuousOn.mul (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E y hy j ℓ)).mono
          (by rw [uIcc_of_le Real.two_pi_pos.le])).intervalIntegrable)
  simpa [Function.comp_def, he] using hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

include hy hγ in
/-- The true finite tail tends to zero.  Its integral terms themselves
form an absolutely convergent weighted gauge series, so no unproved
termwise derivative limit is needed. -/
theorem physicalDrivenTailMoment_tendsto_zero :
    Tendsto (fun N : ℕ => physicalDrivenTailMoment γ E y j N m) atTop (𝓝 0) := by
  let w  := fun θ => deriv γ θ * conj (physicalDrivenCentered γ θ) ^ m
  have hw : Continuous w := hγ.continuous_deriv_one.mul
    ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow m)
  
  have he (N : ℕ) : physicalDrivenTailMoment γ E y j N m =
      ∫ₚ θ, w θ * physicalDrivenGaugeTerm γ E y (j + 2) N θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [physicalDrivenTailMoment, physicalDrivenGaugeTerm, w]
    ring
  simpa [he] using (physicalDrivenGauge_weightedIntegral_hasSum γ hγ.continuous E y hy (j + 2) w
    hw.continuousOn).summable.tendsto_atTop_zero

include E W g j in
/-- The genuine periodic representative of the actual driven gauge on the
closed parameter interval.  Continuity follows from the proved zero endpoints. -/
def physicalDrivenPeriodicGauge (θ : ℝ) : ℂ :=
  AddCircle.liftIco anglePeriod 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) j)
      (θ : ParamCircle)

theorem physicalDrivenPeriodicGauge_periodic :
    Function.Periodic (physicalDrivenPeriodicGauge γ E W g j) anglePeriod := by
  simp [physicalDrivenPeriodicGauge]

include hO in
theorem physicalDrivenPeriodicGauge_eqOn :
    EqOn (physicalDrivenPeriodicGauge γ E W g j)
      (physicalDrivenGauge γ E (physicalDrivenVector W g) j) angleInterval := by
  intro θ hθ
  obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO j
  by_cases hθL : θ = anglePeriod
  · subst θ
    have hlift : AddCircle.liftIco anglePeriod 0
        (physicalDrivenGauge γ E (physicalDrivenVector W g) j) (0 : ParamCircle) =
          physicalDrivenGauge γ E (physicalDrivenVector W g) j 0 :=
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
    unfold physicalDrivenPeriodicGauge
    rw [AddCircle.coe_period, hlift, h0, hL]
  · exact AddCircle.liftIco_zero_coe_apply ⟨hθ.1, lt_of_le_of_ne hθ.2 hθL⟩

end

end PolyaNeumann

end
