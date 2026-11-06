module

public import RequestProject.PhysicalMomentHardyCriterion
public import RequestProject.CorrectedKernelSmooth
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Topology

local instance physicalDrivenTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The actual wave-number scalar in the transport coefficient. -/
def physicalDrivenQ (E : ℝ) : ℂ := -(Complex.I * (Real.sqrt E : ℂ)) / 2

theorem physicalDrivenQ_sq_ne_zero  (hE : 0 < E) : physicalDrivenQ E ^ 2 ≠ 0 :=
  pow_ne_zero _ (show physicalDrivenQ E ≠ 0 by
    unfold physicalDrivenQ
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hE).ne'))) (by norm_num))

/-- The actual driven vector with zero initial value, given by variation
of constants.  No terminal value is built into this definition. -/
def physicalDrivenVector (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (θ : ℝ) : Ell2 :=
  (-(Complex.I / (Real.sqrt 2 : ℂ))) •
    W θ (∫ s in 0..θ, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))

@[simp] theorem physicalDrivenVector_zero W g :
    physicalDrivenVector W g 0 = 0 := by
  simp [physicalDrivenVector]

/-- The terminal zero is a consequence of the actual adjoint observation
kernel, rather than an imposed periodic endpoint condition. -/
theorem physicalDrivenVector_endpoint W g
    (hO : observationAdj W g = 0) : physicalDrivenVector W g (2 * Real.pi) = 0 := by
  change (-(Complex.I / (Real.sqrt 2))) • W (2 * Real.pi) (observationAdj W g) = 0
  rw [hO, map_zero, smul_zero]

/-- The physical zeroth trace has its actual sqrt(2) normalization. -/
def physicalDrivenRow (y : ℝ → Ell2) (n : ℕ) (θ : ℝ) : ℂ :=
  if n = 0 then (Real.sqrt 2 : ℂ) * (y θ : ℕ → ℂ) 0 else (y θ : ℕ → ℂ) n

/-- Genuine scaled derivative data. -/
def physicalDrivenScaledRow (E : ℝ) (y : ℝ → Ell2) (n : ℕ) (θ : ℝ) : ℂ :=
  physicalDrivenQ E ^ n * physicalDrivenRow y n θ

/-- The exact recurrence used by the factorial cancellation. -/
theorem physicalDrivenScaledRow_hasDerivAt_succ
    γ E (g : ℝ → ℂ) y 
    (hy : HasDerivAt y (transportCoeff γ E θ (y θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * g θ) • basisVec 0) θ) (n : ℕ) :
    HasDerivAt (physicalDrivenScaledRow E y (n + 1))
      (deriv γ θ * physicalDrivenScaledRow E y (n + 2) θ +
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenScaledRow E y n θ) θ := by
  convert (show HasDerivAt (physicalDrivenRow y (n + 1)) (physicalDrivenQ E * (deriv γ θ * physicalDrivenRow y (n + 2) θ + conj (deriv γ θ) * physicalDrivenRow y n θ)) θ by
    have hd := ((innerSL ℂ (basisVec (n + 1))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      θ hy
    change HasDerivAt (fun s => inner ℂ (basisVec (n + 1)) (y s))
      (inner ℂ (basisVec (n + 1)) (transportCoeff γ E θ (y θ) +
        (-(Complex.I / (Real.sqrt 2)) * g θ) • basisVec 0)) θ at hd
    simp only [inner_basisVec] at hd
    rw [show physicalDrivenRow y (n + 1) = fun s => (y s) (n + 1) by
      funext s
      simp only [physicalDrivenRow, Nat.succ_ne_zero, if_false]]
    apply hd.congr_deriv
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      basisVec_coord, Nat.succ_ne_zero, if_false, mul_zero, add_zero]
    rw [transportCoeff_apply_coord, shiftN_apply_succ]
    cases n with
    | zero => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight]
    | succ n => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight, Nat.add_assoc]).const_mul
    (physicalDrivenQ E ^ (n + 1)) using 1
  · funext t; rfl
  simp [physicalDrivenScaledRow, pow_succ]
  ring

theorem norm_physicalDrivenScaledRow_le E y n θ :
    ‖physicalDrivenScaledRow E y n θ‖ ≤ ‖physicalDrivenQ E‖ ^ n * (2 * ‖y θ‖) := by
  rw [physicalDrivenScaledRow, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (by
    have hc k := lp.norm_apply_le_norm (p := 2) (by norm_num) (y θ) k
    unfold physicalDrivenRow
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]) (hc 0) (norm_nonneg _) (by norm_num)
    · exact (hc n).trans (by nlinarith [norm_nonneg (y θ)])) (by positivity)

/-- The actual centered physical coordinate, with no mean-zero assertion. -/
def physicalDrivenCentered (γ : ℝ → ℂ) (θ : ℝ) : ℂ := γ θ - γ 0

def physicalDrivenPower (γ : ℝ → ℂ) (ℓ : ℕ) (θ : ℝ) : ℂ :=
  (-physicalDrivenCentered γ θ) ^ ℓ / (ℓ.factorial : ℂ)

def physicalDrivenGaugeTerm (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2)
    (j ℓ : ℕ) (θ : ℝ) : ℂ :=
  physicalDrivenPower γ ℓ θ * physicalDrivenScaledRow E y (ℓ + j) θ

/-- The actual boundary factorial series. -/
def physicalDrivenGauge (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (j : ℕ) (θ : ℝ) : ℂ :=
  ∑' ℓ : ℕ, physicalDrivenGaugeTerm γ E y j ℓ θ

/-- Finite sums contain indices 0,...,N, making the uncancelled tail explicit. -/
def physicalDrivenGaugePartial (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2)
    (j N : ℕ) (θ : ℝ) : ℂ :=
  ∑ ℓ ∈ Finset.range (N + 1), physicalDrivenGaugeTerm γ E y j ℓ θ

theorem physicalDrivenPower_hasDerivAt_succ
     (hγ : ContDiff ℝ 1 γ) (ℓ : ℕ) θ :
    HasDerivAt (physicalDrivenPower γ (ℓ + 1))
      (-deriv γ θ * physicalDrivenPower γ ℓ θ) θ := by
  convert ((((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).neg.pow (ℓ + 1)).div_const ((ℓ + 1).factorial)) using 1
  · funext t; rfl
  simp [physicalDrivenPower, physicalDrivenCentered]
  rw [Nat.factorial_succ]
  push_cast
  field_simp [(by exact_mod_cast (by omega : ℓ + 1 ≠ 0)), (by exact_mod_cast (Nat.factorial_ne_zero ℓ))]

theorem norm_physicalDrivenGaugeTerm_le
    γ E y (j ℓ : ℕ) θ :
    ‖physicalDrivenGaugeTerm γ E y j ℓ θ‖ ≤
      2 * ‖y θ‖ * ‖physicalDrivenQ E‖ ^ j *
        ((‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenQ E‖) ^ ℓ / (ℓ.factorial : ℝ)) := by
  unfold physicalDrivenGaugeTerm
  rw [norm_mul]
  calc
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (norm_physicalDrivenScaledRow_le E y (ℓ + j) θ)
        (norm_nonneg _)
    _ = _ := by
      simp [physicalDrivenPower, pow_add, mul_pow]
      ring

/-- The factorial series is genuinely absolutely convergent at every point
for every actual Hilbert-space vector; no assumed row summability is used. -/
theorem summable_norm_physicalDrivenGaugeTerm
    γ E y j θ :
    Summable (fun ℓ : ℕ => ‖physicalDrivenGaugeTerm γ E y j ℓ θ‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_physicalDrivenGaugeTerm_le γ E y j · θ)
    ((Real.summable_pow_div_factorial
      (‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenQ E‖)).mul_left
        (2 * ‖y θ‖ * ‖physicalDrivenQ E‖ ^ j))

/-- On the compact parameter interval the genuine row bound gives one
summable majorant for the entire factorial gauge, independently of θ. -/
local notation "Φ0" => Icc 0

theorem exists_physicalDrivenGaugeTerm_majorant
    γ (hγ : Continuous γ) E y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) j :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ ℓ θ, θ ∈ Φ0 (2 * Real.pi) →
      ‖physicalDrivenGaugeTerm γ E y j ℓ θ‖ ≤ u ℓ := by
  have h0 : 0 ∈ Φ0 (2 * Real.pi) := ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.sub continuous_const).continuousOn
  have hM0 := (norm_nonneg _).trans (hM 0 h0)
  have hR0 := (norm_nonneg _).trans (hR 0 h0)
  refine ⟨fun ℓ => 2 * M * ‖physicalDrivenQ E‖ ^ j *
    ((R * ‖physicalDrivenQ E‖) ^ ℓ / (ℓ.factorial)),
    (Real.summable_pow_div_factorial _).mul_left _, ?_⟩
  intro ℓ θ hθ
  apply (norm_physicalDrivenGaugeTerm_le γ E y j ℓ θ).trans
  change 2 * ‖y θ‖ * ‖physicalDrivenQ E‖ ^ j *
      ((‖physicalDrivenCentered γ θ‖ * ‖physicalDrivenQ E‖) ^ ℓ / (ℓ.factorial)) ≤
    2 * M * ‖physicalDrivenQ E‖ ^ j *
      ((R * ‖physicalDrivenQ E‖) ^ ℓ / (ℓ.factorial))
  gcongr
  · exact hM θ hθ
  · exact hR θ hθ

theorem physicalDrivenRow_continuousOn y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) n :
    ContinuousOn (physicalDrivenRow y n) (Φ0 (2 * Real.pi)) := by
  have hc k : ContinuousOn (fun θ => (y θ) k)
      (Φ0 (2 * Real.pi)) := by
    have h := (innerSL ℂ (basisVec k)).continuous.comp_continuousOn hy
    change ContinuousOn (fun θ => inner ℂ (basisVec k) (y θ))
      (Φ0 (2 * Real.pi)) at h
    simpa [inner_basisVec] using h
  unfold physicalDrivenRow
  split_ifs
  · exact continuousOn_const.mul (hc 0)
  · exact hc n

theorem physicalDrivenGaugeTerm_continuousOn
    γ (hγ : Continuous γ) E y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) (j ℓ : ℕ) :
    ContinuousOn (physicalDrivenGaugeTerm γ E y j ℓ) (Φ0 (2 * Real.pi)) := by
  exact (show Continuous (physicalDrivenPower γ ℓ) by
    unfold physicalDrivenPower physicalDrivenCentered
    fun_prop).continuousOn.mul
    (continuousOn_const.mul (physicalDrivenRow_continuousOn y hy (ℓ + j)))

/-- The actual factorial gauge has a genuine continuous representative on
the entire closed parameter interval, including its endpoint values. -/
theorem physicalDrivenGauge_continuousOn
    γ (hγ : Continuous γ) E y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) j :
    ContinuousOn (physicalDrivenGauge γ E y j) (Φ0 (2 * Real.pi)) := by
  apply (show HasSumUniformlyOn (physicalDrivenGaugeTerm γ E y j) (physicalDrivenGauge γ E y j) (Φ0 (2 * Real.pi)) by
    obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenGaugeTerm_majorant γ hγ E y hy j
    exact HasSumUniformlyOn.of_norm_le_summable hu hbd).tendstoUniformlyOn.continuousOn
  exact (Eventually.of_forall fun s : Finset ℕ =>
    continuousOn_finset_sum s (fun ℓ _ =>
      physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j ℓ)).frequently

/-- The actual gauge vanishes whenever the actual driven vector does. -/
theorem physicalDrivenGauge_eq_zero_of_vector_eq_zero
    γ E y j  (hy : y θ = 0) :
    physicalDrivenGauge γ E y j θ = 0 := by
  unfold physicalDrivenGauge
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro ℓ
      simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow, hy]
    _ = 0 := tsum_zero

theorem physicalDrivenGauge_actual_endpoints
    γ E W g
    (hO : observationAdj W g = 0) j :
    physicalDrivenGauge γ E (physicalDrivenVector W g) j 0 = 0 ∧
      physicalDrivenGauge γ E (physicalDrivenVector W g) j (2 * Real.pi) = 0 :=
  ⟨physicalDrivenGauge_eq_zero_of_vector_eq_zero γ E _ j (physicalDrivenVector_zero W g),
    physicalDrivenGauge_eq_zero_of_vector_eq_zero γ E _ j (physicalDrivenVector_endpoint W g hO)⟩

theorem physicalDrivenGaugePartial_continuousOn
    γ (hγ : Continuous γ) E y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) j N :
    ContinuousOn (physicalDrivenGaugePartial γ E y j N) (Φ0 (2 * Real.pi)) :=
  continuousOn_finset_sum _ (fun ℓ _ =>
    physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j ℓ)

theorem physicalDrivenGaugePartial_eq_zero_of_vector_eq_zero
    γ E y j N  (hy : y θ = 0) :
    physicalDrivenGaugePartial γ E y j N θ = 0 := by
  apply Finset.sum_eq_zero
  intro ℓ _
  simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow, hy]

/-- The finite physical antiholomorphic moment, with ordinary coordinate
measure and the actual centered physical coordinate. -/
def physicalDrivenMomentPartial (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2)
    (j N m : ℕ) : ℂ :=
  ∫ θ in 0..(2 * Real.pi), conj (deriv γ θ) *
    physicalDrivenGaugePartial γ E y j N θ * conj (physicalDrivenCentered γ θ) ^ m

/-- The actual uncancelled finite-sum tail, before a justified limit is taken. -/
def physicalDrivenTailMoment (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2)
    (j N m : ℕ) : ℂ :=
  ∫ θ in 0..(2 * Real.pi), deriv γ θ * physicalDrivenPower γ N θ *
    physicalDrivenScaledRow E y (N + j + 2) θ * conj (physicalDrivenCentered γ θ) ^ m

/-- A continuous weight can be integrated through the actual absolutely
convergent gauge series.  The dominating series is derived from genuine
Hilbert-space rows on the compact parameter interval. -/
theorem physicalDrivenGauge_weightedIntegral_hasSum
    γ (hγ : Continuous γ) E y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) j w
    (hw : ContinuousOn w (Φ0 (2 * Real.pi))) :
    HasSum (fun ℓ : ℕ => ∫ θ in 0..(2 * Real.pi),
      w θ * physicalDrivenGaugeTerm γ E y j ℓ θ)
      (∫ θ in 0..(2 * Real.pi), w θ * physicalDrivenGauge γ E y j θ) := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenGaugeTerm_majorant γ hγ E y hy j
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hsub : uIoc 0 (2 * Real.pi) ⊆ Φ0 (2 * Real.pi) := by
    rw [uIoc_of_le Real.two_pi_pos.le]
    exact Ioc_subset_Icc_self
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (bound := fun ℓ _ => C * u ℓ) ?_ ?_ ?_ intervalIntegrable_const ?_
  · intro ℓ
    exact ((hw.mul (physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j ℓ)).mono hsub).aestronglyMeasurable
      measurableSet_uIoc
  · intro ℓ
    exact Eventually.of_forall fun θ hθ => by
      rw [norm_mul]
      exact mul_le_mul (hC θ (hsub hθ)) (hbd ℓ θ (hsub hθ)) (norm_nonneg _) ((norm_nonneg _).trans (hC 0 ⟨le_rfl, Real.two_pi_pos.le⟩))
  · exact Eventually.of_forall fun _ _ => hu.mul_left C
  · exact Eventually.of_forall fun θ _ =>
      ((summable_norm_physicalDrivenGaugeTerm γ E y j θ).of_norm.hasSum).mul_left (w θ)

/-- The infinite physical moment is the integral of the actual factorial
series, not a separately postulated Hardy function. -/
def physicalDrivenMoment (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (j m : ℕ) : ℂ :=
  ∫ θ in 0..(2 * Real.pi), conj (deriv γ θ) *
    physicalDrivenGauge γ E y j θ * conj (physicalDrivenCentered γ θ) ^ m

theorem physicalDrivenMomentPartial_tendsto
    γ (hγ : ContDiff ℝ 1 γ) E y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) j m :
    Tendsto (fun N => physicalDrivenMomentPartial γ E y j N m) atTop
      (𝓝 (physicalDrivenMoment γ E y j m)) := by
  let w : ℝ → ℂ := fun θ => conj (deriv γ θ) * conj (physicalDrivenCentered γ θ) ^ m
  have hw : Continuous w :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
      ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow m)
  have hs := physicalDrivenGauge_weightedIntegral_hasSum γ hγ.continuous E y hy j w hw.continuousOn
  rw [show (∫ θ in 0..(2 * Real.pi), w θ * physicalDrivenGauge γ E y j θ) = physicalDrivenMoment γ E y j m by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [w]
    ring] at hs
  have he N : physicalDrivenMomentPartial γ E y j N m =
      ∑ ℓ ∈ Finset.range (N + 1), ∫ θ in 0..(2 * Real.pi),
        w θ * physicalDrivenGaugeTerm γ E y j ℓ θ := by
    calc
      _ = ∫ θ in 0..(2 * Real.pi), ∑ ℓ ∈ Finset.range (N + 1),
          w θ * physicalDrivenGaugeTerm γ E y j ℓ θ := by
        unfold physicalDrivenMomentPartial physicalDrivenGaugePartial
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ℓ _
        dsimp only [w]
        ring
      _ = _ := intervalIntegral.integral_finset_sum (fun ℓ _ =>
        ((hw.continuousOn.mul (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E y hy j ℓ)).mono
          (by rw [uIcc_of_le Real.two_pi_pos.le])).intervalIntegrable)
  simpa [Function.comp_def, he] using hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- The true finite tail tends to zero.  Its integral terms themselves
form an absolutely convergent weighted gauge series, so no unproved
termwise derivative limit is needed. -/
theorem physicalDrivenTailMoment_tendsto_zero
    γ (hγ : ContDiff ℝ 1 γ) E y
    (hy : ContinuousOn y (Φ0 (2 * Real.pi))) j m :
    Tendsto (fun N => physicalDrivenTailMoment γ E y j N m) atTop (𝓝 0) := by
  let w : ℝ → ℂ := fun θ => deriv γ θ * conj (physicalDrivenCentered γ θ) ^ m
  have he N : physicalDrivenTailMoment γ E y j N m =
      ∫ θ in 0..(2 * Real.pi), w θ * physicalDrivenGaugeTerm γ E y (j + 2) N θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [physicalDrivenTailMoment, physicalDrivenGaugeTerm, w]
    rw [Nat.add_assoc]
    ring
  simpa [he] using (physicalDrivenGauge_weightedIntegral_hasSum γ hγ.continuous E y hy (j + 2) w (hγ.continuous_deriv_one.mul ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow m)).continuousOn).summable.tendsto_atTop_zero

/-- The genuine periodic representative of the actual driven gauge on the
closed parameter interval.  Continuity follows from the proved zero endpoints. -/
def physicalDrivenPeriodicGauge (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) (j : ℕ) (θ : ℝ) : ℂ :=
  AddCircle.liftIco (2 * Real.pi) 0
    (physicalDrivenGauge γ E (physicalDrivenVector W g) j)
      (θ : AddCircle (2 * Real.pi))

theorem physicalDrivenPeriodicGauge_periodic γ E
    W g j :
    Function.Periodic (physicalDrivenPeriodicGauge γ E W g j) (2 * Real.pi) := by
  intro θ
  unfold physicalDrivenPeriodicGauge
  rw [AddCircle.coe_add_period]

theorem physicalDrivenPeriodicGauge_eqOn γ E
    W g (hO : observationAdj W g = 0) j :
    EqOn (physicalDrivenPeriodicGauge γ E W g j)
      (physicalDrivenGauge γ E (physicalDrivenVector W g) j) (Φ0 (2 * Real.pi)) := by
  intro θ hθ
  obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO j
  by_cases hθL : θ = 2 * Real.pi
  · subst θ
    have hlift : AddCircle.liftIco (2 * Real.pi) 0
        (physicalDrivenGauge γ E (physicalDrivenVector W g) j) (0 : AddCircle (2 * Real.pi)) =
          physicalDrivenGauge γ E (physicalDrivenVector W g) j 0 :=
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
    unfold physicalDrivenPeriodicGauge
    rw [AddCircle.coe_period, hlift, h0, hL]
  · exact AddCircle.liftIco_zero_coe_apply ⟨hθ.1, lt_of_le_of_ne hθ.2 hθL⟩

end PolyaNeumann

end
