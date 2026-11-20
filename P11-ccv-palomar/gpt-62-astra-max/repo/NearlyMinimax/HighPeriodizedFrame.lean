module

public import NearlyMinimax.HighFramePolynomial


@[expose] public section

/-! Actual periodization and smooth local charts for polynomial frame fields. -/
noncomputable section
open Set Function Filter
open scoped Topology BigOperators ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem integerLatticeTranslate_locallyFinite {d : ℕ} (G : Covariate d → ℝ)
    (hG : ∀ u, G u ≠ 0 → ∀ r, |u r| < 1) :
    LocallyFinite (fun z : Fin d → ℤ => support (fun x : Covariate d =>
      G (fun r => x r - z r))) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  let S  := fun r => Finset.Icc (⌊x r⌋ - 3) (⌊x r⌋ + 3)
  apply (Fintype.piFinset S).finite_toSet.subset
  intro z hz
  obtain ⟨y, hy, hnear⟩ := hz
  apply Fintype.mem_piFinset.mpr
  intro r
  have hclose := abs_lt.mp (hG _ hy r)
  have hcoord  := by
    exact (show |y r - x r| ≤ ‖y - x‖ from by
      exact norm_le_pi_norm (y - x) r).trans_lt (by assumption)
  have hcoord' := abs_lt.mp hcoord
  have hfloor := Int.floor_le (x r)
  have hceil := Int.lt_floor_add_one (x r)
  apply Finset.mem_Icc.mpr
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith

section
variable {d k : ℕ} (j : HighWindowLabels d k) {G : Covariate d → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0)

def highPeriodizedChart
    (G : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  ∑ᶠ z : Fin d → ℤ, if (∀ r, (z r) = j r) then
    G (fun r => k * x r - z r) else 0

include hG0 in
theorem highPeriodizedChart_locallyFinite :
    LocallyFinite (fun z : Fin d → ℤ => support (fun x : Covariate d =>
      if (∀ r, (z r) = j r) then G (fun r => k * x r - z r) else 0)) := by
  have hlf := integerLatticeTranslate_locallyFinite G (fun u hu r => (highWindowTensor_support_bound (fun h => hu (hG0 u h)) r).trans (by norm_num))
  have hc : Continuous (fun x : Covariate d => fun r => k * x r) := by fun_prop
  apply (hlf.preimage_continuous hc).subset
  simp

include hG hG0 in
theorem highPeriodizedChart_contDiff :
    ContDiff ℝ ∞ (highPeriodizedChart j G) := by
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodizedChart_locallyFinite j hG0)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : ∀ r, (z r) = j r
  · simp [ite_eq_left hz]
    fun_prop
  · simp [ite_eq_right hz]
    exact contDiff_const

theorem highPeriodicWindow_term_le {j : ZMod k} (x : ℝ)
    {z : ℤ} (hz : z = j) :
    highWindowProfile (k * x - z) ≤ highPeriodicWindow j x := by
  have hh := single_le_finsum z (highPeriodicWindow_locallyFinite j |>.point_finite x)
    (fun q => show 0 ≤ (if q = j then
      highWindowProfile (k * x - q) else 0) from by
      split_ifs
      · exact highWindowProfile_nonneg _
      · exact le_rfl)
  simpa only [ite_eq_left hz, highPeriodicWindow] using hh

end

section
variable {d k : ℕ} [NeZero k] (hk : 4 ≤ k) (j : HighWindowLabels d k) {G : Covariate d → ℝ}
    (hG : ContDiff ℝ ∞ G) (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0)
include hk hG0

/-- Any chart supported by the compact profile has one smooth chart formula
in a neighborhood, including points where that formula is zero. -/
theorem highPeriodizedChart_eventuallyEq_single (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ r, (z r) = j r) ∧
      highPeriodizedChart j G =ᶠ[𝓝 x]
        (fun y => G (fun r => k * y r - z r)) := by
  choose z hz he using fun r => highPeriodicWindow_eventuallyEq_single hk (j r) (x r)
  refine ⟨z, hz, ?_⟩
  have hcoord r  :=
    (continuous_apply r).continuousAt.eventually (he r)
  filter_upwards [Filter.eventually_all.mpr hcoord] with y hy
  rw [highPeriodizedChart, finsum_eq_single _ z]
  · simp [ite_eq_left hz]
  · intro q hq
    by_cases hqj : ∀ r, (q r) = j r
    · simp [ite_eq_left hqj]
      by_contra hnonzero
      have hqeq : q = z := by
        funext r
        have hqr : highWindowProfile (k * y r - q r) ≠ 0 := fun hh => (fun h => hnonzero (hG0 _ h)) (Finset.prod_eq_zero (Finset.mem_univ r) hh)
        have hzpositive : 0 < highWindowProfile (k * y r - z r) := by
          have hh := highPeriodicWindow_term_le (y r) (hqj r)
          rw [hy r] at hh
          exact (lt_of_le_of_ne (highWindowProfile_nonneg _) (Ne.symm hqr)).trans_le hh
        exact highPeriodicWindow_support_subsingleton (by omega) (j r) (y r) (by
          simp_all) (by
          simpa only [mem_support, ite_eq_left (hz r)] using hzpositive.ne')
      exact hq hqeq
    · simp [ite_eq_right hqj]

include hG in
theorem highPeriodizedChart_derivative_bound
    {q : ℕ} {B : ℝ} (hB : ∀ u, ‖iteratedFDeriv ℝ q G u‖ ≤ B) (x : Covariate d) :
    ‖iteratedFDeriv ℝ q (highPeriodizedChart j G) x‖ ≤ B * k ^ q := by
  obtain ⟨z, hz, he⟩ := highPeriodizedChart_eventuallyEq_single hk j hG0 x
  rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
  have hh := smooth_affine_iteratedFDeriv_bound hG k
    (fun r => (z r)) x hB
  rwa [abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)] at hh

end

theorem highPeriodizedChart_tsupport_profile {d : ℕ} {G : Covariate d → ℝ}
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    tsupport G ⊆ tsupport (highWindowTensor d) := by
  apply closure_mono
  intro u hu
  exact fun h => hu (hG0 u h)

section
variable {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
include hk

theorem highPeriodizedChart_derivative_support_lift
    {j : HighWindowLabels d k} {G : Covariate d → ℝ}
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) {q : ℕ} {x : Covariate d}
    (hx : iteratedFDeriv ℝ q (highPeriodizedChart j G) x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ r, (z r) = j r) ∧
      ∀ r, |k * x r - z r| ≤ 3 / 4 := by
  obtain ⟨z, hz, he⟩ := highPeriodizedChart_eventuallyEq_single hk j hG0 x
  let A : Covariate d → ℝ := fun y => G (fun r => k * y r - z r)
  have hn : iteratedFDeriv ℝ q A x ≠ 0 := by
    rwa [← (he.iteratedFDeriv ℝ q).eq_of_nhds]
  have hs  := (support_iteratedFDeriv_subset q) (show x ∈ support (iteratedFDeriv ℝ q A) from hn)
  have ht  :=
    (tsupport_comp_subset_preimage G (by
      fun_prop)) hs
  exact ⟨z, hz, highWindowTensor_tsupport_bound
    (highPeriodizedChart_tsupport_profile hG0 ht)⟩

theorem highPeriodizedChart_derivative_active_subset
    {G : HighWindowLabels d k → Covariate d → ℝ}
    (hG0 : ∀ j u, highWindowTensor d u = 0 → G j u = 0) (q : ℕ) (x : Covariate d) :
    Finset.univ.filter (fun j => iteratedFDeriv ℝ q (highPeriodizedChart j (G j)) x ≠ 0) ⊆
      highActiveLabelBox d k x := by
  intro j hj
  obtain ⟨z, hz, hclose⟩ := highPeriodizedChart_derivative_support_lift hk
    (hG0 j) (Finset.mem_filter.mp hj).2
  apply Fintype.mem_piFinset.mpr
  intro r
  have he := integer_close_three_quarters (hclose r)
  rcases he with he | he
  · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, true_or]
  · simp only [← hz r, he, Finset.mem_insert, Finset.mem_singleton, or_true]

end

variable {d : ℕ}

def highFrameField (k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) (x : Covariate d) : ℝ :=
  η * ∑ j, highPeriodizedChart j (highFrameProfile (P j)) x

theorem highFrameProfile_zero_of_window_zero (P : MvPolynomial (Fin d) ℝ)
    (u : Covariate d) (hu : highWindowTensor d u = 0) : highFrameProfile P u = 0 := by
  simp [highFrameProfile, hu]

theorem highFrameField_contDiff (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ ∞ (highFrameField k η P) := by
  change ContDiff ℝ ∞ (fun x => η • ∑ j, highPeriodizedChart j (highFrameProfile (P j)) x)
  apply ContDiff.const_smul
  apply ContDiff.sum
  solve_by_elim [highPeriodizedChart_contDiff, highFrameProfile_contDiff, highFrameProfile_zero_of_window_zero]

/-- The coefficient ball is independent of the polynomial degree.  Its
normalization makes every derivative through the fixed order at most one
before the spatial rescaling. -/
theorem highFrameField_derivative_bound (d m : ℕ) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k, ∀ (_ : NeZero k), 4 ≤ k → ∀ η,
      ∀ P,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) → ∀ q ≤ m, ∀ x : Covariate d,
      ‖iteratedFDeriv ℝ q (highFrameField k η P) x‖ ≤
        |η| * 2 ^ d * k ^ q := by
  obtain ⟨B, hB0, hB⟩ := highFrameProfile_derivative_bound d m
  let Cfr := max B 1
  have hCfr0 : 0 < Cfr := by positivity
  refine ⟨Cfr, (le_max_right _ _), ?_⟩
  intro k hk0 hk η P hP q hq x
  letI := hk0
  have hprofile j u :
      ‖iteratedFDeriv ℝ q (highFrameProfile (P j)) u‖ ≤ 1 := by
    calc
      _ ≤ _ := hB _ q hq u
      _ ≤ _ := mul_le_mul (le_max_left _ _) (hP j)
        (frameCoefficientL1_nonneg _) hCfr0.le
      _ = 1 := mul_inv_cancel₀ hCfr0.ne'
  have hchart j :
      ‖iteratedFDeriv ℝ q (highPeriodizedChart j (highFrameProfile (P j))) x‖ ≤
        k ^ q := by
    simpa using highPeriodizedChart_derivative_bound hk j
      (highFrameProfile_contDiff (P j)) (highFrameProfile_zero_of_window_zero (P j)) (hprofile j) x
  have hsmooth j :
      ContDiffAt ℝ q (highPeriodizedChart j (highFrameProfile (P j))) x :=
    ((highPeriodizedChart_contDiff j (highFrameProfile_contDiff (P j))
      (highFrameProfile_zero_of_window_zero (P j))).of_le (by simp)).contDiffAt
  have he : iteratedFDeriv ℝ q (highFrameField k η P) x =
      η • ∑ j, iteratedFDeriv ℝ q (highPeriodizedChart j (highFrameProfile (P j))) x := by
    change iteratedFDeriv ℝ q
      (fun y => η • ∑ j, highPeriodizedChart j (highFrameProfile (P j)) y) x = _
    rw [iteratedFDeriv_const_smul_apply' (by
      apply ContDiffAt.sum
      tauto), iteratedFDeriv_fun_sum_apply (fun j _ => hsmooth j)]
  rw [he, norm_smul]
  have hh := finite_sum_norm_le_active_count (by positivity) hchart
    ((Finset.card_le_card (highPeriodizedChart_derivative_active_subset hk (fun j => highFrameProfile_zero_of_window_zero (P j)) q x)).trans (highActiveLabelBox_card_le d k x))
  have hh' := mul_le_mul_of_nonneg_left hh (abs_nonneg η)
  push_cast at hh'
  convert hh' using 1 <;> ring

/-- Original mixed partials, Euclidean Hölder modulus, and the full original
norm of the actual frame field, uniformly in degree and resolution. -/
theorem highFrameField_model_bounds (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf, 0 ≤ cf → ∀ P,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField k (cf * k ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ 2 ^ d * (cf * k ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ 2 ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * (2 ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U, holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal ((((C.order + 1 : ℕ) ^ d + 2) * 2 ^ d) * cf)) := by
  obtain ⟨Cfr, hCfr1, hCfr⟩ := highFrameField_derivative_bound d (C.order + 1)
  refine ⟨Cfr, hCfr1, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  let F := highFrameField k (cf * k ^ (-C.smoothness)) P
  have hkR : (1 : ℝ) ≤ k := by bound
  have hkpos : (0 : ℝ) < k := by positivity
  have hA : 0 ≤ 2 ^ d * cf := by positivity
  have hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ (2 ^ d * cf) *
        k ^ (q - C.smoothness) := by
    intro q hq x
    have hh := hCfr k hk0 hk (cf * k ^ (-C.smoothness)) P hP q hq x
    rw [abs_of_nonneg (by positivity)] at hh
    have hp : k ^ (-C.smoothness) * k ^ q =
        (k : ℝ) ^ (q - C.smoothness) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hkpos]
      ring
    convert hh using 1
    rw [← hp]
    ring
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives
    (highFrameField_contDiff ..) hkR hA hbound
  have hvalue x :
      |F x| ≤ 2 ^ d * (cf * k ^ (-C.smoothness)) := by
    have hh := hCfr k hk0 hk (cf * k ^ (-C.smoothness)) P hP 0 (by omega) x
    have hη : 0 ≤ cf * k ^ (-C.smoothness) := by positivity
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg hη, pow_zero] at hh
    bound
  refine ⟨hvalue, hs, hm, ?_⟩
  intro U
  convert (holderNorm_of_scaled_derivatives U (highFrameField_contDiff ..) hkR hA hbound) using 1
  ring

end NearlyMinimax
