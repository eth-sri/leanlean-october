module

public import NearlyMinimax.AllocationBounds
public import NearlyMinimax.DegreeBounds


@[expose] public section

/-!
# Scalar factorial variance allocation for the actual quadratic profile

The coarse/fine bounds below derive their degree conditions from the profile
and degree floor. No factorial-series inequality is an input hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace NearlyMinimax

section
variable (C₀ C_D β S z : ℝ)

def profileVarianceArgument : ℝ := Real.exp z / (C_D * S)

def profileVarianceDegree : ℕ := Nat.floor (β * quadraticProfile S z)

def profileVarianceWeight : ℝ :=
  factorialSeries (profileVarianceDegree β S z) (profileVarianceArgument C_D S z) *
    max 1 (C₀ / profileVarianceArgument C_D S z)

end

section
variable {β C_D S z : ℝ} (hβ : 0 ≤ β) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D)
include hβ hDβ

include hD1 in
theorem profileVariance_coarse_ratio (hS : 2 ≤ S) (hz : z ≤ 0) :
    (profileVarianceDegree β S z) * profileVarianceArgument C_D S z ≤ 1 / 2 := by
  have hS₀ : 0 < S := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS  := mul_pos hD₀ hS₀
  have hQ : 0 ≤ quadraticProfile S z :=
    (by positivity : 0 ≤ S / 4).trans (quadraticProfile_lower hS₀)
  have hf := Nat.floor_le (mul_nonneg hβ hQ)
  have hfe := mul_le_mul_of_nonneg_right hf (Real.exp_pos z).le
  have hc := mul_le_mul_of_nonneg_left (quadraticProfile_coarse_bound hS hz) hβ
  unfold profileVarianceDegree profileVarianceArgument
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hCS).2
  nlinarith [mul_nonneg hβ hS₀.le]

theorem profileVariance_fine_degree_bounds (hS : 0 < S) (hz0 : 0 ≤ z) (hzS : z ≤ S) :
    (profileVarianceDegree β S z) ≤ C_D * S ∧
      (profileVarianceDegree β S z) * z ≤ β * S ^ 2 / 4 := by
  have hQ : 0 ≤ quadraticProfile S z :=
    (by positivity : 0 ≤ S / 4).trans (quadraticProfile_lower hS)
  have hf := Nat.floor_le (mul_nonneg hβ hQ)
  have hu := mul_le_mul_of_nonneg_left (quadraticProfile_fine_upper hS hz0 hzS) hβ
  have hv := mul_le_mul_of_nonneg_left (quadraticProfile_fine_bound hS hzS) hβ
  unfold profileVarianceDegree
  constructor
  · nlinarith [mul_nonneg hβ hS.le]
  · nlinarith

end

section
variable {C₀ C_D β S z : ℝ} (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D) (hβ : 0 ≤ β) (hS : 2 ≤ S)
include hC hD1 hDβ hS hβ

theorem profileVarianceWeight_coarse_bound (hz : z ≤ 0) :
    profileVarianceWeight C₀ C_D β S z ≤ 2 * C₀ := by
  have hS₀ : 0 < S := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS  := mul_pos hD₀ hS₀
  have hCS1 : 1 ≤ C_D * S := by nlinarith
  have hx : 0 < profileVarianceArgument C_D S z := div_pos (Real.exp_pos z) hCS
  have hxC : profileVarianceArgument C_D S z ≤ C₀ := by
    exact ((div_le_one hCS).2 ((Real.exp_le_one_iff.2 hz).trans hCS1)).trans hC
  have hs := factorialSeries_coarse_bound hx.le
    (profileVariance_coarse_ratio hβ hD1 hDβ hS hz)
  unfold profileVarianceWeight
  rw [max_eq_right ((le_div_iff₀ hx).2 (by simpa using hxC))]
  calc
    _ ≤ (2 * profileVarianceArgument C_D S z) * (C₀ / profileVarianceArgument C_D S z) :=
      by bound
    _ = _ := by field_simp

theorem profileVarianceWeight_fine_bound (hz0 : 0 ≤ z) (hzS : z ≤ S) :
    profileVarianceWeight C₀ C_D β S z ≤
      C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  have hC₀ : 0 < C₀ := by linarith
  have hS₀ : 0 < S := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS  := mul_pos hD₀ hS₀
  obtain ⟨hdeg, hprod⟩ := profileVariance_fine_degree_bounds hβ hDβ hS₀ hz0 hzS
  have he : (C_D * S) * profileVarianceArgument C_D S z = Real.exp z := by
    unfold profileVarianceArgument
    grind
  have hweight : max 1 (C₀ / profileVarianceArgument C_D S z) ≤ C₀ * C_D * S := by
    apply max_le
    · nlinarith
    · apply (div_le_iff₀ (div_pos (Real.exp_pos z) hCS)).2
      calc
        C₀ ≤ _ := by simpa using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.2 hz0) hC₀.le
        _ = (C₀ * C_D * S) * profileVarianceArgument C_D S z := by rw [← he]; ring
  exact factorialSeries_fine_weighted hz0 hC₀.le hCS hdeg hprod
    (by positivity) hweight

/-- Both coarse and fine levels obey the same explicit envelope. -/
theorem profileVarianceWeight_uniform_bound (hz : z ≤ S) :
    let expScale := Real.exp (β * S ^ 2 / 4)
    profileVarianceWeight C₀ C_D β S z ≤
      2 * C₀ * C_D ^ 2 * S ^ 2 * expScale := by
  intro expScale
  have hsq : 1 ≤ C_D ^ 2 * S ^ 2 := by bound
  have hexp : 1 ≤ expScale := Real.one_le_exp_iff.2 (by positivity)
  have hfactor : 1 ≤ C_D ^ 2 * S ^ 2 * expScale := by nlinarith
  rcases le_or_gt z 0 with hz0 | hz0
  · apply (profileVarianceWeight_coarse_bound hC hD1 hDβ hβ hS hz0).trans
    have hm := mul_le_mul_of_nonneg_left hfactor (by positivity)
    linarith
  · apply (profileVarianceWeight_fine_bound hC hD1 hDβ hβ hS hz0.le hz).trans
    bound

end

section
variable {δ a C C₀ C_D β x : ℝ} (j : ℕ) (hC : 0 < C₀) (hD : 0 < C_D) (hx : 0 < x)
    (hS : 0 < allocationWidth a C x)
include hC hD hx hS

/-- In the explicit candidate allocation, the normalized variance argument is exactly `C₀ K_j/n`. -/
theorem actual_profileVarianceArgument_eq_cell_fraction :
    profileVarianceArgument C_D (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x j) = C₀ * Real.exp (δ * j) / x := by
  unfold profileVarianceArgument allocationLevelPosition
  rw [Real.exp_add, Real.exp_sub, Real.exp_log hx,
    Real.exp_log (by positivity)]
  field_simp

end

/-- The paper's maximum weighted factorial variance, over all explicit candidate levels. -/
def actualVarianceMaximum (δ a C C₀ C_D γ β x : ℝ) : ℝ :=
  (Finset.range (terminalAllocationLevel δ a C (C₀ * C_D) γ x + 1)).sup'
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun j =>
      profileVarianceWeight C₀ C_D β (allocationWidth a C x)
        (allocationLevelPosition δ a C (C₀ * C_D) x j))

theorem actualVarianceMaximum_nonneg {δ a C C₀ C_D γ β x : ℝ}
    (hD : 0 < C_D) (hS : 0 < allocationWidth a C x) :
    0 ≤ actualVarianceMaximum δ a C C₀ C_D γ β x := by
  have hw : 0 ≤ profileVarianceWeight C₀ C_D β (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x 0) := by
    apply mul_nonneg
    · apply factorialSeries_nonneg
      unfold profileVarianceArgument
      positivity
    · positivity
  apply hw.trans
  exact Finset.le_sup' (fun j => profileVarianceWeight C₀ C_D β (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x j)) (Finset.mem_range.2 (Nat.succ_pos _))

/-- The actual maximum variance has the proved fine-level envelope eventually. -/
theorem eventually_actualVarianceMaximum_bound {δ a C₀ C_D γ β : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (C : ℝ) :
    ∀ᶠ x in atTop,
      actualVarianceMaximum δ a C C₀ C_D γ β x ≤
        2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 *
          Real.exp (β * (allocationWidth a C x) ^ 2 / 4) := by
  have hH : 0 < C₀ * C_D := by positivity
  filter_upwards [(allocationWidth_tendsto_atTop ha C).eventually (eventually_ge_atTop 2),
    eventually_actual_allocation_level_range hδ ha hH hγ C] with x hx hz
  apply Finset.sup'_le
  intro j hj
  grind [profileVarianceWeight_uniform_bound]

/-- The scalar spatial reserve multiplied by the actual maximum factorial variance. -/
def actualAllocationVarianceRatio (δ a C C₀ C_D γ β η varpi x : ℝ) : ℝ :=
  Real.exp (-2 * varpi * Real.log x + η *
    roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x)) *
      actualVarianceMaximum δ a C C₀ C_D γ β x

set_option maxHeartbeats 600000 in
/-- The actual scalar variance ratio has an explicit exponentially vanishing reserve. -/
theorem eventually_actualAllocationVarianceRatio_bound {δ a C₀ C_D γ β η varpi : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (C : ℝ) (hshift : C = 1 + 2 * (η + 2) / β) (hcoef : β * a ^ 2 / 4 = 2 * varpi) :
    ∀ᶠ x in atTop, 0 ≤ actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi x ∧
      actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi x ≤
        2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 * Real.exp (-2 * allocationWidth a C x) := by
  have hH : 0 < C₀ * C_D := by positivity
  have hD : 0 < C_D := by linarith
  have hw := allocationWidth_tendsto_atTop ha C
  filter_upwards [hw.eventually (eventually_ge_atTop 2),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 0),
    eventually_terminal_cell_log_nonneg ha hH C γ,
    eventually_actualVarianceMaximum_bound hδ ha hC hD1 hDβ hβ.le hγ C]
    with x hS hHS hL hLT hmax
  have hS₀ : 0 < allocationWidth a C x := by linarith
  have hn  :=
    actualVarianceMaximum_nonneg (δ := δ) (C₀ := C₀) (γ := γ) (β := β) hD hS₀
  have hdef : allocationWidth a C x =
      a * Real.sqrt (Real.log x) - (1 + 2 * (η + 2) / β) := by unfold allocationWidth; rw [hshift]
  have hbudget := quadratic_allocation_budget hβ (by linarith) hS₀.le hdef
  have hbase : β * (a * Real.sqrt (Real.log x)) ^ 2 / 4 = 2 * varpi * Real.log x := by
    grind
  rw [hbase] at hbudget
  have ht := (roundedTerminalDepth_bounds hδ hLT).2
  have hcand : candidateTerminalDepth a C (C₀ * C_D) γ x ≤ allocationWidth a C x := by
    unfold candidateTerminalDepth
    have hell  := Real.log_nonneg hHS
    have hlogS : 0 ≤ Real.log (allocationWidth a C x) := Real.log_nonneg (by linarith)
    linarith [mul_nonneg hγ hlogS]
  constructor
  · exact mul_nonneg (Real.exp_pos _).le hn
  · calc
      _ ≤ _ :=
        mul_le_mul ((by apply Real.exp_le_exp.2; nlinarith : Real.exp (-2 * varpi * Real.log x + η * roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x)) ≤ Real.exp (-β * allocationWidth a C x ^ 2 / 4 - 2 * allocationWidth a C x))) hmax hn (Real.exp_pos _).le
      _ = (2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2) *
          (Real.exp (-β * (allocationWidth a C x) ^ 2 / 4 - 2 * allocationWidth a C x) *
            Real.exp (β * (allocationWidth a C x) ^ 2 / 4)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        ring

/-- Consequently `W≤1` eventually follows for this actual scalar allocation, rather than being assumed. -/
theorem actualAllocationVarianceRatio_tends_zero {δ a C₀ C_D γ β η varpi : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (C : ℝ) (hshift : C = 1 + 2 * (η + 2) / β) (hcoef : β * a ^ 2 / 4 = 2 * varpi) :
    Tendsto (actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi) atTop (𝓝 0) := by
  have hb := eventually_actualAllocationVarianceRatio_bound hδ ha hC hD1 hDβ hβ hγ hη C hshift hcoef
  apply squeeze_zero' (hb.mono fun x hx => hx.1) (hb.mono fun x hx => hx.2)
  exact (tendsto_allocation_reserve_bound C₀ C_D).comp (allocationWidth_tendsto_atTop ha C)

end NearlyMinimax
