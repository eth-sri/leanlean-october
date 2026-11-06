module
public import Mathlib
public import NearlyMinimax.HolderTaylorBridge
public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.GridProjection
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
def partitionPairMass  [Fintype ι] (p : ι → ℝ) : ℝ :=
  Fintype.card ι  * ∑ i, p i ^ 2
def elementarySmoothness  (C : ModelConstants d) : ℝ := min C.smoothness 1
theorem elementarySmoothness_pos  (C : ModelConstants d) :
    0 < elementarySmoothness C := lt_min C.smoothness_pos (by norm_num)
theorem regular_grid_index_corner_le (k hk x) (hx : 0 ≤ x) :
    (regularGridIndex k hk x ) / k ≤ x := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have := Nat.floor_le (mul_nonneg hkr.le hx)
  have : ((min ⌊(k : ℝ) * x⌋₊ (k - 1) : ℕ) : ℝ) ≤ ⌊(k : ℝ) * x⌋₊ := by
    exact_mod_cast min_le_left ⌊k * x⌋₊ (k - 1)
  apply (div_le_iff₀ hkr).2
  change ((min ⌊k * x⌋₊ (k - 1) : ℕ) : ℝ) ≤ x * k
  nlinarith
theorem regular_grid_cell_corner_le  (k hk x) (hx : x ∈ unitCube d) (i ) :
    regularGridCorner k (regularGridCell k hk x) i ≤ x i :=
  regular_grid_index_corner_le k hk (x i) (hx i).1
theorem regular_grid_same_cell_radius  (k hk x y) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (hcell : regularGridCell k hk x = regularGridCell k hk y) (i ) :
    |x i - y i| ≤ 1 / k := by
  have hx' := regular_grid_cell_radius k hk x hx i
  have hy' := regular_grid_cell_radius k hk y hy i
  have hxlo := regular_grid_cell_corner_le k hk x hx i
  have := regular_grid_cell_corner_le k hk y hy i
  rw [hcell] at hx'
  rw [hcell] at hxlo
  exact abs_le.2 ⟨by linarith [(abs_le.mp hy').2], by linarith [(abs_le.mp hx').2]⟩
def regularGridProbability  (θ : RegressionParameter d) (k ) (hk : 0 < k)
    (c : Fin d → Fin k) : ℝ :=
  (designLaw θ).real ((regularGridCell k hk) ⁻¹' {c})
theorem regularGridProbability_nonneg {d : ℕ} (θ : RegressionParameter d)
    (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    0 ≤ regularGridProbability θ k hk c := measureReal_nonneg
theorem regularGridProbability_sum {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    ∑ c, regularGridProbability θ k hk c = 1 := by
  letI := designLaw_isProbability C θ hθ
  unfold regularGridProbability
  have he := sum_measureReal_preimage_singleton (μ := designLaw θ)
    (Finset.univ : Finset (Fin d → Fin k))
    (fun c hc => measurableSet_singleton c |>.preimage (regular_grid_cell_measurable k hk))
  simpa using he
theorem admissible_designLaw_le_cubeVolume  (C : ModelConstants d)
    (θ ) (hθ : Admissible C θ) :
    designLaw θ ≤ ENNReal.ofReal C.densityUpper • cubeVolume d := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hθ.2.2.1] with x hx
  exact ENNReal.ofReal_le_ofReal hx.2
theorem regular_grid_fiber_volume_le  (k hk c) :
    cubeVolume d ((regularGridCell k hk) ⁻¹' {c}) ≤ ENNReal.ofReal (1 / k) ^ d := by
  rw [cubeVolume, Measure.restrict_apply ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))]
  let a : Covariate d := fun i => regularGridCorner k c i
  let b : Covariate d := fun i => regularGridCorner k c i + 1 / k
  have hsub : (regularGridCell k hk) ⁻¹' {c} ∩ unitCube d ⊆ Icc a b := by
    intro x hx
    have hcell : regularGridCell k hk x = c := hx.1
    have hr (i : Fin d) : |x i - regularGridCorner k c i| ≤ 1 / k := by
      simpa only [hcell] using regular_grid_cell_radius k hk x hx.2 i
    constructor
    · intro i
      simpa only [hcell] using regular_grid_cell_corner_le k hk x hx.2 i
    · intro i
      have := (abs_le.mp (hr i)).2
      linarith
  apply (measure_mono hsub).trans_eq
  rw [Real.volume_Icc_pi]
  have hside (i : Fin d) : b i - a i = 1 / k := by dsimp [a, b]; ring
  simp_rw [hside]
  simp
theorem regularGridProbability_cap  (C : ModelConstants d)
    (θ ) (hθ : Admissible C θ) (k hk c) :
    regularGridProbability θ k hk c ≤ C.densityUpper / k ^ d := by
  have h_regularGridProbability_le : regularGridProbability θ k hk c ≤ C.densityUpper * (1 / k) ^ d := by
    letI := designLaw_isProbability C θ hθ
    have hdom := Measure.le_iff.1 (admissible_designLaw_le_cubeVolume C θ hθ)
      ((regularGridCell k hk) ⁻¹' {c})
      ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))
    rw [Measure.smul_apply, smul_eq_mul] at hdom
    have hcap : (designLaw θ) ((regularGridCell k hk) ⁻¹' {c}) ≤
        ENNReal.ofReal C.densityUpper * ENNReal.ofReal (1 / k) ^ d := by
      apply hdom.trans
      gcongr
      exact regular_grid_fiber_volume_le k hk c
    have hu : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
    apply (ENNReal.toReal_mono (by finiteness) hcap).trans_eq
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hu]
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / k)]
  convert h_regularGridProbability_le using 1 <;> rw [div_pow, one_pow] <;> ring
end NearlyMinimax
