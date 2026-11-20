module

public import NearlyMinimax.HolderTaylorBridge
public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.GridProjection
public import NearlyMinimax.PairMass


@[expose] public section

/-! Actual regular-grid geometry and design masses for the elementary
same-cell pair-difference estimator. Bounds use the original model density
cap and Hölder regularity, rather than assumed collision probabilities. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax

section
variable {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) {k : ℕ}
    (hk : 0 < k) {x y : Covariate d} (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (hcell : regularGridCell k hk x = regularGridCell k hk y) (i : Fin d)

def elementarySmoothness (C : ModelConstants d) : ℝ := min C.smoothness 1

theorem elementarySmoothness_pos (C : ModelConstants d) :
    0 < elementarySmoothness C := lt_min C.smoothness_pos (by norm_num)

include hθ hx hy in
/-- All admissible regressions have the spatial modulus needed by a first
order pair difference, including smoothness above one. -/
theorem admissible_regression_spatial_modulus :
    |θ.regression x - θ.regression y| ≤
      (2 * (d + 1) * C.holderBound) *
        euclideanNorm (x - y) ^ elementarySmoothness C := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  have hm := RoughRegime.Model.holderBall_spatial_modulus
    (mul_nonneg (by norm_num) C.holderBound_pos.le)
    (euclideanExtension_mem_holderBall hreg hNorm)
    (x := (euclideanPoint x)) (y := (euclideanPoint y)) hx hy
  have hdiff : euclideanPoint x - euclideanPoint y = euclideanPoint (x - y) :=
    ((euclideanCoordinates d).symm.map_sub x y).symm
  rw [hdiff, euclideanPoint_norm] at hm
  simp only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point,
    hcube x hx, hcube y hy] at hm
  unfold elementarySmoothness
  bound

theorem regular_grid_index_corner_le {x : ℝ} (hx : 0 ≤ x) :
    (regularGridIndex k hk x) / k ≤ x := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfloor := Nat.floor_le (mul_nonneg hkr.le hx)
  have hmin : ((min ⌊k * x⌋₊ (k - 1) : ℕ) : ℝ) ≤ ⌊k * x⌋₊ := by
    bound
  apply (div_le_iff₀ hkr).2
  change min _ (k - 1) ≤ x * k
  nlinarith

include hx in
theorem regular_grid_cell_corner_le :
    regularGridCorner (regularGridCell k hk x) i ≤ x i :=
  regular_grid_index_corner_le hk (hx i).1

include hx hy hcell in
theorem regular_grid_same_cell_radius :
    |x i - y i| ≤ 1 / k := by
  grind [regular_grid_cell_radius hk hx i, regular_grid_cell_radius hk hy i, regular_grid_cell_corner_le hk hx i, regular_grid_cell_corner_le hk hy i]

include hθ hx hy hcell in
theorem regular_grid_same_cell_regression_difference :
    |θ.regression x - θ.regression y| ≤
      (2 * (d + 1) * C.holderBound) *
        (Real.sqrt d * (1 / k)) ^ elementarySmoothness C := by
  apply (admissible_regression_spatial_modulus hθ hx hy).trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by unfold euclideanNorm; positivity) (euclideanNorm_le_coordinate_radius (by positivity) (regular_grid_same_cell_radius hk hx hy hcell))
      (elementarySmoothness_pos C).le)
  exact mul_nonneg (by positivity) C.holderBound_pos.le

/-- The probability of each explicit regular-grid label under the actual
admissible design law. -/
def regularGridProbability (θ : RegressionParameter d) {k : ℕ} (hk : 0 < k)
    (c : Fin d → Fin k) : ℝ :=
  (designLaw θ).real ((regularGridCell k hk) ⁻¹' {c})

theorem regularGridProbability_nonneg (θ : RegressionParameter d)
    {k : ℕ} (hk : 0 < k) (c : Fin d → Fin k) :
    0 ≤ regularGridProbability θ hk c := measureReal_nonneg

include hθ in
theorem regularGridProbability_sum :
    ∑ c, regularGridProbability θ hk c = 1 := by
  letI := designLaw_isProbability C θ hθ
  unfold regularGridProbability
  have he := sum_measureReal_preimage_singleton (μ := designLaw θ)
    Finset.univ
    (fun c hc => measurableSet_singleton c |>.preimage (regular_grid_cell_measurable k hk))
  simpa using he

end

variable {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) {k : ℕ}
    (hk : 0 < k) (c : Fin d → Fin k)

include hθ in
/-- The original density cap gives domination by scaled cube volume. -/
theorem admissible_designLaw_le_cubeVolume :
    designLaw θ ≤ ENNReal.ofReal C.densityUpper • cubeVolume d := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hθ.2.2.1] with x hx
  exact ENNReal.ofReal_le_ofReal hx.2

/-- Each cell fiber, restricted to the cube, lies in a closed coordinate
box of side `1/k`. The right-boundary convention preserves this bound. -/
theorem regular_grid_fiber_volume_le :
    cubeVolume d ((regularGridCell k hk) ⁻¹' {c}) ≤ ENNReal.ofReal (1 / k) ^ d := by
  rw [cubeVolume, Measure.restrict_apply ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))]
  let a  := fun i => regularGridCorner c i
  let b  := fun i => regularGridCorner c i + 1 / k
  have hsub : (regularGridCell k hk) ⁻¹' {c} ∩ unitCube d ⊆ Icc a b := by
    intro x hx
    have hcell : regularGridCell k hk x = c := hx.1
    have hr i : |x i - regularGridCorner c i| ≤ 1 / k := by
      simpa only [hcell] using regular_grid_cell_radius hk hx.2 i
    constructor
    · intro i
      simpa only [hcell] using regular_grid_cell_corner_le hk hx.2 i
    · intro i
      grind
  apply (measure_mono hsub).trans_eq
  rw [Real.volume_Icc_pi]
  have hside i : b i - a i = 1 / k := by ring
  simp_rw [hside]
  simp

include hθ in
/-- A genuine uniform upper bound for every grid cell probability. -/
theorem regularGridProbability_le :
    regularGridProbability θ hk c ≤ C.densityUpper * (1 / k) ^ d := by
  letI := designLaw_isProbability C θ hθ
  have hdom := Measure.le_iff.1 (admissible_designLaw_le_cubeVolume hθ)
    ((regularGridCell k hk) ⁻¹' {c})
    ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))
  rw [Measure.smul_apply, smul_eq_mul] at hdom
  have hcap : (designLaw θ) ((regularGridCell k hk) ⁻¹' {c}) ≤
      ENNReal.ofReal C.densityUpper * ENNReal.ofReal (1 / k) ^ d := by
    apply hdom.trans
    gcongr
    exact regular_grid_fiber_volume_le hk c
  have hu : 0 ≤ C.densityUpper := (by linarith [C.one_lt_densityUpper])
  apply (ENNReal.toReal_mono (by finiteness) hcap).trans_eq
  simp_all

include hθ in
theorem regularGridProbability_cap :
    regularGridProbability θ hk c ≤ C.densityUpper / k ^ d := by
  convert regularGridProbability_le hθ hk c using 1 <;> rw [div_pow] <;> ring

end NearlyMinimax
