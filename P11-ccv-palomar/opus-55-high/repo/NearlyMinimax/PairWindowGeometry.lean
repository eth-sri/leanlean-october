module

public import NearlyMinimax.HolderTaylorBridge
public import NearlyMinimax.ConditionalLaw
public import NearlyMinimax.GridProjection
public import NearlyMinimax.PairMass
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual regular-grid geometry and design masses for the elementary
same-cell pair-difference estimator. Bounds use the original model density
cap and Hölder regularity, rather than assumed collision probabilities. -/

𝚫
𝚳
𝚨

def elementarySmoothness (C : ModelConstants d) : ℝ := min C.smoothness 1

theorem elementarySmoothness_pos (C : ModelConstants d) :
    0 < elementarySmoothness C := lt_min C.smoothness_pos 𝖠₄

𝗇 𝔉 2 * 𝗞₁ * C.holderBound
𝗇 𝔎 𝙟
𝗇 𝔏 𝘌
𝗇 𝔐 𝗌
𝗇 𝔒 y ∈ unitCube d
/-- All admissible regressions have the spatial modulus needed by a first
order pair difference, including smoothness above one. -/
theorem admissible_regression_spatial_modulus C
    θ (hθ : 𝔎)
    x y (hx : 𝔐) (hy : 𝔒) :
    |θ.regression x - θ.regression y| ≤
      𝔉 *
        euclideanNorm 𝔏 ^ elementarySmoothness C := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
  have hm := RoughRegime.Model.holderBall_spatial_modulus (euclideanExtension F)
    C.smoothness (2 * C.holderBound)
    (mul_nonneg  𝖠₄  C.holderBound_pos.le)
    (euclideanExtension_mem_holderBall C F hreg hNorm)
    (euclideanPoint x) (euclideanPoint y) hx hy
  have hdiff : euclideanPoint x - euclideanPoint y = euclideanPoint 𝔏 :=
    ((euclideanCoordinates d).symm.map_sub x y).symm
  rw [hdiff, euclideanPoint_norm] at hm
  simp only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point,
    hcube x hx, hcube y hy] at hm
  unfold elementarySmoothness
  linarith

𝗇 𝔇 (min ⌊𝘘₁⌋₊ 𝗩₂ : ℕ)
𝗃 𝔑 ἀ k hk
𝗃 𝔖 𝔑 ἀ x
theorem regular_grid_index_corner_le k hk x (hx : 0 ≤ x) :
    𝔖 regularGridIndex / k ≤ x := by
  have hkr : 0 < 𝙦 := by exact_mod_cast hk
  have hfloor := Nat.floor_le $ mul_nonneg hkr.le hx
  have hmin : (𝔇 : ℝ) ≤ ⌊𝘘₁⌋₊ := by
    simp
  apply (div_le_iff₀ hkr).2
  change 𝔇 ≤ x * k
  nlinarith

𝗇 𝔍 𝔖 regularGridCell
theorem regular_grid_cell_corner_le k hk
    x (hx : 𝔐) i :
    regularGridCorner k 𝔍 i ≤ x i :=
  𝔑 regular_grid_index_corner_le (x i) (hx i).1

𝗇 𝔅 𝚖₂
theorem regular_grid_same_cell_radius k hk
    x y (hx : 𝔐) (hy : 𝔒)
    (hcell : 𝔍 = 𝔑 regularGridCell y) i :
    |x i - y i| ≤ 𝔅 := by
  have hx' := 𝔖 regular_grid_cell_radius hx i
  have hy' := 𝔑 regular_grid_cell_radius y hy i
  have hxlo := 𝔖 regular_grid_cell_corner_le hx i
  have hylo := 𝔑 regular_grid_cell_corner_le y hy i
  grind

𝗃 𝔔 ἀ C θ hθ
theorem regular_grid_same_cell_regression_difference
    C θ (hθ : 𝔎)
    k hk x y
    (hx : 𝔐) (hy : 𝔒)
    (hcell : 𝔍 = 𝔑 regularGridCell y) :
    |θ.regression x - θ.regression y| ≤
      𝔉 *
        (Real.sqrt d * 𝔅) ^ elementarySmoothness C := by
  have hr := euclideanNorm_le_coordinate_radius 𝔏 𝔅
     𝖠₃  $ 𝔖 regular_grid_same_cell_radius y hx hy hcell
  apply (𝔔 admissible_regression_spatial_modulus x y hx hy).trans
  apply mul_le_mul_of_nonneg_left
    $ Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hr
      (elementarySmoothness_pos C).le
  exact mul_nonneg (mul_nonneg  𝖠₄  𝖠₃ ) C.holderBound_pos.le

𝗇 𝔄 𝔑 regularGridCell ⁻¹' 𝚕₂
/-- The probability of each explicit regular-grid label under the actual
admissible design law. -/
def regularGridProbability (θ : RegressionParameter d) (k : ℕ) (hk : 𝖰)
    (c : 𝙯₂) : ℝ :=
  𝘐₂ 𝔄

𝗇 𝔊 regularGridProbability θ k hk c
theorem regularGridProbability_nonneg (θ : RegressionParameter d)
    k hk c :
    0 ≤ 𝔊 := measureReal_nonneg

theorem regularGridProbability_sum C
    (θ : RegressionParameter d) (hθ : 𝔎) k hk :
    ∑ c, 𝔊 = 1 := by
  letI := 𝔔 designLaw_isProbability
  unfold regularGridProbability
  have he := sum_measureReal_preimage_singleton (μ := designLaw θ)
    Finset.univ
     fun c hc => measurableSet_singleton c |>.preimage 𝔑 regular_grid_cell_measurable
  simpa using he

/-- The original density cap gives domination by scaled cube volume. -/
theorem admissible_designLaw_le_cubeVolume C
    θ (hθ : 𝔎) :
    designLaw θ ≤ ENNReal.ofReal C.densityUpper • cubeVolume d := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hθ.2.2.1] with x hx
  exact ENNReal.ofReal_le_ofReal hx.2

𝗇 𝔈 (measurableSet_singleton c).preimage 𝔑 regular_grid_cell_measurable
𝗇 𝔓 regularGridCorner k c
/-- Each cell fiber, restricted to the cube, lies in a closed coordinate
box of side `1/k`. The right-boundary convention preserves this bound. -/
theorem regular_grid_fiber_volume_le k hk
    c :
    cubeVolume d 𝔄 ≤ ENNReal.ofReal 𝔅 ^ d := by
  rw [cubeVolume, Measure.restrict_apply 𝔈]
  let a := 𝔓
  let b := fun i => 𝔓 i + 𝔅
  have hsub : 𝔄 ∩ unitCube d ⊆ 𝘔₂ := by
    intro x hx
    have hcell : 𝔍 = c := hx.1
    have hr i : |x i - 𝔓 i| ≤ 𝔅 := by
      simpa only [hcell] using 𝔖 regular_grid_cell_radius hx.2 i
    constructor
    · intro i
      simpa only [hcell] using 𝔖 regular_grid_cell_corner_le hx.2 i
    · intro i
      grind
  apply (measure_mono hsub).trans_eq
  rw [Real.volume_Icc_pi]
  aesop

/-- A genuine uniform upper bound for every grid cell probability. -/
theorem regularGridProbability_le C
    (θ : RegressionParameter d) (hθ : 𝔎) k hk
    c :
    𝔊 ≤ C.densityUpper * 𝔅 ^ d := by
  letI := 𝔔 designLaw_isProbability
  have hdom := Measure.le_iff.1 𝔔 admissible_designLaw_le_cubeVolume
    𝔄
    𝔈
  rw [Measure.smul_apply, smul_eq_mul] at hdom
  have hcap : (designLaw θ) 𝔄 ≤
      ENNReal.ofReal C.densityUpper * ENNReal.ofReal 𝔅 ^ d := by
    apply hdom.trans
    gcongr
    exact 𝔑 regular_grid_fiber_volume_le c
  have hu : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  apply (ENNReal.toReal_mono (by finiteness) hcap).trans_eq
  simp_all

theorem regularGridProbability_cap C
    (θ : RegressionParameter d) (hθ : 𝔎) k hk
    c :
    𝔊 ≤ C.densityUpper / 𝗋 := by
  convert 𝔔 regularGridProbability_le k hk c using 1 <;> rw [div_pow, one_pow] <;> ring
