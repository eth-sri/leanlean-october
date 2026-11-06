module

public import NearlyMinimax.IncrementPilotKernels
public import NearlyMinimax.DyadicTaylor
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine physical feature-row factors for the sharp pair pilot. -/
open MeasureTheory ProbabilityTheory Matrix
𝚺
𝚨

theorem dyadicPilotCell_subset_coarser j J (hj : j ≤ J) (x : Covariate d) :
    dyadicPilotCell J x ⊆ dyadicPilotCell j x := by
  induction J with
  | zero =>
    have he : 𝘠 := 𝖡₃
    subst j
    exact subset_rfl
  | succ J ih =>
    by_cases he : j = 𝗯
    · simp_all
    · intro z hz
      apply ih 𝖡₃
      simpa using dyadicPilotCell_subset_parent 𝗯 x hz

𝗇 𝔄 z - x
𝗇 𝔅 𝗜
𝗇 𝔉 𝗌
𝗇 𝔊 z ∈ unitCube d
𝗇 𝔍 𝙉 ^ j
𝗇 𝔎 𝘷
theorem dyadicAnchoredFeature_abs_le_distance j x z
    (hx : 𝔉) (hz : 𝔊) (hc : z ∈ dyadicPilotCell j x)
    (γ : 𝗎) :
    |𝘧₁ γ| ≤ 𝔅 * euclideanNorm 𝔄 := by
  have hv i : |(𝔍 • 𝔄) i| ≤ 1 := by
    have hr := regular_grid_same_cell_radius 𝔎  𝖠₃  z x hz hx hc i
    have he : (𝔅 : ℕ) = 𝔍 := 𝖢₄
    rw [he] at hr
    change |𝔎 * (z i - x i)| ≤ 1
    rw [abs_mul, abs_of_nonneg 𝖠₃ ]
    exact (mul_le_mul_of_nonneg_left hr 𝖠₃ ).trans_eq 𝖧₃
  have h := anchoredMonomial_abs_le_euclideanNorm γ (𝔎 • 𝔄) hv
  rw [euclideanNorm_smul, abs_of_nonneg $ pow_nonneg (by norm_num : 𝙋 ≤ 2) j ] at h
  exact h

𝗇 𝔇 𝚃
def dyadicPilotRow (j : ℕ) (x z : Covariate d) : Fin 𝔇 → ℝ :=
  fun i => 𝘧₁ $ anchoredFinIndex i

𝗇 𝔈 dyadicPilotRow (ℓ := ℓ) j x z i
theorem dyadicPilotRow_sum_abs_le_distance j x z
    (hx : 𝔉) (hz : 𝔊) (hc : z ∈ dyadicPilotCell j x) :
     ∑ i, |𝔈| ≤
      𝔇 * 𝔅 * euclideanNorm 𝔄 := by
  apply (Finset.sum_le_sum fun i _ => dyadicAnchoredFeature_abs_le_distance j x z hx hz hc _ ).trans_eq
  simp [mul_assoc]

𝗇 𝔏 𝖵₂
/-- Every feature row for a coarser pilot satisfies its genuine `h 2^j`
factor on the actual finest dyadic same-cell pair support. -/
theorem dyadicPilotRow_sum_abs_le_fine_cell j J (hj : j ≤ J)
    x z (hx : 𝔉) (hz : 𝔊)
    (hc : z ∈ dyadicPilotCell J x) :
     ∑ i, |𝔈| ≤
      𝔇 * 𝔅 * Real.sqrt d * 𝔏⁻¹ := by
  apply (dyadicPilotRow_sum_abs_le_distance j x z hx hz
    $ dyadicPilotCell_subset_coarser j J hj x hc ).trans
  have hr := euclideanNorm_le_coordinate_radius 𝔄 (1 / (𝔏 : ℕ) )
     𝖠₃  $ regular_grid_same_cell_radius (2 ^ J)  𝖠₃  z x hz hx hc
  apply (mul_le_mul_of_nonneg_left hr 𝖠₃ ).trans_eq
  grind
