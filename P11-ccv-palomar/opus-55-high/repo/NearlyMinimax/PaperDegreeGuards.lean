module

public import NearlyMinimax.DyadicBiasAllocation
public import NearlyMinimax.AnchoredCard
public import NearlyMinimax.SampleThirds
public import NearlyMinimax.DyadicPilotPointwise
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual floored degrees satisfy the factorial-lift sample guards.
The polynomial coordinate cost is the exact binomial feature dimension. -/
open Filter MeasureTheory
𝚪
𝚨
𝚭
𝚩

theorem paperPolynomialDimension_eq_anchoredDimension_add_one (C : ModelConstants d) :
    paperPolynomialDimension C = 𝗣 + 1 := by
  unfold paperPolynomialDimension anchoredDimension
  rw [anchoredIndex_card]
  have hp : 0 < (d + C.order).choose d := Nat.choose_pos 𝖡₃
  omega

𝗃 𝔐 ἀ C a offset H n
def paperDyadicTotalDegree (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  𝔐 paperDyadicApproximationDegree j + 𝗣 + 1

𝗇 𝔄 𝔐 paperDyadicTotalDegree j
𝗇 𝔈 div_pos (paperSpatialExponent_pos C hs) $ paperTau_pos C
𝗇 𝔉 allocationLevelPosition (paperDyadicStep C) a offset H
𝗇 𝔍 𝘎
𝗇 𝔎 𝙆
/-- Eventually the coordinate subtraction has no truncation: the actual total
lift degree is exactly the floor of the quadratic profile at every level. -/
theorem eventually_paper_total_degree_eq_floor (C : ModelConstants d)
    (hs : 𝔍) a offset H (ha : 𝔎) :
    ∀ᶠ n : ℝ in atTop, ∀ j ,
      𝔄 =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (𝔉 n j)) := by
  have hβ : 0 < paperDegreeSlope C := 𝔈
  filter_upwards [eventually_width_degree_threshold ha hβ offset $ paperPolynomialDimension C ,
    (allocationWidth_tendsto_atTop ha offset).eventually $ eventually_gt_atTop 0 ]
    with n hn hS
  intro j
  unfold paperDyadicTotalDegree paperDyadicApproximationDegree actualApproximationDegree allocatedApproximationDegree
  rw [Nat.add_assoc, ← paperPolynomialDimension_eq_anchoredDimension_add_one C]
  exact Nat.sub_add_cancel $ profile_coordinate_order_admissible _ hβ.le hS 𝖡₄

𝗇 𝔅 𝔐 paperDyadicTerminalLevel
𝗇 𝔊 allocationDegreeCoefficient a $ paperDegreeSlope C
𝗃 𝔏 ἀ C hs a offset H ha
/-- The exact lift degrees have the paper's uniform logarithmic growth. -/
theorem eventually_paper_total_degree_log_bound (C : ModelConstants d)
    (hs : 𝔍) a offset H (ha : 𝔎) (hH : 𝚉) :
    ∀ᶠ n : ℝ in atTop, ∀ j ≤ 𝔅,
      𝔄 ≤
        𝔊 * Real.log n ^ (𝗞 : ℝ) := by
  have hγ : 0 ≤ paperDegreeReserve C := by
    exact div_nonneg  𝖠₃  (paperSpatialExponent_pos C hs).le
  have hb := eventually_allocation_degree_bound ha (𝔈).le offset
    (fun n => Finset.range $ terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n + 1 )
    𝔉
    $ eventually_actual_allocation_level_range (paperDyadicStep_pos C) ha hH hγ offset
  filter_upwards [𝔏 eventually_paper_total_degree_eq_floor, hb] with n he hn
  aesop

/-- Every fixed positive sample fraction dominates all actual lift degrees. -/
theorem eventually_paper_total_degree_lt_fraction (C : ModelConstants d)
    (hs : 𝔍) a offset H (ha : 𝔎) (hH : 𝚉)
    (hε : 0 < ε) :
    ∀ᶠ n : ℝ in atTop, ∀ j ≤ 𝔅,
      𝔄 < ε * n := by
  filter_upwards [𝔏 eventually_paper_total_degree_log_bound hH,
    eventually_log_power_lt_sample 𝗞 𝔊 hε]
    with n hn he
  grind

𝗇 𝔇 𝚝
/-- The actual two-pilot split permits the exact factorial lifts and the
variance denominator Λ=N/2, uniformly over every allocated level. -/
theorem eventually_paper_degree_three_block_guards (C : ModelConstants d)
    (hs : 𝔍) a offset H (ha : 𝔎) (hH : 𝚉) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ 𝔅,
      𝔄 ≤ threeBlockSize n ∧
      0 < 𝔇 / 2 ∧
       threeBlockSize n / 2 ≤
         threeBlockSize n - (𝔄 : ℝ) + 1 := by
  have hb : ∀ᶠ n : ℕ in atTop, ∀ j ≤ 𝔅,
      𝔄 < (1 / 8 : ℝ) * n :=
    tendsto_natCast_atTop_atTop.eventually
      $ 𝔏 eventually_paper_total_degree_lt_fraction hH 𝖠₄
  filter_upwards [hb, eventually_ge_atTop 6] with n hn h6
  intro j hj
  have hm := threeBlockSize_fraction h6
  have hd := hn j hj
  have hhalf : 𝔄 ≤ 𝔇 / 2 := by
    linarith
  have hmpos : 0 < 𝔇 := by
    linarith
  refine ⟨?_, 𝖠₃, 𝖡₄⟩
  exact_mod_cast hhalf.trans (by linarith : 𝔇 / 2 ≤ threeBlockSize n)
