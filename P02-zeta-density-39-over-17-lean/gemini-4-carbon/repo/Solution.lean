module

public import CountCore
public import WrittenDensity.Common
public import GuthMaynard.Improvement.NativeIngham
public import GuthMaynard.Improvement.WeakShortDensity
public import TwoTermZeroDensity
public import AdjacentZeroDensity
public import ThirdZeroDensity
public import MathCollab.Density.Stronger.NativeDensity
public import RightSolidActualDensity
public import DashedInitialActualDensity
public import TraceAlternatives.NativeCubeRows34
public import TraceAlternatives.NativeUniversalRows45
public import LaterPairs.NativeSharpRows78

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
public section
namespace LewkoDensityPalomar

open MathCollab.Density Montgomery.WrittenDensity GuthMaynard.Improvement MathCollab.Density.Stronger
open Montgomery.RationalMoment Montgomery.RationalMoment.RightDetector Montgomery.RationalMoment.RightDetector.Physical

variable {σ ε : ℝ}

theorem provider_P1 (hlo : 1/2 ≤ σ) (hhi : σ ≤ 7/10) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  apply of_db
  rw [show (-3/(σ - 2))*(1-σ) = (3/(2 - σ))*(1-σ) by field_simp [show σ - 2 ≠ 0 by linarith, show 2 - σ ≠ 0 by linarith]; ring]
  by_cases h : σ ≤ 9/13
  · exact weaken_frac (ingham_lower_density σ hlo h ε hε)
  · exact weaken_frac (short_density (by linarith) (by linarith) hε)

theorem piece_G2 (hlo : 7/10 ≤ σ) (hhi : σ ≤ 19/25) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  apply of_db
  by_cases h1 : σ ≤ 5/7
  · exact weaken_frac (short_density (by linarith) h1 hε)
  by_cases h2 : σ ≤ 113/153
  · exact weaken_frac (adjacent_density_second (by linarith) h2 hε)
  by_cases h3 : σ ≤ 3/4
  · exact weaken_frac (third_density_segment (by linarith) h3 hε)
  · exact weaken_frac (stronger_density_bound_native (by linarith) hε)

theorem provider_P2 (hlo : 7/10 ≤ σ) (hhi : σ < 19/25) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) :=
  piece_G2 hlo hhi.le hε

theorem provider_P3 (hlo : 19/25 ≤ σ) (hhi : σ < 127/167) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (stronger_density_bound_native (by linarith) hε)

theorem provider_P4 (hlo : 127/167 ≤ σ) (hhi : σ < 13/17) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (stronger_density_bound_native (by linarith) hε)

theorem piece_G5 (hlo : 13/17 ≤ σ) (hhi : σ ≤ 17/22) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (stronger_density_bound_native (by linarith) hε)

theorem provider_P5 (hlo : 13/17 ≤ σ) (hhi : σ < 17/22) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) :=
  piece_G5 hlo hhi.le hε

theorem provider_P6 (hlo : 17/22 ≤ σ) (hhi : σ < 41/53) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (stronger_density_bound_native (by linarith) hε)

theorem piece_G7 (hlo : 41/53 ≤ σ) (hhi : σ ≤ 7/9) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (stronger_density_bound_native (by linarith) hε)

theorem provider_P7 (hlo : 41/53 ≤ σ) (hhi : σ < 7/9) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) :=
  piece_G7 hlo hhi.le hε

theorem provider_P8 (hlo : 7/9 ≤ σ) (hhi : σ < 1867/2347) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  apply of_db
  by_cases h1 : σ ≤ 29359/37574
  · exact weaken_frac (density_right_solid_first hlo h1 hε)
  by_cases h2 : σ ≤ 1015/1294
  · exact weaken_frac (density_right_solid_second (by linarith) h2 hε)
  by_cases h3 : σ ≤ 353/447
  · exact weaken_frac (density_right_solid_third (by linarith) h3 hε)
  · exact weaken_frac (density_right_solid_fourth (by linarith) (by linarith) hε)

private theorem p13_aux (hlo : 3/4 < σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (stronger_density_bound_native hlo hε)

theorem provider_P9 (hlo : 23/29 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  p13_aux (by linarith) hhi hε

theorem provider_P10 (hlo : 7/10 < σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  apply of_db
  by_cases hz : 7/8 < σ
  · exact density_of_actual_zero hz
  by_cases h1 : σ ≤ 5/7
  · exact weaken_frac (short_density (by linarith) h1 hε)
  by_cases h2 : σ ≤ 113/153
  · exact weaken_frac (adjacent_density_second (by linarith) h2 hε)
  by_cases h3 : σ ≤ 3/4
  · exact weaken_frac (third_density_segment (by linarith) h3 hε)
  · exact weaken_frac (stronger_density_bound_native (by linarith) hε)

theorem provider_P11 (hlo : 9/13 ≤ σ) (hhi : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (short_density hlo hhi hε)

theorem provider_P12 (hlo : 5/7 ≤ σ) (hhi : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  apply of_db
  by_cases h : σ ≤ 113/153
  · exact weaken_frac (adjacent_density_second hlo h hε)
  · exact weaken_frac (third_density_segment (by linarith) hhi hε)

theorem provider_P13 (hlo : 3/4 < σ) (hhi : σ < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  p13_aux hlo hhi.le hε

theorem provider_P14 (hlo : 7/10 ≤ σ) (hhi : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  apply of_db
  by_cases h : σ ≤ 12/17
  · exact weaken_frac (short_density (by linarith) (by linarith) hε)
  · exact weaken_frac (two_term_density_first (by linarith) hhi hε)

theorem provider_P15 (hlo : 5/7 ≤ σ) (hhi : σ ≤ 113/153) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (adjacent_density_second hlo hhi hε)

theorem provider_P16 (hlo : 113/153 ≤ σ) (hhi : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (third_density_segment hlo hhi hε)

theorem provider_P17 (hlo : 7/9 ≤ σ) (hhi : σ ≤ 29359/37574) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_right_solid_first hlo hhi hε)

theorem provider_P18 (hlo : 29359/37574 ≤ σ) (hhi : σ ≤ 1015/1294) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_right_solid_second hlo hhi hε)

theorem provider_P19 (hlo : 1015/1294 ≤ σ) (hhi : σ ≤ 353/447) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_right_solid_third hlo hhi hε)

theorem provider_P20 (hlo : 353/447 ≤ σ) (hhi : σ ≤ 467/586) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_right_solid_fourth hlo hhi hε)

theorem provider_P21 (hlo : 467/586 ≤ σ) (hhi : σ ≤ 289/358) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) := by
  apply of_db
  by_cases h : σ ≤ 4/5
  · exact weaken_frac (density_right_solid_fifth hlo h hε)
  · exact weaken_frac (density_dashed_first (by linarith) hhi hε)

theorem provider_P22 (hlo : 289/358 ≤ σ) (hhi : σ ≤ 163/198) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_dashed_second hlo hhi hε)

theorem provider_P23 (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_cube_row3 hlo hhi hε)

theorem provider_P24 (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 2018/2375) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_universal_row4 hlo hhi hε)

theorem provider_P25 (hlo : 2018/2375 ≤ σ) (hhi : σ ≤ 1959705/2298302) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_universal_row5 hlo hhi hε)

theorem provider_P26 (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_sharp_row6 hlo hhi hε)

theorem provider_P27 (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_sharp_row7 hlo hhi hε)

theorem provider_P28 (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) :=
  of_db <| weaken_frac (density_sharp_row8 hlo hhi hε)

theorem uniform_P29 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 7/8 ≤ σ → σ ≤ 1 → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  obtain ⟨C, hC, h⟩ := density_sharp_row8 (σ := 7/8) (by norm_num) le_rfl hε
  refine ⟨C, hC, fun σ T hlo _ hT => zeroCount_le_of_nat T ?_⟩
  exact (Nat.cast_le.mpr (zetaDensityCount_mono hlo le_rfl)).trans (by convert h T hT using 2; norm_num)

theorem uniform_P30 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 19/22 ≤ σ → σ ≤ 23/26 → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  have hunif : ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 19/22 ≤ σ → σ ≤ 23/26 → 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ (((24/(30*σ-11))*(1-σ)) + ε) := by
    apply density_curve_uniform_on_interval (K := 457) (by norm_num) (by norm_num) _ _ hε
    · intro x y hx hxy hy
      have hx0 : 0 < 30 * x - 11 := by linarith
      have hy0 : 0 < 30 * y - 11 := by linarith
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_le_iff_le_add',
        div_sub_div _ _ hx0.ne' hy0.ne', div_le_iff₀ (mul_pos hx0 hy0)]
      have hp : 1 ≤ (30 * x - 11) * (30 * y - 11) := by nlinarith
      have hnum : 24 * (1 - x) * (30 * y - 11) - (30 * x - 11) * (24 * (1 - y)) = 456 * (y - x) := by ring
      linarith [hnum, mul_le_mul_of_nonneg_left hp (show 0 ≤ 456 * (y - x) by linarith)]
    · intro σ hlo hhi ε hε
      change DensityBound σ ((24/(30*σ-11))*(1-σ)) ε
      by_cases hz : 7/8 < σ
      · exact density_of_actual_zero hz
      by_cases h1 : σ ≤ 2905/3354
      · exact weaken_frac (density_sharp_row7 (by linarith) h1 hε)
      · exact weaken_frac (density_sharp_row8 (by linarith) (by linarith) hε)
  obtain ⟨C, hC, hb⟩ := hunif
  exact ⟨C, hC, fun σ T hlo hhi hT => zeroCount_le_of_nat T (hb σ T hlo hhi hT)⟩

theorem uniform_P31 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 23/26 ≤ σ → σ ≤ 1 → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  refine ⟨1, zero_lt_one, fun σ T hlo _ hT => zeroCount_le_of_nat T ?_⟩
  rw [Montgomery.ZeroFreeHatching.actual_density_count_zero (by linarith : 7/8 < σ), Nat.cast_zero]
  have : 0 < T := by linarith
  positivity

theorem provider_P29 (hlo : 7/8 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) :=
  let ⟨C, hC, h⟩ := uniform_P29 hε; ⟨C, hC, fun T => h σ T hlo hhi⟩

theorem provider_P30 (hlo : 19/22 ≤ σ) (hhi : σ ≤ 23/26) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) :=
  let ⟨C, hC, h⟩ := uniform_P30 hε; ⟨C, hC, fun T => h σ T hlo hhi⟩

theorem provider_P31 (hlo : 23/26 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) :=
  let ⟨C, hC, h⟩ := uniform_P31 hε; ⟨C, hC, fun T => h σ T hlo hhi⟩

theorem piece_G1 (hlo : 1/2 ≤ σ) (hhi : σ ≤ 7/10) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) :=
  provider_P1 hlo hhi hε

theorem piece_G3 (hlo : 19/25 ≤ σ) (hhi : σ < 127/167) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) :=
  provider_P3 hlo hhi hε

theorem piece_G4 (hlo : 127/167 ≤ σ) (hhi : σ < 13/17) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) :=
  provider_P4 hlo hhi hε

theorem piece_G6 (hlo : 17/22 ≤ σ) (hhi : σ < 41/53) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) :=
  provider_P6 hlo hhi hε

theorem piece_G8 (hlo : 7/9 ≤ σ) (hhi : σ < 23/29) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) :=
  provider_P8 hlo (by linarith) hε

theorem piece_G9 (hlo : 23/29 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  p13_aux (by linarith) (by linarith) hε

theorem piece_G10 (hlo : 7/8 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) :=
  provider_P10 (by linarith) hhi hε

theorem piece_B1 (hlo : 1/2 ≤ σ) (hhi : σ ≤ 9/13) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) :=
  provider_P1 hlo (by linarith) hε

theorem piece_B2 (hlo : 9/13 ≤ σ) (hhi : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) :=
  provider_P11 hlo hhi hε

theorem piece_B3 (hlo : 5/7 ≤ σ) (hhi : σ ≤ 11/15) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) :=
  provider_P12 hlo (by linarith) hε

theorem piece_B4 (hlo : 11/15 ≤ σ) (hhi : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) :=
  piece_G2 (by linarith) (by linarith) hε

theorem piece_B5 (hlo : 3/4 < σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  p13_aux hlo (by linarith) hε

theorem piece_B6 (hlo : 7/8 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) :=
  provider_P10 (by linarith) hhi hε

theorem piece_O1 (hlo : 1/2 ≤ σ) (hhi : σ ≤ 9/13) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) :=
  provider_P1 hlo (by linarith) hε

theorem piece_O2 (hlo : 9/13 ≤ σ) (hhi : σ ≤ 12/17) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) :=
  provider_P11 hlo (by linarith) hε

theorem piece_O3 (hlo : 12/17 ≤ σ) (hhi : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) :=
  provider_P14 (by linarith) hhi hε

theorem piece_O4 (hlo : 5/7 ≤ σ) (hhi : σ ≤ 113/153) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) :=
  provider_P15 hlo hhi hε

theorem piece_O5 (hlo : 113/153 ≤ σ) (hhi : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) :=
  provider_P16 hlo hhi hε

theorem piece_O6 (hlo : 3/4 < σ) (hhi : σ ≤ 7/9) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  p13_aux hlo (by linarith) hε

theorem piece_O7 (hlo : 7/9 ≤ σ) (hhi : σ ≤ 29359/37574) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) :=
  provider_P17 hlo hhi hε

theorem piece_O8 (hlo : 29359/37574 ≤ σ) (hhi : σ ≤ 1015/1294) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) :=
  provider_P18 hlo hhi hε

theorem piece_O9 (hlo : 1015/1294 ≤ σ) (hhi : σ ≤ 353/447) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) :=
  provider_P19 hlo hhi hε

theorem piece_O10 (hlo : 353/447 ≤ σ) (hhi : σ ≤ 467/586) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) :=
  provider_P20 hlo hhi hε

theorem piece_O11 (hlo : 467/586 ≤ σ) (hhi : σ ≤ 289/358) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) :=
  provider_P21 hlo hhi hε

theorem piece_O12 (hlo : 289/358 ≤ σ) (hhi : σ ≤ 163/198) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) :=
  provider_P22 hlo hhi hε

theorem piece_O13 (hlo : 163/198 ≤ σ) (hhi : σ ≤ 7873/9370) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) :=
  provider_P23 hlo hhi hε

theorem piece_O14 (hlo : 7873/9370 ≤ σ) (hhi : σ ≤ 2018/2375) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) :=
  provider_P24 hlo hhi hε

theorem piece_O15 (hlo : 2018/2375 ≤ σ) (hhi : σ ≤ 1959705/2298302) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) :=
  provider_P25 hlo hhi hε

theorem piece_O16 (hlo : 1959705/2298302 ≤ σ) (hhi : σ ≤ 6482825/7570038) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) :=
  provider_P26 hlo hhi hε

theorem piece_O17 (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) :=
  provider_P27 hlo hhi hε

theorem piece_O18 (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) :=
  provider_P28 hlo hhi hε

theorem piece_O19 (hlo : 7/8 ≤ σ) (hhi : σ ≤ 24139/27578) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) :=
  provider_P29 hlo (by linarith) hε

theorem piece_O20 (hlo : 24139/27578 ≤ σ) (hhi : σ ≤ 23/26) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) :=
  provider_P30 (by linarith) hhi hε

theorem piece_O21 (hlo : 23/26 ≤ σ) (hhi : σ ≤ 17/19) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) :=
  provider_P31 hlo (by linarith) hε

theorem piece_O22 (hlo : 17/19 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) :=
  provider_P10 (by linarith) hhi hε

theorem global39over17 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((39/17*(1-σ)) + ε)) := by
  have hunif : ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ ((39/17*(1-σ)) + ε) := by
    apply density_curve_uniform_on_interval (K := 3) (by norm_num) (by norm_num) _ _ hε
    · intros; linarith
    · intro σ hlo hhi ε hε
      change DensityBound σ (39/17*(1-σ)) ε
      by_cases h1 : σ ≤ 9/13
      · exact weaken_frac (ingham_lower_density σ hlo h1 ε hε)
      by_cases h2 : σ ≤ 5/7
      · exact weaken_frac (short_density (by linarith) h2 hε)
      by_cases h3 : σ ≤ 113/153
      · exact weaken_frac (adjacent_density_second (by linarith) h3 hε)
      by_cases h4 : σ ≤ 3/4
      · exact weaken_frac (third_density_segment (by linarith) h4 hε)
      · exact weaken_frac (stronger_density_bound_native (by linarith) hε)
  obtain ⟨C, hC, hb⟩ := hunif
  exact ⟨C, hC, fun σ T hlo hhi hT => zeroCount_le_of_nat T (hb σ T hlo hhi hT)⟩

end LewkoDensityPalomar
