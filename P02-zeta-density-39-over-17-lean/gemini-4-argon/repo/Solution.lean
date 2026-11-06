module
public import CountCore
public import GuthMaynard.Improvement.GlobalDensity
public import MonotoneCurve.ActualDensity
public import RightSolidActualDensity
public import TraceAlternatives.NativeUniversalRows45
public import WrittenDensity.Uniform

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
open scoped BigOperators ENNReal
public section
namespace LewkoDensityPalomar
open MathCollab.Density GuthMaynard.Improvement MathCollab.Density.Stronger Montgomery.RationalMoment Montgomery.RationalMoment.RightDetector Montgomery.RationalMoment.RightDetector.Physical Montgomery.WrittenDensity

variable {σ ε : ℝ}

local notation "ZB" a "," b "," E =>
  (a : ℝ) ≤ σ → σ ≤ (b : ℝ) → 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((E * (1 - σ)) + ε))

local notation "ZBL" a "," b "," E =>
  (a : ℝ) ≤ σ → σ < (b : ℝ) → 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((E * (1 - σ)) + ε))

private theorem bdw {c d c' d' : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ (c * (1 - σ) / d + ε))
    (hd : 0 < d := by linarith) (hd' : 0 < d' := by linarith)
    (h1 : σ ≤ 1 := by linarith) (hc : c * d' ≤ c' * d := by linarith) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((c' / d') * (1 - σ)) + ε)) :=
  bound_of_div_weaken h hd hd' h1 hc

private theorem sbdw {c' d' : ℝ} (hε : 0 < ε) (hlo : 3/4 < σ := by linarith)
    (hd : 0 < 2*σ := by linarith) (hd' : 0 < d' := by linarith)
    (h1 : σ ≤ 1 := by linarith) (hc : 3 * d' ≤ c' * (2*σ) := by linarith) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((c' / d') * (1 - σ)) + ε)) :=
  bound_of_div_weaken (stronger_density_bound_native hlo hε) hd hd' h1 hc

theorem global39over17 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((39/17 : ℝ)*(1-σ)) + ε)) := by
  obtain ⟨C, hC, hb⟩ := global_density_uniform hε
  refine ⟨C, hC, fun σ T hlo hhi hT => ?_⟩
  rw [zeroCount_eq_zetaDensityCount, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb σ T hlo hhi hT)

theorem uniform_P29 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  obtain ⟨C, hC, hb⟩ := Montgomery.MonotoneCurve.seven_eighths_right_uniform hε
  refine ⟨C, hC, fun σ T hlo _ hT => ?_⟩
  rw [zeroCount_eq_zetaDensityCount, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb σ hlo T hT)

theorem uniform_P30 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ →
      σ ≤ (23/26 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  obtain ⟨C, hC, hb⟩ := uniform_source_oct2_mixed_4 hε
  refine ⟨C, hC, fun σ T hlo hhi hT => ?_⟩
  rw [zeroCount_eq_zetaDensityCount, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ((hb σ T hlo hhi hT).trans_eq ?_)
  congr 2; ring

theorem uniform_P31 (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  obtain ⟨C, hC, hb⟩ := uniform_source_oct2_mixed_5 hε
  refine ⟨C, hC, fun σ T hlo hhi hT => ?_⟩
  rw [zeroCount_eq_zetaDensityCount, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ((hb σ T hlo hhi hT).trans_eq ?_)
  congr 2; ring

theorem provider_P1 : ZB 1/2, 7/10, -3/(σ - 2) := by
  intro hlo hhi hε
  rw [show σ - 2 = -(2 - σ) by ring, div_neg, neg_div, neg_neg]
  by_cases h : σ ≤ 9/13
  · exact bdw (ingham_lower_density σ hlo h ε hε)
  · exact bdw (short_density (by linarith) (by linarith) hε)

theorem piece_G2 : ZB 7/10, 19/25, 15/(5*σ + 3) := by
  intro hlo hhi hε
  by_cases h1 : σ ≤ 5/7
  · exact bdw (short_density (by linarith) h1 hε)
  by_cases h2 : σ ≤ 113/153
  · exact bdw (adjacent_density_second (by linarith) h2 hε)
  by_cases h3 : σ ≤ 3/4
  · exact bdw (third_density_segment (by linarith) h3 hε)
  · exact sbdw hε

theorem provider_P2 : ZBL 7/10, 19/25, 15/(5*σ + 3) :=
  fun hlo hhi => piece_G2 hlo hhi.le

theorem provider_P3 : ZBL 19/25, 127/167, 9/(8*σ - 2) := fun _ _ => sbdw
theorem provider_P4 : ZBL 127/167, 13/17, 15/(13*σ - 3) := fun _ _ => sbdw
theorem piece_G5 : ZB 13/17, 17/22, 6/(5*σ - 1) := fun _ _ => sbdw
theorem provider_P5 : ZBL 13/17, 17/22, 6/(5*σ - 1) := fun hlo hhi => piece_G5 hlo hhi.le
theorem provider_P6 : ZBL 17/22, 41/53, 2/(9*σ - 6) := fun _ _ => sbdw
theorem piece_G7 : ZB 41/53, 7/9, 9/(7*σ - 1) := fun _ _ => sbdw
theorem provider_P7 : ZBL 41/53, 7/9, 9/(7*σ - 1) := fun hlo hhi => piece_G7 hlo hhi.le
theorem provider_P8 : ZBL 7/9, 1867/2347, 9/(16*σ - 8) := fun _ _ => sbdw
theorem provider_P9 : ZB 23/29, 1, 3/(2*σ) := fun _ _ => sbdw

theorem provider_P10 (hlo : (7/10 : ℝ) < σ) (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  by_cases h1 : σ ≤ 3/4
  · obtain ⟨C, hC, hb⟩ := global_density_uniform hε
    refine bound_of_weaken ⟨C, hC, fun T hT => hb σ T (by linarith) hhi hT⟩ ?_
    rw [div_mul_eq_mul_div (3 : ℝ), le_div_iff₀ (by linarith)]
    nlinarith
  by_cases h2 : σ ≤ 7/8
  · exact sbdw hε
  · exact bound_of_weaken (density_of_actual_zero (by linarith)) le_rfl

theorem provider_P11 : ZB 9/13, 5/7, 18/(7*σ+3) :=
  fun hlo hhi hε => bdw (short_density hlo hhi hε)

theorem provider_P12 : ZB 5/7, 3/4, 9/4 := by
  intro hlo hhi hε
  by_cases h : σ ≤ 113/153
  · exact bdw (adjacent_density_second hlo h hε)
  · exact bdw (third_density_segment (by linarith) hhi hε)

theorem provider_P13 (hlo : (3/4 : ℝ) < σ) (hhi : σ < (1 : ℝ)) :
    0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  sbdw

theorem provider_P14 : ZB 7/10, 5/7, 6/(8*σ-3) := by
  intro hlo hhi hε
  by_cases h : σ ≤ 12/17
  · exact bdw (short_density (by linarith) (by linarith) hε)
  · exact bdw (two_term_density_first (by linarith) hhi hε)

theorem provider_P15 : ZB 5/7, 113/153, 12/(9*σ-1) :=
  fun hlo hhi hε => bdw (adjacent_density_second hlo hhi hε)

theorem provider_P16 : ZB 113/153, 3/4, 255/(153*σ+7) :=
  fun hlo hhi hε => bdw (third_density_segment hlo hhi hε)

theorem provider_P17 : ZB 7/9, 29359/37574, 3/(11*σ-7) :=
  fun hlo hhi hε => bdw (density_right_solid_first hlo hhi hε)

theorem provider_P18 : ZB 29359/37574, 1015/1294, 4744/(4870*σ-1283) :=
  fun hlo hhi hε => bdw (density_right_solid_second hlo hhi hε)

theorem provider_P19 : ZB 1015/1294, 353/447, 6154/(6354*σ-1693) :=
  fun hlo hhi hε => bdw (density_right_solid_third hlo hhi hε)

theorem provider_P20 : ZB 353/447, 467/586, 3782/(3936*σ-1065) :=
  fun hlo hhi hε => bdw (density_right_solid_fourth hlo hhi hε)

theorem provider_P21 : ZB 467/586, 289/358, 2168/(2282*σ-631) :=
  fun hlo hhi hε => bdw (density_dashed_first hlo hhi hε)

theorem provider_P22 : ZB 289/358, 163/198, 566/(606*σ-173) :=
  fun hlo hhi hε => bdw (density_dashed_second hlo hhi hε)

theorem provider_P23 : ZB 163/198, 7873/9370, 31544/(35670*σ-11203) :=
  fun hlo hhi hε => bdw (density_cube_row3 hlo hhi hε)

theorem provider_P24 : ZB 7873/9370, 2018/2375, 1261710/(1447460*σ-465509) :=
  fun hlo hhi hε => bdw (density_universal_row4 hlo hhi hε)

theorem provider_P25 : ZB 2018/2375, 1959705/2298302, 3066/(3616*σ-1215) :=
  fun hlo hhi hε => bdw (density_universal_row5 hlo hhi hε)

theorem provider_P26 : ZB 1959705/2298302, 6482825/7570038, 597962/(729216*σ-257415) :=
  fun hlo hhi hε => bdw (density_sharp_row6 hlo hhi hε)

theorem provider_P27 : ZB 6482825/7570038, 2905/3354, 16504356/(20732766*σ-7623595) :=
  fun hlo hhi hε => bdw (density_sharp_row7 hlo hhi hε)

theorem provider_P28 : ZB 2905/3354, 7/8, 2172/(2742*σ-1015) :=
  fun hlo hhi hε => bdw (density_sharp_row8 hlo hhi hε)

theorem provider_P29 (hlo : (7/8 : ℝ) ≤ σ) (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  obtain ⟨C, hC, hb⟩ := uniform_P29 hε
  exact ⟨C, hC, fun T hT => hb σ T hlo hhi hT⟩

theorem provider_P30 : ZB 19/22, 23/26, 24/(30*σ-11) := by
  intro hlo hhi hε
  obtain ⟨C, hC, hb⟩ := uniform_P30 hε
  exact ⟨C, hC, fun T hT => hb σ T hlo hhi hT⟩

theorem provider_P31 : ZB 23/26, 1, 6/(σ+3) := by
  intro hlo hhi hε
  obtain ⟨C, hC, hb⟩ := uniform_P31 hε
  exact ⟨C, hC, fun T hT => hb σ T hlo hhi hT⟩

alias piece_G1 := provider_P1
alias piece_G3 := provider_P3
alias piece_G4 := provider_P4
alias piece_G6 := provider_P6

theorem piece_G8 : ZBL 7/9, 23/29, 9/(16*σ - 8) :=
  fun hlo hhi => provider_P8 hlo (by linarith)

theorem piece_G9 : ZB 23/29, 7/8, 3/(2*σ) :=
  fun hlo hhi => provider_P9 hlo (by linarith)

theorem piece_G10 : ZB 7/8, 1, 3/(10*σ - 7) :=
  fun hlo hhi => provider_P10 (by linarith) hhi

theorem piece_B1 : ZB 1/2, 9/13, -3/(σ - 2) :=
  fun hlo hhi => provider_P1 hlo (by linarith)

alias piece_B2 := provider_P11

theorem piece_B3 : ZB 5/7, 11/15, 9/4 :=
  fun hlo hhi => provider_P12 hlo (by linarith)

theorem piece_B4 : ZB 11/15, 3/4, 15/(5*σ + 3) :=
  fun hlo hhi => piece_G2 (by linarith) (by linarith)

theorem piece_B5 (hlo : (3/4 : ℝ) < σ) (hhi : σ ≤ (7/8 : ℝ)) :
    0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  provider_P13 hlo (by linarith)

alias piece_B6 := piece_G10
alias piece_O1 := piece_B1

theorem piece_O2 : ZB 9/13, 12/17, 18/(7*σ+3) :=
  fun hlo hhi => provider_P11 hlo (by linarith)

theorem piece_O3 : ZB 12/17, 5/7, 6/(8*σ-3) :=
  fun hlo hhi => provider_P14 (by linarith) hhi

alias piece_O4 := provider_P15
alias piece_O5 := provider_P16

theorem piece_O6 (hlo : (3/4 : ℝ) < σ) (hhi : σ ≤ (7/9 : ℝ)) :
    0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  provider_P13 hlo (by linarith)

alias piece_O7 := provider_P17
alias piece_O8 := provider_P18
alias piece_O9 := provider_P19
alias piece_O10 := provider_P20
alias piece_O11 := provider_P21
alias piece_O12 := provider_P22
alias piece_O13 := provider_P23
alias piece_O14 := provider_P24
alias piece_O15 := provider_P25
alias piece_O16 := provider_P26
alias piece_O17 := provider_P27
alias piece_O18 := provider_P28

theorem piece_O19 (hlo : (7/8 : ℝ) ≤ σ) (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) :=
  provider_P29 hlo (by linarith) hε

theorem piece_O20 : ZB 24139/27578, 23/26, 24/(30*σ-11) :=
  fun hlo hhi => provider_P30 (by linarith) hhi

theorem piece_O21 : ZB 23/26, 17/19, 6/(σ+3) :=
  fun hlo hhi => provider_P31 hlo (by linarith)

theorem piece_O22 : ZB 17/19, 1, 3/(10*σ - 7) :=
  fun hlo hhi => provider_P10 (by linarith) hhi

