module
public import CountCore
public import DensityStrip.Count
public import DensityStrip.Rows
public import DensityStrip.LeftRows
public import DashedInitialActualDensity
public import RightSolidActualDensity
public import DensityStrip.Ingham
public import DensityStrip.Strong

/-! Density bounds for the symmetric count of actual zeros with analytic
multiplicity. Each row is stated once; the comparison pieces below just
restrict or weaken those rows. -/
@[expose] public section
noncomputable section
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement
open Montgomery.RationalMoment Montgomery.RationalMoment.RightDetector
open Montgomery.RationalMoment.RightDetector.Physical
namespace LewkoDensityPalomar

/-- Statement notation (not a new count): the advertised bound is a positive
real constant times a power, interpreted in the extended nonnegative reals. -/
macro "CountBound(" s:term "," p:term "," e:term ")" : term =>
  `(∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → zeroCount $s T ≤ ENNReal.ofReal (C*T^($p+$e)))

/-- Native estimates sometimes place the factor `1-σ` in the numerator. -/
macro "from_count " h:term : tactic => `(tactic| (apply estimate_iff.mpr; convert ($h) using 1 <;> ring_nf))

/-- Comparison of two power curves with positive affine denominators. -/
macro "compare_row " h:term : tactic => `(tactic|
 (apply Estimate.weaken ($h)
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  linarith))

macro "restrict_row " h:term : tactic => `(tactic| (intro σ ε hlo hhi he; exact $h (by linarith) (by linarith) he))

theorem provider_P11 : ∀ {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (18/(7*σ+3))*(1-σ), ε) := by
  intro σ ε hl hr he
  have H := DensityStrip.short_density hl hr he
  unfold shortDensityExponent at H
  from_count H

theorem provider_P15 : ∀ {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (12/(9*σ-1))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.adjacent_density_second hl hr he)

theorem provider_P16 : ∀ {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (255/(153*σ+7))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.third_density_segment hl hr he)

theorem provider_P17 : ∀ {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(11*σ-7))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (density_right_solid_first hl hr he)

theorem provider_P18 : ∀ {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (4744/(4870*σ-1283))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (density_right_solid_second hl hr he)

theorem provider_P19 : ∀ {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (6154/(6354*σ-1693))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (density_right_solid_third hl hr he)

theorem provider_P20 : ∀ {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3782/(3936*σ-1065))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (density_right_solid_fourth hl hr he)

theorem provider_P22 : ∀ {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (566/(606*σ-173))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (density_dashed_second hl hr he)

theorem provider_P23 : ∀ {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (31544/(35670*σ-11203))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.later₃ hl hr he)

theorem provider_P24 : ∀ {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (1261710/(1447460*σ-465509))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.later₄ hl hr he)

theorem provider_P25 : ∀ {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3066/(3616*σ-1215))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.later₅ hl hr he)

theorem provider_P26 : ∀ {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (597962/(729216*σ-257415))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.later₆ hl hr he)

theorem provider_P27 : ∀ {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (16504356/(20732766*σ-7623595))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.later₇ hl hr he)

theorem provider_P28 : ∀ {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (2172/(2742*σ-1015))*(1-σ), ε) := by
  intro σ ε hl hr he
  from_count (DensityStrip.later₈ hl hr he)

theorem provider_P21 : ∀ {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (2168/(2282*σ-631))*(1-σ), ε) := by
  intro σ ε hl hr he
  by_cases h : σ ≤ 4/5
  · from_count (density_right_solid_fifth hl h he)
  · from_count (density_dashed_first (by linarith) hr he)

private theorem stronger {s e : ℝ} (hs : 3/4 < s) (he : 0 < e) : Estimate s (3/(2*s)*(1-s)) e := by
  from_count (DensityStrip.strong_density hs he)

private theorem high {s e : ℝ} (hl : 17/19 ≤ s) (hr : s ≤ 1) (he : 0 < e) : Estimate s (3/(10*s-7)*(1-s)) e := by
  apply estimate_iff.mpr
  simpa only [DensityStrip.exponent,DensityStrip.length,one_div,div_eq_mul_inv,one_mul] using DensityStrip.density hl hr he

private theorem lower {s e : ℝ} (hl : 1/2 ≤ s) (hr : s ≤ 9/13) (he : 0 < e) : Estimate s (3/(2-s)*(1-s)) e := by
  from_count (DensityStrip.ingham hl hr he)

theorem provider_P1 : ∀ {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (-3/(σ - 2))*(1-σ), ε) := by
  intro σ ε hl hr he
  change Estimate σ (-3/(σ-2)*(1-σ)) ε
  rw [show σ-2 = -(2-σ) by ring,div_neg,neg_div,neg_neg]
  by_cases h : σ ≤ 9/13
  · exact lower hl h he
  · compare_row (provider_P11 (by linarith) (by linarith) he)

theorem provider_P12 : ∀ {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (9/4)*(1-σ), ε) := by
  intro σ ε hl hr he
  by_cases h : σ ≤ 113/153
  · compare_row (provider_P15 hl h he)
  · compare_row (provider_P16 (by linarith) hr he)

theorem provider_P13 : ∀ {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ < (1 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(2*σ))*(1-σ), ε) := by
  intro σ ε hl hr he
  exact stronger hl he

theorem provider_P9 : ∀ {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(2*σ))*(1-σ), ε) := by
  intro σ ε hl hr he
  exact stronger (by linarith) he

theorem provider_P14 : ∀ {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (6/(8*σ-3))*(1-σ), ε) := by
  intro σ ε hl hr he
  by_cases h : σ ≤ 12/17
  · compare_row (provider_P11 (by linarith) hr he)
  · from_count (DensityStrip.two_term_density_first (by linarith) hr he)

theorem provider_P30 : ∀ {σ ε : ℝ} (hlo : (19/22 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (24/(30*σ-11))*(1-σ), ε) := by
  intro σ ε hl hr he
  by_cases h : σ ≤ 2905/3354
  · compare_row (provider_P27 (by linarith) h he)
  by_cases h' : σ ≤ 7/8
  · compare_row (provider_P28 (by linarith) h' he)
  exact estimate_iff.mpr (DensityStrip.middle_left (by linarith) hr he)

theorem provider_P31 : ∀ {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (6/(σ+3))*(1-σ), ε) := by
  intro σ ε hl hr he
  by_cases h : σ ≤ 17/19
  · exact estimate_iff.mpr (DensityStrip.middle_right hl h he)
  · compare_row (high (by linarith) hr he)

theorem provider_P10 : ∀ {σ ε : ℝ} (hlo : (7/10 : ℝ) < σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(10*σ - 7))*(1-σ), ε) := by
  intro σ ε hl hr he
  by_cases h₁ : σ ≤ 5/7
  · compare_row (provider_P11 (by linarith) h₁ he)
  by_cases h₂ : σ ≤ 3/4
  · compare_row (provider_P12 (by linarith) h₂ he)
  by_cases h₃ : σ ≤ 7/8
  · compare_row (stronger (by linarith) he)
  by_cases h₄ : σ ≤ 23/26
  · compare_row (provider_P30 (by linarith) h₄ he)
  by_cases h₅ : σ ≤ 17/19
  · compare_row (provider_P31 (by linarith) hr he)
  exact high (by linarith) hr he

theorem piece_G2 : ∀ {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (19/25 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (15/(5*σ + 3))*(1-σ), ε) := by
  intro σ ε hl hr he
  by_cases h₁ : σ ≤ 5/7
  · compare_row (provider_P11 (by linarith) h₁ he)
  by_cases h₂ : σ ≤ 113/153
  · compare_row (provider_P15 (by linarith) h₂ he)
  by_cases h₃ : σ ≤ 3/4
  · compare_row (provider_P16 (by linarith) h₃ he)
  compare_row (stronger (by linarith) he)

theorem provider_P2 : ∀ {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ < (19/25 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (15/(5*σ + 3))*(1-σ), ε) := by
  restrict_row piece_G2

theorem provider_P3 : ∀ {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (9/(8*σ - 2))*(1-σ), ε) := by
  intro σ ε hl hr he
  compare_row (stronger (by linarith) he)

theorem provider_P4 : ∀ {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (15/(13*σ - 3))*(1-σ), ε) := by
  intro σ ε hl hr he
  compare_row (stronger (by linarith) he)

theorem piece_G5 : ∀ {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/22 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (6/(5*σ - 1))*(1-σ), ε) := by
  intro σ ε hl hr he
  compare_row (stronger (by linarith) he)

theorem provider_P5 : ∀ {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ < (17/22 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (6/(5*σ - 1))*(1-σ), ε) := by
  restrict_row piece_G5

theorem provider_P6 : ∀ {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (2/(9*σ - 6))*(1-σ), ε) := by
  intro σ ε hl hr he
  compare_row (stronger (by linarith) he)

theorem piece_G7 : ∀ {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (9/(7*σ - 1))*(1-σ), ε) := by
  intro σ ε hl hr he
  compare_row (stronger (by linarith) he)

theorem provider_P7 : ∀ {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ < (7/9 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (9/(7*σ - 1))*(1-σ), ε) := by
  restrict_row piece_G7

theorem provider_P8 : ∀ {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (1867/2347 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (9/(16*σ - 8))*(1-σ), ε) := by
  intro σ ε hl hr he
  compare_row (stronger (by linarith) he)

theorem uniform_P29 : ∀ {ε : ℝ} (hε : 0 < ε),
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  intro ε he
  obtain ⟨C,hC,h⟩ := DensityStrip.later₈ (σ:=(7/8:ℝ)) (by norm_num) le_rfl he
  refine ⟨C,hC,fun σ T hl _ ht => ?_⟩
  rw [zeroCount_eq,← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  apply (Nat.cast_le (α:=ℝ)).mpr (zetaDensityCount_mono hl (le_refl T)) |>.trans
  simpa only [show (2172/(2742*(7/8)-1015)*(1-7/8):ℝ)=1086/5537 by norm_num] using h T ht

theorem provider_P29 : ∀ {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε),
    CountBound(σ, 1086/5537, ε) := by
  intro σ ε hl hr he
  obtain ⟨C,hC,h⟩ := uniform_P29 he
  exact ⟨C,hC,fun T ht => h σ T hl hr ht⟩

theorem uniform_P30 : ∀ {ε : ℝ} (hε : 0 < ε),
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ →
      σ ≤ (23/26 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  intro ε he
  apply uniform_fraction (n:=24) (q:=30) (c:=-11) (by norm_num) he (by norm_num) (by intros; linarith) provider_P30

theorem uniform_P31 : ∀ {ε : ℝ} (hε : 0 < ε),
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  intro ε he
  simpa only [one_mul] using uniform_fraction (q:=1) (c:=3) (n:=6) (by norm_num : (23:ℝ)/26 < 1) he (by norm_num) (by intros; linarith) (by simpa only [one_mul] using @provider_P31)

theorem global39over17 : ∀ {ε : ℝ} (hε : 0 < ε),
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((39/17 : ℝ)*(1-σ)) + ε)) := by
  intro ε he
  suffices h : Closed (1/2) 1 (fun _ => 39/17) by
    simpa only [zero_mul,zero_add] using uniform_fraction (q:=0) (c:=17) (n:=39) (by norm_num : (1:ℝ)/2 < 1) he (by norm_num) (by intros; linarith) (by simpa only [zero_mul,zero_add] using @h)
  intro σ ε hl hr he
  by_cases h₁ : σ ≤ 9/13
  · compare_row (lower hl h₁ he)
  by_cases h₂ : σ ≤ 5/7
  · compare_row (provider_P11 (by linarith) h₂ he)
  by_cases h₃ : σ ≤ 3/4
  · compare_row (provider_P12 (by linarith) h₃ he)
  compare_row (stronger (by linarith) he)

alias piece_G1 := provider_P1

alias piece_G3 := provider_P3

alias piece_G4 := provider_P4

alias piece_G6 := provider_P6

theorem piece_G8 : ∀ {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (23/29 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (9/(16*σ - 8))*(1-σ), ε) := by
  restrict_row provider_P8

theorem piece_G9 : ∀ {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(2*σ))*(1-σ), ε) := by
  restrict_row provider_P9

theorem piece_G10 : ∀ {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(10*σ - 7))*(1-σ), ε) := by
  restrict_row provider_P10

theorem piece_B1 : ∀ {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (-3/(σ - 2))*(1-σ), ε) := by
  restrict_row provider_P1

alias piece_B2 := provider_P11

theorem piece_B3 : ∀ {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (11/15 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (9/4)*(1-σ), ε) := by
  restrict_row provider_P12

theorem piece_B4 : ∀ {σ ε : ℝ} (hlo : (11/15 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (15/(5*σ + 3))*(1-σ), ε) := by
  restrict_row provider_P2

theorem piece_B5 : ∀ {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(2*σ))*(1-σ), ε) := by
  restrict_row provider_P13

alias piece_B6 := piece_G10

alias piece_O1 := piece_B1

theorem piece_O2 : ∀ {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (12/17 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (18/(7*σ+3))*(1-σ), ε) := by
  restrict_row provider_P11

theorem piece_O3 : ∀ {σ ε : ℝ} (hlo : (12/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (6/(8*σ-3))*(1-σ), ε) := by
  restrict_row provider_P14

alias piece_O4 := provider_P15

alias piece_O5 := provider_P16

theorem piece_O6 : ∀ {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(2*σ))*(1-σ), ε) := by
  restrict_row provider_P13

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

theorem piece_O19 : ∀ {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε),
    CountBound(σ, 1086/5537, ε) := by
  restrict_row provider_P29

theorem piece_O20 : ∀ {σ ε : ℝ} (hlo : (24139/27578 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (24/(30*σ-11))*(1-σ), ε) := by
  restrict_row provider_P30

theorem piece_O21 : ∀ {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/19 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (6/(σ+3))*(1-σ), ε) := by
  restrict_row provider_P31

theorem piece_O22 : ∀ {σ ε : ℝ} (hlo : (17/19 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε),
    CountBound(σ, (3/(10*σ - 7))*(1-σ), ε) := by
  restrict_row provider_P10

end LewkoDensityPalomar
