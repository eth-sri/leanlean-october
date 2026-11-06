module
public import CountCore
public import AdjacentZeroDensity
public import DashedInitialActualDensity
public import GuthMaynard.Improvement.GlobalDensity
public import GuthMaynard.Improvement.WeakShortDensity
public import LaterPairs.NativeSharpRow6
public import LaterPairs.NativeSharpRows78
public import MathCollab.Density.Stronger.NativeDensity
public import MonotoneCurve.ActualDensity
public import RightSolidActualDensity
public import ThirdZeroDensity
public import TraceAlternatives.NativeCubeRows34
public import TraceAlternatives.NativeUniversalRows45
public import TwoTermZeroDensity
public import WrittenDensity.Uniform


@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open MathCollab.Density
open scoped BigOperators ENNReal
namespace LewkoDensityPalomar

/-- The common full-count conclusion, with the height-independent constant first. -/
abbrev Bound (σ p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    zeroCount σ T ≤ ENNReal.ofReal (C * T ^ p)

/-- The analogous conclusion with a single constant for the entire closed strip. -/
abbrev UniformBound (a b : ℝ) (p : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, a ≤ σ → σ ≤ b → 2 ≤ T →
    zeroCount σ T ≤ ENNReal.ofReal (C * T ^ p σ)

private theorem count_eq (σ T : ℝ) :
    zeroCount σ T = (zetaDensityCount σ T : ℝ≥0∞) := by
  apply zeroCount_eq_finset σ T (zetaZeroFinset σ (-T) T)
  intro ρ
  simp only [mem_zetaDensityFinset, IsNontrivialZetaZero, and_assoc]

private theorem count_le {σ T B : ℝ} (h : (zetaDensityCount σ T : ℝ) ≤ B) :
    zeroCount σ T ≤ ENNReal.ofReal B := by
  rw [count_eq, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h

private theorem transfer {σ p : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ p) : Bound σ p := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun T hT => count_le (h T hT)⟩

private theorem uniform_transfer {a b : ℝ} {p : ℝ → ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, a ≤ σ → σ ≤ b → 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ p σ) : UniformBound a b p := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun σ T hlo hhi hT => count_le (h σ T hlo hhi hT)⟩

private theorem weaken {σ p q : ℝ} (h : Bound σ p) (hpq : p ≤ q) : Bound σ q := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,fun T hT => (h T hT).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) hpq) hC.le)

private theorem fraction_transfer {σ ε a b c d : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(a*(1-σ)/b+ε))
    (hσ : σ ≤ 1) (hb : 0 < b) (hd : 0 < d) (hcmp : a*d ≤ c*b) :
    Bound σ ((c/d)*(1-σ)+ε) := by
  apply weaken (transfer h)
  have hc : a/b ≤ c/d := (div_le_div_iff₀ hb hd).mpr hcmp
  convert add_le_add_right (mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hσ)) ε using 1 <;> ring

private theorem mono_sigma {σ τ p : ℝ} (hστ : σ ≤ τ) (h : Bound σ p) : Bound τ p := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,fun T hT => le_trans ?_ (h T hT)⟩
  rw [count_eq, count_eq]
  exact_mod_cast zetaDensityCount_mono hστ (le_refl T)

private theorem normalize {σ ε a b : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(a*(1-σ)/b+ε)) :
    Bound σ ((a/b)*(1-σ)+ε) := by
  convert transfer h using 1 <;> ring_nf

theorem provider_P1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  have he : -3/(σ-2) = 3/(2-σ) := by
    rw [show σ-2 = -(2-σ) by ring, div_neg]
    ring
  rw [he]
  by_cases h : σ ≤ (9/13 : ℝ)
  · apply fraction_transfer (GuthMaynard.Improvement.ingham_lower_density σ hlo h ε hε)
      (by linarith) <;> nlinarith
  · apply fraction_transfer (GuthMaynard.Improvement.short_density (by linarith) (by linarith) hε)
      (by linarith) <;> nlinarith


theorem provider_P2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ < (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  by_cases h : σ ≤ (5/7 : ℝ)
  · apply fraction_transfer (GuthMaynard.Improvement.short_density (by linarith) h hε)
      (by linarith) <;> nlinarith
  by_cases h' : σ ≤ (113/153 : ℝ)
  · apply fraction_transfer (Montgomery.RationalMoment.adjacent_density_second (by linarith) h' hε)
      (by linarith) <;> nlinarith
  by_cases h'' : σ ≤ (3/4 : ℝ)
  · apply fraction_transfer (Montgomery.RationalMoment.third_density_segment (by linarith) h'' hε)
      (by linarith) <;> nlinarith
  · apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
      (by linarith) <;> nlinarith


theorem provider_P3 {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) := by
  apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
    (by linarith) <;> nlinarith


theorem provider_P4 {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) := by
  apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
    (by linarith) <;> nlinarith


theorem provider_P5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ < (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) := by
  apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
    (by linarith) <;> nlinarith


theorem provider_P6 {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) := by
  apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
    (by linarith) <;> nlinarith


theorem provider_P7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ < (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) := by
  apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
    (by linarith) <;> nlinarith


theorem provider_P8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (1867/2347 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
    (by linarith) <;> nlinarith


theorem provider_P9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) hε)
    (by linarith) <;> nlinarith


theorem provider_P10 {σ ε : ℝ} (hlo : (7/10 : ℝ) < σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  by_cases hz : (7/8 : ℝ) < σ
  · apply transfer
    exact Montgomery.WrittenDensity.density_of_actual_zero hz
  by_cases h : (3/4 : ℝ) < σ
  · apply fraction_transfer (MathCollab.Density.Stronger.stronger_density_bound_native h hε)
      (by linarith) <;> nlinarith
  · have hb := provider_P1 (σ := (1/2 : ℝ)) (by norm_num) (by norm_num) hε
    norm_num at hb
    apply weaken (mono_sigma (by linarith) hb)
    rw [div_mul_eq_mul_div]
    suffices 1 ≤ 3 * (1 - σ) / (10 * σ - 7) by linarith
    apply (le_div_iff₀ (by linarith : 0 < 10*σ-7)).mpr
    nlinarith


theorem provider_P11 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact normalize (GuthMaynard.Improvement.short_density hlo hhi hε)

theorem provider_P12 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  apply fraction_transfer (Montgomery.Refined.refined_density_middle (by linarith) hhi hε)
    (by linarith) <;> nlinarith

theorem provider_P13 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ < (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact normalize (MathCollab.Density.Stronger.stronger_density_bound_native hlo hε)

theorem provider_P14 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  by_cases h : σ ≤ (12/17 : ℝ)
  · apply fraction_transfer (GuthMaynard.Improvement.short_density (by linarith) (by linarith) hε)
      (by linarith) <;> nlinarith
  · exact normalize (Montgomery.RationalMoment.two_term_density_first (by linarith) hhi hε)

theorem provider_P15 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.adjacent_density_second hlo hhi hε)

theorem provider_P16 {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.third_density_segment hlo hhi hε)

theorem provider_P17 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.density_right_solid_first hlo hhi hε)

theorem provider_P18 {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.density_right_solid_second hlo hhi hε)

theorem provider_P19 {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.density_right_solid_third hlo hhi hε)

theorem provider_P20 {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth hlo hhi hε)

theorem provider_P21 {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) := by
  by_cases h : σ ≤ (4/5 : ℝ)
  · exact normalize (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth hlo h hε)
  · exact normalize (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) hhi hε)

theorem provider_P22 {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.density_dashed_second hlo hhi hε)

theorem provider_P23 {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 hlo hhi hε)

theorem provider_P24 {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 hlo hhi hε)

theorem provider_P25 {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 hlo hhi hε)

theorem provider_P26 {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 hlo hhi hε)

theorem provider_P27 {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 hlo hhi hε)

theorem provider_P28 {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) := by
  exact normalize (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 hlo hhi hε)

theorem provider_P29 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  apply transfer
  obtain ⟨C,hC,h⟩ := Montgomery.MonotoneCurve.seven_eighths_right_uniform hε
  exact ⟨C,hC,fun T hT => h σ hlo T hT⟩

theorem provider_P30 {σ ε : ℝ} (hlo : (19/22 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  convert transfer (Montgomery.WrittenDensity.source_oct2_mixed_4 hlo hhi hε) using 1 <;> ring_nf

theorem provider_P31 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  exact transfer (Montgomery.WrittenDensity.density_of_actual_zero (by linarith))

alias piece_G1 := provider_P1

theorem piece_G2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  by_cases hend : σ = (19/25 : ℝ)
  · subst σ
    convert (provider_P3 (σ := (19/25 : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact provider_P2 (by linarith) (lt_of_le_of_ne hhi hend) hε

alias piece_G3 := provider_P3

alias piece_G4 := provider_P4

theorem piece_G5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) := by
  by_cases hend : σ = (17/22 : ℝ)
  · subst σ
    convert (provider_P6 (σ := (17/22 : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact provider_P5 (by linarith) (lt_of_le_of_ne hhi hend) hε

alias piece_G6 := provider_P6

theorem piece_G7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) := by
  by_cases hend : σ = (7/9 : ℝ)
  · subst σ
    convert (provider_P8 (σ := (7/9 : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact provider_P7 (by linarith) (lt_of_le_of_ne hhi hend) hε

theorem piece_G8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (23/29 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  exact provider_P8 hlo (by linarith) hε

theorem piece_G9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact provider_P9 hlo (by linarith) hε

theorem piece_G10 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact provider_P10 (by linarith) hhi hε

theorem piece_B1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact provider_P1 hlo (by linarith) hε

alias piece_B2 := provider_P11

theorem piece_B3 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (11/15 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  exact provider_P12 hlo (by linarith) hε

theorem piece_B4 {σ ε : ℝ} (hlo : (11/15 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  exact provider_P2 (by linarith) (by linarith) hε

theorem piece_B5 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact provider_P13 hlo (by linarith) hε

alias piece_B6 := piece_G10

alias piece_O1 := piece_B1

theorem piece_O2 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (12/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact provider_P11 hlo (by linarith) hε

theorem piece_O3 {σ ε : ℝ} (hlo : (12/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  exact provider_P14 (by linarith) hhi hε

alias piece_O4 := provider_P15

alias piece_O5 := provider_P16

theorem piece_O6 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact provider_P13 hlo (by linarith) hε

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

theorem piece_O19 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  exact provider_P29 hlo (by linarith) hε

theorem piece_O20 {σ ε : ℝ} (hlo : (24139/27578 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  exact provider_P30 (by linarith) hhi hε

theorem piece_O21 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/19 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  exact provider_P31 hlo (by linarith) hε

theorem piece_O22 {σ ε : ℝ} (hlo : (17/19 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact provider_P10 (by linarith) hhi hε

theorem global39over17 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((39/17 : ℝ)*(1-σ)) + ε)) := by
  exact uniform_transfer (GuthMaynard.Improvement.global_density_uniform hε)

theorem uniform_P29 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  apply uniform_transfer
  obtain ⟨C,hC,h⟩ := Montgomery.MonotoneCurve.seven_eighths_right_uniform hε
  refine ⟨C,hC,?_⟩
  intro σ T hlo hhi hT
  exact h σ hlo T hT

theorem uniform_P30 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ →
      σ ≤ (23/26 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  apply uniform_transfer
  obtain ⟨C,hC,h⟩ := Montgomery.WrittenDensity.uniform_source_oct2_mixed_4 hε
  refine ⟨C,hC,?_⟩
  intro σ T hlo hhi hT
  convert (h σ T hlo hhi hT) using 1
  all_goals ring_nf

theorem uniform_P31 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  refine ⟨1, by norm_num, fun σ T hlo hhi hT => ?_⟩
  rw [count_eq, Montgomery.ZeroFreeHatching.actual_density_count_zero (by linarith)]
  simp

end LewkoDensityPalomar
