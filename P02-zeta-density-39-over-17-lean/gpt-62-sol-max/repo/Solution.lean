module

public import CountCore
public import AdjacentZeroDensity
public import DashedInitialActualDensity
public import GuthMaynard.Improvement.CurveUniformization
public import GuthMaynard.Improvement.NativeIngham
public import GuthMaynard.Improvement.WeakShortDensity
public import LaterPairs.NativeSharpRows78
public import MathCollab.Density.Stronger.NativeDensity
public import RightSolidActualDensity
public import ThirdZeroDensity
public import TraceAlternatives.NativeCubeRows34
public import TraceAlternatives.NativeUniversalRows45
public import TwoTermZeroDensity
public import ZeroFreeDensityBridge

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace LewkoDensityPalomar
open MathCollab.Density GuthMaynard.Improvement Montgomery.RationalMoment
open Montgomery.RationalMoment.RightDetector Montgomery.RationalMoment.RightDetector.Physical

/-- A pointwise power bound; the exponent includes the epsilon loss. -/
abbrev Bound (σ p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → zeroCount σ T ≤ ENNReal.ofReal (C * T^p)

/-- A power bound with one constant for the whole closed interval of cutoffs. -/
abbrev UniformBound (a b : ℝ) (p : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, a ≤ σ → σ ≤ b → 2 ≤ T →
    zeroCount σ T ≤ ENNReal.ofReal (C * T^(p σ))

private abbrev FiniteBound (σ p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T : ℝ) ≤ C * T^p

private theorem count_le_iff {σ T X : ℝ} (hX : 0 ≤ X) :
    zeroCount σ T ≤ ENNReal.ofReal X ↔ (zetaDensityCount σ T : ℝ) ≤ X := by
  rw [zeroCount_eq_density, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff hX]

private theorem bound_iff {σ p : ℝ} : Bound σ p ↔ FiniteBound σ p := by
  constructor <;> rintro ⟨C, hC, h⟩ <;> refine ⟨C, hC, fun T hT => ?_⟩
  · exact (count_le_iff (by positivity)).mp (h T hT)
  · exact (count_le_iff (by positivity)).mpr (h T hT)

private theorem of_finite {σ p : ℝ} : FiniteBound σ p → Bound σ p := bound_iff.mpr

private theorem uniformize {a b K ε : ℝ} {p : ℝ → ℝ}
    (hab : a < b) (hK : 0 < K)
    (hmod : ∀ x y, a ≤ x → x ≤ y → y ≤ b → p x ≤ p y + K * (y-x))
    (h : ∀ σ, a ≤ σ → σ ≤ b → ∀ η, 0 < η → Bound σ (p σ + η)) (hε : 0 < ε) :
    UniformBound a b (fun σ => p σ + ε) := by
  obtain ⟨C, hC, hC'⟩ := density_curve_uniform_on_interval hab hK hmod
    (fun σ hlo hhi η hη => bound_iff.mp (h σ hlo hhi η hη)) hε
  exact ⟨C, hC, fun σ T hlo hhi hT => (count_le_iff (by positivity)).mpr (hC' σ T hlo hhi hT)⟩

private theorem pointwise {a b σ : ℝ} {p : ℝ → ℝ}
    (h : UniformBound a b p) (hlo : a ≤ σ) (hhi : σ ≤ b) : Bound σ (p σ) := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun T => h σ T hlo hhi⟩

private theorem weaken {σ p q : ℝ} (h : Bound σ p) (hpq : p ≤ q) : Bound σ q := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun T hT => (h T hT).trans <| ENNReal.ofReal_le_ofReal <|
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hpq) hC.le⟩

private theorem weaken_coeff {σ ε A B : ℝ} (hσ : σ ≤ 1)
    (h : Bound σ (A * (1-σ) + ε)) (hAB : A ≤ B) : Bound σ (B * (1-σ) + ε) :=
  weaken h (add_le_add (mul_le_mul_of_nonneg_right hAB (sub_nonneg.mpr hσ)) le_rfl)

private theorem count_zero {σ : ℝ} (hσ : 7/8 < σ) (T : ℝ) : zeroCount σ T = 0 := by
  rw [zeroCount_eq_density, Montgomery.ZeroFreeHatching.actual_density_count_zero hσ, Nat.cast_zero]

private theorem zero_free_bound {σ p : ℝ} (hσ : 7/8 < σ) : Bound σ p :=
  ⟨1, by norm_num, fun T _ => by simp [count_zero hσ T]⟩

/- The native bounds. All comparisons below reuse these at the same cutoff. -/

theorem provider_P11 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  apply of_finite
  convert (short_density hlo hhi hε) using 1 <;> ring_nf

private theorem stronger {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    Bound σ ((3/(2*σ)) * (1-σ) + ε) := by
  apply of_finite
  convert (Stronger.stronger_density_bound_native hσ hε) using 1 <;> ring_nf

theorem provider_P13 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ < (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  stronger hlo hε

theorem provider_P14 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  by_cases h : σ ≤ 12/17
  · apply weaken_coeff (by linarith) (provider_P11 (by linarith) hhi hε)
    exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)
  · apply of_finite
    convert (two_term_density_first (le_of_not_ge h) hhi hε) using 1 <;> ring_nf

theorem provider_P15 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) := by
  apply of_finite
  convert (adjacent_density_second hlo hhi hε) using 1 <;> ring_nf

theorem provider_P16 {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) := by
  apply of_finite
  convert (third_density_segment hlo hhi hε) using 1 <;> ring_nf

theorem provider_P17 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_right_solid_first hlo hhi hε) using 1 <;> ring_nf

theorem provider_P18 {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_right_solid_second hlo hhi hε) using 1 <;> ring_nf

theorem provider_P19 {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_right_solid_third hlo hhi hε) using 1 <;> ring_nf

theorem provider_P20 {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_right_solid_fourth hlo hhi hε) using 1 <;> ring_nf

theorem provider_P21 {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) := by
  apply of_finite
  by_cases h : σ ≤ 4/5
  · convert (density_right_solid_fifth hlo h hε) using 1 <;> ring_nf
  · convert (density_dashed_first (le_of_not_ge h) hhi hε) using 1 <;> ring_nf

theorem provider_P22 {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_dashed_second hlo hhi hε) using 1 <;> ring_nf

theorem provider_P23 {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_cube_row3 hlo hhi hε) using 1 <;> ring_nf

theorem provider_P24 {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_universal_row4 hlo hhi hε) using 1 <;> ring_nf

theorem provider_P25 {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_universal_row5 hlo hhi hε) using 1 <;> ring_nf

theorem provider_P26 {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_sharp_row6 hlo hhi hε) using 1 <;> ring_nf

theorem provider_P27 {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_sharp_row7 hlo hhi hε) using 1 <;> ring_nf

theorem provider_P28 {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) := by
  apply of_finite
  convert (density_sharp_row8 hlo hhi hε) using 1 <;> ring_nf

theorem uniform_P29 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  obtain ⟨C, hC, h⟩ := provider_P28 (σ := 7/8) (by norm_num) le_rfl hε
  norm_num at h
  refine ⟨C, hC, fun σ T hlo _ hT => ?_⟩
  apply le_trans _ (h T hT)
  simp only [zeroCount_eq_density]
  exact_mod_cast zetaDensityCount_mono hlo (le_refl T)

theorem provider_P29 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) :=
  pointwise (uniform_P29 hε) hlo hhi

private theorem bound30 {σ ε : ℝ} (hlo : 19/22 ≤ σ) (hhi : σ ≤ 23/26) (hε : 0 < ε) :
    Bound σ ((24/(30*σ-11)) * (1-σ) + ε) := by
  by_cases hz : 7/8 < σ
  · exact zero_free_bound hz
  by_cases h : σ ≤ 2905/3354
  · apply weaken_coeff (by linarith) (provider_P27 (by linarith) h hε)
    exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)
  · apply weaken_coeff (by linarith) (provider_P28 (le_of_not_ge h) (le_of_not_gt hz) hε)
    exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem uniform_P30 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ →
      σ ≤ (23/26 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  apply uniformize (K := 456) (by norm_num) (by norm_num) _
    (fun _ hlo hhi _ hη => bound30 hlo hhi hη) hε
  intro x y hx hxy hy
  have hd : 0 < 30*x-11 := by linarith
  have he : 0 < 30*y-11 := by linarith
  apply sub_le_iff_le_add'.mp
  calc
    _ = 456 * (y-x) / ((30*x-11)*(30*y-11)) := by field_simp; ring
    _ ≤ 456 * (y-x) := div_le_self (by positivity)
      (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith))

theorem provider_P30 {σ ε : ℝ} (hlo : (19/22 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) :=
  bound30 hlo hhi hε

theorem uniform_P31 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) :=
  ⟨1, by norm_num, fun σ T hlo _ _ => by simp [count_zero (by linarith : 7/8 < σ) T]⟩

theorem provider_P31 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) :=
  pointwise (uniform_P31 hε) hlo hhi

/- The older curves follow by comparing coefficients of the nonnegative factor 1-σ. -/
private theorem ingham {σ ε : ℝ} (hlo : 1/2 ≤ σ) (hhi : σ ≤ 9/13) (hε : 0 < ε) :
    Bound σ ((-3/(σ-2)) * (1-σ) + ε) := by
  rw [← neg_sub (2 : ℝ) σ, neg_div_neg_eq, div_mul_eq_mul_div]
  exact of_finite (ingham_lower_density σ hlo hhi ε hε)

theorem provider_P1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  by_cases h : σ ≤ 9/13
  · exact ingham hlo h hε
  apply weaken_coeff (by linarith) (provider_P11 (le_of_not_ge h) (by linarith) hε)
  rw [← neg_sub (2 : ℝ) σ, neg_div_neg_eq]
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem piece_G2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  by_cases h₁ : σ ≤ 5/7
  · apply weaken_coeff (by linarith) (provider_P11 (by linarith) h₁ hε)
    exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)
  by_cases h₂ : σ ≤ 113/153
  · apply weaken_coeff (by linarith) (provider_P15 (le_of_not_ge h₁) h₂ hε)
    exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)
  by_cases h₃ : σ ≤ 3/4
  · apply weaken_coeff (by linarith) (provider_P16 (le_of_not_ge h₂) h₃ hε)
    exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)
  apply weaken_coeff (by linarith) (stronger (lt_of_not_ge h₃) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem provider_P2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ < (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) :=
  piece_G2 hlo hhi.le hε

theorem provider_P3 {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) := by
  apply weaken_coeff (by linarith) (stronger (by linarith) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem provider_P4 {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) := by
  apply weaken_coeff (by linarith) (stronger (by linarith) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem provider_P6 {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) := by
  apply weaken_coeff (by linarith) (stronger (by linarith) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem provider_P8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (1867/2347 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  apply weaken_coeff (by linarith) (stronger (by linarith) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem piece_G5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) := by
  apply weaken_coeff (by linarith) (stronger (by linarith) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem provider_P5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ < (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) :=
  piece_G5 hlo hhi.le hε

theorem piece_G7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) := by
  apply weaken_coeff (by linarith) (stronger (by linarith) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

theorem provider_P7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ < (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) :=
  piece_G7 hlo hhi.le hε

theorem provider_P9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  stronger (by linarith) hε

theorem provider_P12 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  by_cases h : σ ≤ 113/153
  · apply weaken_coeff (by linarith) (provider_P15 hlo h hε)
    exact (div_le_iff₀ (by linarith)).2 (by linarith)
  · apply weaken_coeff (by linarith) (provider_P16 (le_of_not_ge h) hhi hε)
    exact (div_le_iff₀ (by linarith)).2 (by linarith)

theorem global39over17 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((39/17 : ℝ)*(1-σ)) + ε)) := by
  apply uniformize (p := fun σ => (39/17)*(1-σ)) (K := 39/17)
    (by norm_num) (by norm_num) (by intros; ring_nf; rfl) _ hε
  intro σ hlo hhi ε hε
  by_cases h₁ : σ ≤ 9/13
  · apply weaken_coeff hhi (ingham hlo h₁ hε)
    rw [← neg_sub (2 : ℝ) σ, neg_div_neg_eq]
    exact (div_le_iff₀ (by linarith)).2 (by linarith)
  by_cases h₂ : σ ≤ 5/7
  · apply weaken_coeff hhi (provider_P11 (le_of_not_ge h₁) h₂ hε)
    exact (div_le_iff₀ (by linarith)).2 (by linarith)
  by_cases h₃ : σ ≤ 3/4
  · exact weaken_coeff hhi (provider_P12 (le_of_not_ge h₂) h₃ hε) (by norm_num)
  apply weaken_coeff hhi (stronger (lt_of_not_ge h₃) hε)
  exact (div_le_iff₀ (by linarith)).2 (by linarith)

theorem provider_P10 {σ ε : ℝ} (hlo : (7/10 : ℝ) < σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  by_cases h : σ ≤ 3/4
  · have hb : Bound σ ((39/17)*(1-σ)+ε) :=
      pointwise (global39over17 hε) (by linarith) hhi
    apply weaken_coeff hhi hb
    exact (le_div_iff₀ (by linarith)).2 (by linarith)
  by_cases hz : 7/8 < σ
  · exact zero_free_bound hz
  apply weaken_coeff hhi (stronger (lt_of_not_ge h) hε)
  exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)

/- Plotted intervals, restricted from the corresponding bounds. -/

theorem piece_G1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) :=
  provider_P1 hlo hhi hε

theorem piece_G3 {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) :=
  provider_P3 hlo hhi hε

theorem piece_G4 {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) :=
  provider_P4 hlo hhi hε

theorem piece_G6 {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) :=
  provider_P6 hlo hhi hε

theorem piece_G8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (23/29 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) :=
  provider_P8 hlo (by linarith) hε

theorem piece_G9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  provider_P9 hlo (by linarith) hε

theorem piece_G10 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) :=
  provider_P10 (by linarith) hhi hε

theorem piece_B1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) :=
  provider_P1 hlo (by linarith) hε

theorem piece_B2 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) :=
  provider_P11 hlo hhi hε

theorem piece_B3 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (11/15 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) :=
  provider_P12 hlo (by linarith) hε

theorem piece_B4 {σ ε : ℝ} (hlo : (11/15 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) :=
  piece_G2 (by linarith) (by linarith) hε

theorem piece_B5 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  provider_P13 hlo (by linarith) hε

theorem piece_B6 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) :=
  provider_P10 (by linarith) hhi hε

theorem piece_O1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) :=
  provider_P1 hlo (by linarith) hε

theorem piece_O2 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (12/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) :=
  provider_P11 hlo (by linarith) hε

theorem piece_O3 {σ ε : ℝ} (hlo : (12/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) :=
  provider_P14 (by linarith) hhi hε

theorem piece_O4 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) :=
  provider_P15 hlo hhi hε

theorem piece_O5 {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) :=
  provider_P16 hlo hhi hε

theorem piece_O6 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) :=
  provider_P13 hlo (by linarith) hε

theorem piece_O7 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) :=
  provider_P17 hlo hhi hε

theorem piece_O8 {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) :=
  provider_P18 hlo hhi hε

theorem piece_O9 {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) :=
  provider_P19 hlo hhi hε

theorem piece_O10 {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) :=
  provider_P20 hlo hhi hε

theorem piece_O11 {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) :=
  provider_P21 hlo hhi hε

theorem piece_O12 {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) :=
  provider_P22 hlo hhi hε

theorem piece_O13 {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) :=
  provider_P23 hlo hhi hε

theorem piece_O14 {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) :=
  provider_P24 hlo hhi hε

theorem piece_O15 {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) :=
  provider_P25 hlo hhi hε

theorem piece_O16 {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) :=
  provider_P26 hlo hhi hε

theorem piece_O17 {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) :=
  provider_P27 hlo hhi hε

theorem piece_O18 {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) :=
  provider_P28 hlo hhi hε

theorem piece_O19 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) :=
  provider_P29 hlo (by linarith) hε

theorem piece_O20 {σ ε : ℝ} (hlo : (24139/27578 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) :=
  provider_P30 (by linarith) hhi hε

theorem piece_O21 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/19 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) :=
  provider_P31 hlo (by linarith) hε

theorem piece_O22 {σ ε : ℝ} (hlo : (17/19 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) :=
  provider_P10 (by linarith) hhi hε

end LewkoDensityPalomar
