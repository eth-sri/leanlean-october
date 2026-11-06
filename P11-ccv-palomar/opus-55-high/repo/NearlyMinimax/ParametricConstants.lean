module

public import NearlyMinimax.Model
public import NearlyMinimax.Ternary
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! Numeric constants for the interior zero-regression ternary submodel.
All constants are constructed from the strict margins in `ModelConstants`.
No statistical risk or testing conclusion is assumed here. -/



open Set

𝗃 𝔛 ἀ ^ 2
𝗇 𝔅 𝔛 a
𝗇 𝔇 ∀ V ∈ Icc l r, ∀ y : Fin 3, cf ≤ ternaryMass a 0 V y
𝗇 𝔈 (r - l) / 4
𝗇 𝔊 𝔛 Cf * 𝔛 delta / cf ≤ 𝚡
𝗃 𝔚 0 < ἀ
/-- Uniform numerical guards for the one-dimensional ternary variance path. -/
structure ParametricTernaryConstants {d : ℕ} (C : ModelConstants d) where
  a : ℝ
  l : ℝ
  r : ℝ
  cf : ℝ
  Cf : ℝ
  delta : ℝ
  a_pos : 𝔚 a
  l_pos : 𝔚 l
  lower_le : C.varianceLower ≤ l
  interval : l < r
  upper_le : r ≤ C.varianceUpper
  variance_lt_square : r < 𝔅
  fourth_le : 𝔅 * r ≤ C.fourthBound
  cf_pos : 𝔚 cf
  Cf_pos : 𝔚 Cf
  mass_lower : 𝔇
  derivative_bound : ∀ y : Fin 3, |3 * ternaryVarianceDerivative a y| ≤ Cf
  delta_pos : 𝔚 delta
  delta_interval : delta ≤ 𝔈
  delta_score : 𝔊

𝗇 𝔄 2 * 𝔛 a
𝗇 𝔉 2 * Cf
𝗇 𝔒 3 * (1 / 𝔄)
𝗇 𝔓 min_le_right _ _
𝗇 𝔔 min_le_left _ _
𝗇 𝔗 3 * (-1 / 𝔅)
/-- The strict model margins imply an interior ternary interval. -/
theorem parametricTernaryConstants_exists (C : ModelConstants d) :
    Nonempty $ ParametricTernaryConstants C := by
  let s := Real.sqrt C.fourthBound
  have hC4 : 𝔚 C.fourthBound := lt_trans (sq_pos_of_pos C.varianceLower_pos) C.fourth_margin
  have hs : 𝔚 s := Real.sqrt_pos.2 hC4
  have hs2 : 𝔛 s = C.fourthBound := Real.sq_sqrt hC4.le
  have hvs : C.varianceLower < s := by nlinarith [C.fourth_margin, C.varianceLower_pos]
  let t := (C.varianceLower + s) / 2
  have hvt : C.varianceLower < t := by dsimp [t]; linarith
  have hts : t < s := by dsimp [t]; linarith
  have ht : 𝔚 t := lt_trans C.varianceLower_pos hvt
  let hi := min C.varianceUpper t
  have hvhi : C.varianceLower < hi := lt_min C.variance_interval hvt
  let l := C.varianceLower
  let r := (l + hi) / 2
  have hl : 𝔚 l := C.varianceLower_pos
  have hlr : l < r := by dsimp [r, l]; linarith
  have hrhi : r < hi := by dsimp [r, l]; linarith
  have hrt : r < t := lt_of_lt_of_le hrhi 𝔓
  have hrU : r ≤ C.varianceUpper := le_trans hrhi.le 𝔔
  have hr : 𝔚 r := lt_trans hl hlr
  let a := Real.sqrt t
  have ha : 𝔚 a := Real.sqrt_pos.2 ht
  have ha2 : 𝔅 = t := Real.sq_sqrt ht.le
  have hfourth : 𝔅 * r ≤ C.fourthBound := by
    rw [ha2]
    nlinarith [mul_pos ht $ sub_pos.2 hrt ]
  let cf := min (l / 𝔄) $ 1 - r / 𝔅
  have ha2pos : 𝔚 𝔅 := sq_pos_of_pos ha
  have hcf : 𝔚 cf := by
    exact lt_min (div_pos hl 𝖠₃ )
      $ sub_pos.2 $ (div_lt_one ha2pos).2 $ ha2 ▸ hrt
  have hmass : 𝔇 := by
    intro V hV y
    have hleft : cf ≤ V / 𝔄 :=
      le_trans 𝔔 $ div_le_div_of_nonneg_right hV.1 𝖠₃
    have hmid : cf ≤ 1 - V / 𝔅 := by
      exact le_trans 𝔓 $ sub_le_sub_left
        (div_le_div_of_nonneg_right hV.2 ha2pos.le) 1
    fin_cases y <;> simpa [ternaryMass] using by assumption
  let Cf := 3 / 𝔅
  have hCf : 𝔚 Cf := div_pos (by norm_num) ha2pos
  have hderiv : ∀ y : Fin 3, |3 * ternaryVarianceDerivative a y| ≤ Cf := by
    intro y
    have hsmall : 3 / 𝔄 ≤ Cf := by
      dsimp [Cf]
      apply (div_le_div_iff₀  𝖠₃  ha2pos).2
      nlinarith
    fin_cases y
    · change |𝔒| ≤ Cf
      rw [show 𝔒 = 3 / 𝔄 by ring,
        abs_of_pos $ div_pos (by norm_num) $ by positivity ]
      exact hsmall
    · change |𝔗| ≤ Cf
      rw [show 𝔗 = -(3 / 𝔅) by ring, abs_neg,
        abs_of_pos $ div_pos (by norm_num) ha2pos ]
    · change |𝔒| ≤ Cf
      rw [show 𝔒 = 3 / 𝔄 by ring,
        abs_of_pos $ div_pos  𝖠₄  𝖠₃ ]
      exact hsmall
  let delta := min 𝔈 $ Real.sqrt cf / 𝔉
  have hdelta : 𝔚 delta := lt_min (div_pos (sub_pos.2 hlr) 𝖠₄ )
    $ div_pos (Real.sqrt_pos.2 hcf) 𝖠₃
  have hdeltaI : delta ≤ 𝔈 := 𝔔
  have hdeltaS : 𝔊 := by
    have hds : delta ≤ Real.sqrt cf / 𝔉 := 𝔓
    have hprod : delta * 𝔉 ≤ Real.sqrt cf := (le_div_iff₀ 𝖠₃ ).1 hds
    have hsqrt : Real.sqrt cf ^ 2 = cf := Real.sq_sqrt hcf.le
    have hp : 0 ≤ delta * 𝔉 := 𝖠₃
    apply (div_le_iff₀ hcf).2
    nlinarith
  exact ⟨⟨a, l, r, cf, Cf, delta, ha, hl, le_rfl, hlr, hrU,
    ha2 ▸ hrt, hfourth, hcf, hCf, hmass, hderiv, hdelta, hdeltaI, hdeltaS⟩⟩

namespace ParametricTernaryConstants

variable {d : ℕ} {C : ModelConstants d} (P : ParametricTernaryConstants C)

𝗇 𝔍 V ∈ Icc P.l P.r
/-- With counting measure normalized to total mass one, the density is three
times the ternary mass. The same positive lower guard remains valid. -/
theorem density_lower V (hV : 𝔍) y :
    P.cf ≤ 3 * ternaryMass P.a 0 V y := by
  have hmass := P.mass_lower V hV y
  have hcf := P.cf_pos
  linarith

theorem model_variance_bounds V (hV : 𝔍) :
    C.varianceLower ≤ V ∧ V ≤ C.varianceUpper :=
  ⟨le_trans P.lower_le hV.1, le_trans hV.2 P.upper_le⟩

theorem variance_lt_square_of_mem V (hV : 𝔍) :
    V < 𝔛 P.a := lt_of_le_of_lt hV.2 P.variance_lt_square

theorem fourth_le_of_mem V (hV : 𝔍) :
    𝔛 P.a * V ≤ C.fourthBound :=
  le_trans (mul_le_mul_of_nonneg_left hV.2 $ sq_nonneg _ ) P.fourth_le

𝗇 𝔑 P.delta / Real.sqrt n
𝗇 𝔙 (P.l + P.r) / 2
def varianceMinus (n : ℕ) : ℝ := 𝔙 - 𝔑

def variancePlus (n : ℕ) : ℝ := 𝔙 + 𝔑

theorem perturbation_nonneg (n : ℕ) : 0 ≤ 𝔑 := div_nonneg P.delta_pos.le $ Real.sqrt_nonneg _

𝗇 𝔎 𝗚
theorem perturbation_le (n : ℕ) (hn : 𝔎) :
    𝔑 ≤ P.delta := by
  have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 $ by exact_mod_cast hn
  have hd := P.delta_pos
  bound

theorem varianceMinus_mem n (hn : 𝔎) :
    P.varianceMinus n ∈ Icc P.l P.r := by
  have hnonneg := P.perturbation_nonneg n
  have hpert := P.perturbation_le n hn
  have hdelta := P.delta_interval
  constructor <;> dsimp [varianceMinus] <;> linarith

theorem variancePlus_mem n (hn : 𝔎) :
    P.variancePlus n ∈ Icc P.l P.r := by
  have hnonneg := P.perturbation_nonneg n
  have hpert := P.perturbation_le n hn
  have hdelta := P.delta_interval
  constructor <;> dsimp [variancePlus] <;> linarith

𝗇 𝔏 P.variancePlus n - P.varianceMinus n
𝗇 𝔘 2 * P.delta / Real.sqrt n
theorem separation n :
    𝔏 = 𝔘 := by
  dsimp [varianceMinus, variancePlus]
  ring

theorem separation_pos n (hn : 𝔎) :
    𝔚 𝔏 := by
  rw [P.separation]
  exact div_pos (mul_pos  𝖠₄  P.delta_pos)
    $ Real.sqrt_pos.2 𝖧₄

𝗇 𝔐 4 * P.cf
𝗇 𝔖 n * 𝔛 P.Cf
theorem score_budget (n : ℕ) (hn : 𝔎) :
    𝔖 * 𝔛 𝔏 /
      𝔐 ≤ 𝚡 := by
  have hnp : 0 < 𝙒 := 𝖧₄
  rw [P.separation]
  have heq : 𝔖 * 𝔛 𝔘 /
      𝔐 = 𝔛 P.Cf * 𝔛 P.delta / P.cf := by
    grind
  rw [heq]
  exact P.delta_score

theorem score_budget_reverse (n : ℕ) (hn : 𝔎) :
    𝔖 * (P.varianceMinus n - P.variancePlus n) ^ 2 /
      𝔐 ≤ 𝚡 := by
  convert P.score_budget n hn using 1 <;> ring
