module

public import NearlyMinimax.Model
public import NearlyMinimax.Ternary

@[expose] public section

/-! Numeric constants for the interior zero-regression ternary submodel.
All constants are constructed from the strict margins in `ModelConstants`.
No statistical risk or testing conclusion is assumed here. -/

noncomputable section

namespace NearlyMinimax

open Set

/-- Uniform numerical guards for the one-dimensional ternary variance path. -/
structure ParametricTernaryConstants {d : ℕ} (C : ModelConstants d) where
  a : ℝ
  l : ℝ
  r : ℝ
  cf : ℝ
  Cf : ℝ
  delta : ℝ
  a_pos : 0 < a
  l_pos : 0 < l
  lower_le : C.varianceLower ≤ l
  interval : l < r
  upper_le : r ≤ C.varianceUpper
  variance_lt_square : r < a ^ 2
  fourth_le : a ^ 2 * r ≤ C.fourthBound
  cf_pos : 0 < cf
  Cf_pos : 0 < Cf
  mass_lower : ∀ V ∈ Icc l r, ∀ y : Fin 3, cf ≤ ternaryMass a 0 V y
  derivative_bound : ∀ y : Fin 3, |3 * ternaryVarianceDerivative a y| ≤ Cf
  delta_pos : 0 < delta
  delta_interval : delta ≤ (r - l) / 4
  delta_score : Cf ^ 2 * delta ^ 2 / cf ≤ 1 / 4

/-- The strict model margins imply an interior ternary interval. -/
theorem parametricTernaryConstants_exists {d : ℕ} (C : ModelConstants d) :
    Nonempty (ParametricTernaryConstants C) := by
  let s := Real.sqrt C.fourthBound
  have hC4  := lt_trans (sq_pos_of_pos C.varianceLower_pos) C.fourth_margin
  have hs  := Real.sqrt_pos.2 hC4
  have hs2  := Real.sq_sqrt hC4.le
  have hvs : C.varianceLower < s := by nlinarith [C.fourth_margin, C.varianceLower_pos]
  let t := (C.varianceLower + s) / 2
  have hvt : C.varianceLower < t := by dsimp [t]; linarith
  have hts : t < s := by dsimp [t]; linarith
  have ht  := lt_trans C.varianceLower_pos hvt
  let hi := min C.varianceUpper t
  have hvhi  := lt_min C.variance_interval hvt
  let l := C.varianceLower
  let r := (l + hi) / 2
  have hl  := C.varianceLower_pos
  have hlr : l < r := by dsimp [r, l]; linarith
  have hrhi : r < hi := by dsimp [r, l]; linarith
  have hrt  := lt_of_lt_of_le hrhi (min_le_right _ _)
  have hrU  := le_trans hrhi.le (min_le_left _ _)
  let a := Real.sqrt t
  have ha  := Real.sqrt_pos.2 ht
  have ha2  := Real.sq_sqrt ht.le
  have hfourth : a ^ 2 * r ≤ C.fourthBound := by
    nlinarith [mul_pos ht (sub_pos.2 hrt)]
  let cf := min (l / (2 * a ^ 2)) (1 - r / a ^ 2)
  have ha2pos  := sq_pos_of_pos ha
  have hcf : 0 < cf := by
    bound
  have hmass : ∀ V ∈ Icc l r, ∀ y, cf ≤ ternaryMass a 0 V y := by
    intro V hV y
    have hleft : cf ≤ V / (2 * a ^ 2) :=
      le_trans (min_le_left _ _) (div_le_div_of_nonneg_right hV.1 (by positivity))
    have hmid : cf ≤ 1 - V / a ^ 2 := le_trans (min_le_right _ _) (sub_le_sub_left
        (div_le_div_of_nonneg_right hV.2 ha2pos.le) 1)
    fin_cases y <;> simpa [ternaryMass] using (by assumption)
  let Cf := 3 / a ^ 2
  have hCf : 0 < Cf := by positivity
  have hderiv : ∀ y, |3 * ternaryVarianceDerivative a y| ≤ Cf := by
    intro y
    have hsmall : 3 / (2 * a ^ 2) ≤ Cf := by
      dsimp [Cf]
      apply (div_le_div_iff₀ (by positivity) ha2pos).2
      nlinarith
    fin_cases y
    · change |3 * (1 / (2 * a ^ 2))| ≤ Cf
      grind
    · change |3 * (-1 / a ^ 2)| ≤ Cf
      rw [show 3 * (-1 / a ^ 2) = -(Cf) by ring, abs_neg,
        abs_of_pos (by positivity)]
    · change |3 * (1 / (2 * a ^ 2))| ≤ Cf
      grind
  let delta := min ((r - l) / 4) (Real.sqrt cf / (2 * Cf))
  have hdelta : 0 < delta := by positivity
  have hdeltaI : delta ≤ (r - l) / 4 := min_le_left _ _
  have hdeltaS : Cf ^ 2 * delta ^ 2 / cf ≤ 1 / 4 := by
    have hds : delta ≤ Real.sqrt cf / (2 * Cf) := min_le_right _ _
    have hprod  := (le_div_iff₀ (by positivity)).1 hds
    have hsqrt  := Real.sq_sqrt hcf.le
    have hp : 0 ≤ delta * (2 * Cf) := by positivity
    apply (div_le_iff₀ hcf).2
    nlinarith
  exact ⟨⟨a, l, r, cf, Cf, delta, ha, hl, le_rfl, hlr, hrU,
    ha2 ▸ hrt, hfourth, hcf, hCf, hmass, hderiv, hdelta, hdeltaI, hdeltaS⟩⟩

namespace ParametricTernaryConstants

variable {d : ℕ} {C : ModelConstants d} (P : ParametricTernaryConstants C)

section
variable (V : ℝ) (hV : V ∈ Icc P.l P.r)
include hV

/-- With counting measure normalized to total mass one, the density is three
times the ternary mass.  The same positive lower guard remains valid. -/
theorem density_lower (y : Fin 3) :
    P.cf ≤ 3 * ternaryMass P.a 0 V y := by
  bound [P.mass_lower V hV y, P.cf_pos]

theorem model_variance_bounds :
    C.varianceLower ≤ V ∧ V ≤ C.varianceUpper :=
  ⟨le_trans P.lower_le hV.1, le_trans hV.2 P.upper_le⟩

theorem variance_lt_square_of_mem :
    V < P.a ^ 2 := lt_of_le_of_lt hV.2 P.variance_lt_square

theorem fourth_le_of_mem :
    P.a ^ 2 * V ≤ C.fourthBound :=
  le_trans (mul_le_mul_of_nonneg_left hV.2 (sq_nonneg _)) P.fourth_le

end

variable (n : ℕ) (hn : 1 ≤ n)

def varianceMinus : ℝ := (P.l + P.r) / 2 - P.delta / Real.sqrt n

def variancePlus : ℝ := (P.l + P.r) / 2 + P.delta / Real.sqrt n

theorem perturbation_nonneg : 0 ≤ P.delta / Real.sqrt n := div_nonneg P.delta_pos.le (Real.sqrt_nonneg _)

include hn in
theorem perturbation_le :
    P.delta / Real.sqrt n ≤ P.delta := by
  have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  bound [P.delta_pos]

include hn in
theorem varianceMinus_mem :
    P.varianceMinus n ∈ Icc P.l P.r := by
  have hnonneg := P.perturbation_nonneg n
  have hpert := P.perturbation_le n hn
  have hdelta := P.delta_interval
  grind [varianceMinus]

include hn in
theorem variancePlus_mem :
    P.variancePlus n ∈ Icc P.l P.r := by
  have hnonneg := P.perturbation_nonneg n
  have hpert := P.perturbation_le n hn
  have hdelta := P.delta_interval
  grind [variancePlus]

theorem separation :
    P.variancePlus n - P.varianceMinus n = 2 * P.delta / Real.sqrt n := by
  dsimp [varianceMinus, variancePlus]
  ring

include hn in
theorem score_budget :
    n * P.Cf ^ 2 * (P.variancePlus n - P.varianceMinus n) ^ 2 /
      (4 * P.cf) ≤ 1 / 4 := by
  have hnp : 0 < (n : ℝ) := by positivity
  rw [P.separation]
  have heq : n * P.Cf ^ 2 * (2 * P.delta / Real.sqrt n) ^ 2 /
      (4 * P.cf) = P.Cf ^ 2 * P.delta ^ 2 / P.cf := by
    grind
  rw [heq]
  exact P.delta_score

end ParametricTernaryConstants

end NearlyMinimax
