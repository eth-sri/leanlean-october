module

public import NearlyMinimax.HighScoreOrthogonality
public import NearlyMinimax.HighCenteredMark

@[expose] public section

/-! Bounds for the actual signed separated density/response row.  The local
budget is the total variation of its constructed signed packet, rather than
an assumed bound for a score action. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

variable {n : ℕ} (hn : 1 ≤ n) (a ρ pPlus pMinus cMass : ℝ)

def highSeparatedDerivativeBudget : ℝ :=
  4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2)

theorem highSeparatedDerivativeBudget_nonneg :
    0 ≤ highSeparatedDerivativeBudget a ρ := by
  unfold highSeparatedDerivativeBudget
  positivity

include hn in
theorem high_response_variance_correction_abs_bound
    {a V η pPlus : ℝ} (ha : 0 < a) (hpPlus : 0 ≤ pPlus)
    {p g w : Fin n → ℝ} {φ : Fin n → ι → ℝ} {c : ι → ℝ}
    (hw : ∀ i, |w i| ≤ 1) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : TernaryVector n) :
    |η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      pPlus ^ n * (1 / a ^ 2) * n ^ 2 * η ^ 2 := by
  have hvar : |∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      n / a ^ 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact (mul_le_mul (by
          simpa using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2)
          (high_response_variance_term_abs_bound a V η ha g w φ c hp y i)
          (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : n ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
  calc
    _ ≤ _ :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (finite_density_product_abs_bound p hpPlus hIncoming) (sq_nonneg η))
        hvar (abs_nonneg _) (by positivity)
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnsq (sq_nonneg a)) (by positivity)
    _ = _ := by ring

def highSeparatedScoreExponentialConstant : ℝ :=
  4 * max 1 (pPlus / (pMinus * cMass)) *
    max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)

theorem highSeparatedScoreExponentialConstant_pos :
    0 < highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass := mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

include hn in
theorem highSeparated_score_budget_absorb (η B : ℝ) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hB : 0 ≤ B) :
    let ratio := 1 / a ^ 2
    (pPlus / (pMinus * cMass)) ^ n *
      (highSeparatedDerivativeBudget a ρ * B + ratio) * n ^ 2 * η ^ 2 ≤
      (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ n *
        η ^ 2 * (B + 1) := by
  intro ratio
  let R  := max 1 (pPlus / (pMinus * cMass))
  let K  := max 1 (highSeparatedDerivativeBudget a ρ + ratio)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hder := highSeparatedDerivativeBudget_nonneg a ρ
  have hK : highSeparatedDerivativeBudget a ρ * B + ratio ≤ K * (B + 1) := by
    have hk : highSeparatedDerivativeBudget a ρ + ratio ≤ K := le_max_right _ _
    have hz : 0 ≤ ratio := by positivity
    nlinarith only [hk, hB, hder, hz, mul_nonneg hB hz]
  have hnReal : 2 * (n : ℝ) ^ 2 + 1 ≤ 2 ^ (2 * n) := by exact_mod_cast (Nat.two_mul_sq_add_one_le_two_pow_two_mul n)
  have hnsq : n ^ 2 ≤ (4 : ℝ) ^ n := by
    have he : 2 ^ (2 * n) = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
    rw [he] at hnReal
    nlinarith only [hnReal, sq_nonneg n]
  have hRpow : (pPlus / (pMinus * cMass)) ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (div_nonneg hpPlus (mul_pos hpMinus hcMass).le) (le_max_right _ _) _
  have hKpow : K ≤ K ^ n := le_self_pow₀ hK1 (by omega)
  calc
    _ ≤ (R ^ n * (K * (B + 1))) * 4 ^ n * η ^ 2 := by
      gcongr <;> assumption
    _ ≤ (R ^ n * (K ^ n * (B + 1))) * 4 ^ n * η ^ 2 := by
      gcongr
    _ = _ := by
      dsimp [highSeparatedScoreExponentialConstant, R, K]
      ring

end NearlyMinimax
