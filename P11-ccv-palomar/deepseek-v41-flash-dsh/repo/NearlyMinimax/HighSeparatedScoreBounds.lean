module

public import NearlyMinimax.HighSeparatedScores
public import NearlyMinimax.HighCenteredMark

@[expose] public section

/-! Bounds for the actual signed separated density/response row.  The local
budget is the total variation of its constructed signed packet, rather than
an assumed bound for a score action. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

def highSeparatedDerivativeBudget (a ρ : ℝ) : ℝ :=
  4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2)

variable (a ρ : ℝ)

theorem highSeparatedDerivativeBudget_nonneg :
    0 ≤ highSeparatedDerivativeBudget a ρ := by
  unfold highSeparatedDerivativeBudget
  positivity

theorem high_response_variance_correction_abs_bound {n : ℕ} (hn : 1 ≤ n)
    (a V η pPlus : ℝ) (ha : 0 < a) (hpPlus : 0 ≤ pPlus)
    (p g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) :
    |η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      pPlus ^ n * (1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 := by
  have hvar : |∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      (n : ℝ) / a ^ 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hwsq : (w i) ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2
        exact (mul_le_mul hwsq
          (high_response_variance_term_abs_bound a V η ha g w φ c hp y i)
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
  calc
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) / a ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (finite_density_product_abs_bound p pPlus hpPlus hIncoming) (sq_nonneg η))
        hvar (abs_nonneg _) (by positivity)
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) ^ 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnsq (sq_nonneg a)) (by positivity)
    _ = _ := by ring

def highSeparatedScoreExponentialConstant (a ρ pPlus pMinus cMass : ℝ) : ℝ :=
  4 * max 1 (pPlus / (pMinus * cMass)) *
    max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)

theorem highSeparatedScoreExponentialConstant_pos (a ρ pPlus pMinus cMass : ℝ) :
    0 < highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass := by
  unfold highSeparatedScoreExponentialConstant
  exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

theorem highSeparated_score_budget_absorb (n : ℕ) (hn : 1 ≤ n)
    (a ρ pPlus pMinus cMass η B : ℝ) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hB : 0 ≤ B) :
    (pPlus / (pMinus * cMass)) ^ n *
      (highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 ≤
      (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ n *
        η ^ 2 * (B + 1) := by
  let R : ℝ := max 1 (pPlus / (pMinus * cMass))
  let K : ℝ := max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hK1 : 1 ≤ K := le_max_left _ _
  have hder := highSeparatedDerivativeBudget_nonneg a ρ
  have hK : highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2 ≤ K * (B + 1) := by
    have hk : highSeparatedDerivativeBudget a ρ + 1 / a ^ 2 ≤ K := le_max_right _ _
    have hz : 0 ≤ 1 / a ^ 2 := by positivity
    nlinarith only [hk, hB, hder, hz, mul_nonneg hB hz]
  have hnNat := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have hnReal : (2 : ℝ) * (n : ℝ) ^ 2 + 1 ≤ 2 ^ (2 * n) := by exact_mod_cast hnNat
  have hnsq : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
    have he : (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
    rw [he] at hnReal
    nlinarith only [hnReal, sq_nonneg (n : ℝ)]
  have hRpow : (pPlus / (pMinus * cMass)) ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (div_nonneg hpPlus (mul_pos hpMinus hcMass).le) (le_max_right _ _) _
  have hKpow : K ≤ K ^ n := le_self_pow₀ hK1 (by omega)
  calc
    _ ≤ (R ^ n * (K * (B + 1))) * (4 : ℝ) ^ n * η ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hRpow hK (by positivity) (by positivity)) hnsq
          (sq_nonneg _) (by positivity)) (sq_nonneg η)
    _ ≤ (R ^ n * (K ^ n * (B + 1))) * (4 : ℝ) ^ n * η ^ 2 := by
      gcongr
    _ = _ := by
      dsimp [highSeparatedScoreExponentialConstant, R, K]
      simp only [mul_pow]
      ring

end NearlyMinimax
