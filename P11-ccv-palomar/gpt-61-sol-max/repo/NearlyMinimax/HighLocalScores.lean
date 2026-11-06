module

public import NearlyMinimax.HighResponseRemainder

@[expose] public section

/-! Actual finite density-marked response updates and their local scores.
All likelihood and score bounds are proved from legal density/response
factors and the finite atomic rules. -/
noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

section Packet
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

/-- Density marks are kept separate from the response covariance marks. -/
def highDensityResponseAction q C (weights : E → ℝ)
    (A : E → ι → ι → ℝ) c (b : E → ℝ)
    Φ  :=
  ∑ e, weights e * b e * responseMatrixAction q C (A e) c Φ

omit [DecidableEq ι] in
theorem high_response_product_normalized {n : ℕ} (a V η : ℝ) (ha : a ≠ 0)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) :
    ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y = 1 := by
  unfold highResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

omit [DecidableEq ι] in
theorem high_response_variance_term_sum_zero {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (i : Fin n) :
    ∑ y : Fin n → Fin 3, highResponseVarianceTerm a V η g w φ c y i = 0 := by
  simpa only [highResponseVarianceTerm, patchVarianceTerm, zero_mul, add_zero] using
    patch_variance_term_sum_zero n a V 0 (coefficientRegression η g w φ c) (fun _ => 0) 0 i

/-- The explicit finite covariance-mark variation entering the response
packet; it is determined by the actual matrices and density weights. -/
def highResponsePacketCost C (weights : E → ℝ) (A : E → ι → ι → ℝ)  :=
  ∑ e, |weights e| * (2 * C ^ 2 * ∑ k, ∑ l, |A e k l|)

def highLocalDerivativeConstant q a ρ  :=
  (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
    (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2))

theorem finite_density_product_abs_bound {n } (p : Fin n → ℝ) pPlus
    (_hpPlus : 0 ≤ pPlus) (hp : ∀ i, |p i| ≤ pPlus) :
    |∏ i, p i| ≤ pPlus ^ n := by
  rw [Finset.abs_prod]
  grind only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_le_prod₀, abs_nonneg]

omit [DecidableEq ι] in
theorem high_response_variance_term_abs_bound {n : ℕ} (a V η : ℝ) (ha : 0 < a)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) (i : Fin n) :
    |highResponseVarianceTerm a V η g w φ c y i| ≤ 1 / a ^ 2 := by
  have hprod : |∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (coefficientRegression η g w φ c l) V (y l)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply (Finset.prod_le_prod₀ (fun l _ => abs_nonneg _)
      (fun l _ => show |ternaryMass a (coefficientRegression η g w φ c l) V (y l)| ≤ 1 from by
        rw [abs_of_nonneg (hp l (y l))]
        exact ternary_mass_le_one a _ V ha.ne' (hp l) (y l))).trans_eq
    exact Finset.prod_const_one
  unfold highResponseVarianceTerm
  rw [abs_mul]
  exact (mul_le_mul (ternary_variance_derivative_abs_bound a ha (y i)) hprod
    (abs_nonneg _) (by positivity : 0 ≤ 1 / a ^ 2)).trans_eq (mul_one _)

theorem high_density_response_product_abs_bound {n } q (hn : 1 ≤ n)
    C a V η ρ pPlus (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    weights A (pReset : E → Fin n → ℝ)
    (g w : Fin n → ℝ) φ c
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) y :
    |highDensityResponseAction q C weights A c (fun e => ∏ i, pReset e i)
      (fun c => highResponseProduct a V η g w φ c y)| ≤
      pPlus ^ n * highResponsePacketCost C weights A *
        (highLocalDerivativeConstant q a ρ * n ^ 2 * η ^ 2) := by
  unfold highDensityResponseAction
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e, (|weights e| * pPlus ^ n) *
        ((2 * C ^ 2 * ∑ k, ∑ l, |A e k l|) *
          (highLocalDerivativeConstant q a ρ * (n : ℝ) ^ 2 * η ^ 2)) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul, abs_mul]
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left
          (finite_density_product_abs_bound (pReset e) pPlus hpPlus (hReset e)) (abs_nonneg _))
        _ (abs_nonneg _) (by positivity)
      exact (high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
        (A e) g w φ c y hc hg hw hφ hp).trans_eq (by
          unfold highLocalDerivativeConstant
          ring)
    _ = _ := by
      unfold highResponsePacketCost
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring

end Packet
end NearlyMinimax
