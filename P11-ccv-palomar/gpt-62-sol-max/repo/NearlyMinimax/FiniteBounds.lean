module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators
namespace NearlyMinimax

section
variable {ι : Type*} {s : Finset ι}

theorem norm_sum_le_card_mul {E : Type*} [SeminormedAddCommGroup E]
    {f : ι → E} {B : ℝ} (h : ∀ i ∈ s, ‖f i‖ ≤ B) :
    ‖∑ i ∈ s, f i‖ ≤ (s.card : ℝ) * B := by
  simpa using norm_sum_le_of_le s h

theorem abs_sum_le_card_mul {f : ι → ℝ} {B : ℝ} (h : ∀ i ∈ s, |f i| ≤ B) :
    |∑ i ∈ s, f i| ≤ (s.card : ℝ) * B := by
  simpa only [Real.norm_eq_abs] using norm_sum_le_card_mul (f := f) (by simpa only [Real.norm_eq_abs] using h)

theorem norm_sum_le_support_card_mul {E : Type*} [SeminormedAddCommGroup E] [Fintype ι]
    {f : ι → E} {B : ℝ} (hzero : ∀ i ∉ s, f i = 0) (h : ∀ i ∈ s, ‖f i‖ ≤ B) :
    ‖∑ i, f i‖ ≤ (s.card : ℝ) * B := by
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ => hzero i)]
  exact norm_sum_le_card_mul h

section
variable {f : ι → ℝ}

theorem abs_prod_le_pow {B : ℝ} (h : ∀ i ∈ s, |f i| ≤ B) :
    |∏ i ∈ s, f i| ≤ B ^ s.card := by
  rw [Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) h

theorem abs_prod_le_one (h : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ 1 := by
  simpa only [one_pow] using abs_prod_le_pow h

end

/-- An absolute bound for a signed sum, allowing a different envelope at each index. -/
theorem abs_weighted_sum_le_sum {w f B : ι → ℝ} (h : ∀ i ∈ s, |f i| ≤ B i) :
    |∑ i ∈ s, w i * f i| ≤ ∑ i ∈ s, |w i| * B i :=
  (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun i hi => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h i hi) (abs_nonneg _)

theorem abs_weighted_sum_le {w f : ι → ℝ} {B : ℝ} (h : ∀ i ∈ s, |f i| ≤ B) :
    |∑ i ∈ s, w i * f i| ≤ (∑ i ∈ s, |w i|) * B := by
  rw [Finset.sum_mul]
  exact abs_weighted_sum_le_sum h

end
end NearlyMinimax
