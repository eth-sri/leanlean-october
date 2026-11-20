module

public import NearlyMinimax.FinePairAllCounts

@[expose] public section

/-! Uniform all-count response and density-coefficient bounds for the true
fine-pair row. The dependence on the exterior degree remains explicit. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section
variable (ad bd : ℝ) (hbd : 0 ≤ bd) (M n d q : ℕ)

def finePairResponseActionBudget (C a ρ : ℝ) : ℝ :=
  (512 * d * C^2) * responseVariation q * highSeparatedDerivativeBudget a ρ

theorem finePairDistance_response_all_count_bound {d n F : ℕ} (q : ℕ) (hn : 1 ≤ n)
    {C a V η ρ : ℝ} (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : DesignSample d n) {g w : Fin n → ℝ}
    {c : HighFrameVector d F} (y : TernaryVector n)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : HighFrameVector d F, (∑ γ, |v γ|) ≤ C⁻¹ →
      ∀ i, |∑ γ, highFrameFeature (U i) γ * v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    |responseMatrixAction q C (finePairDistanceMatrix d F) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
        finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2 := by
  have hh := high_response_matrix_all_count_bound q hn hC ha hη hρ hηρ
    (finePairDistanceMatrix d F) y hc hg hw hφ hp
  have hA := finePairDistanceMatrix_l1_le d F
  have hnonneg : 0 ≤ responseVariation q *
      (4 * (((2*ρ+a)/a^2)^2 + 2/a^2) * (n : ℝ)^2 * η^2) := by positivity
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2*C^2)) hnonneg
  exact (hh.trans hmul).trans_eq (by
    unfold finePairResponseActionBudget highSeparatedDerivativeBudget
    ring)

def finePairDensityCoefficientBudget : ℝ :=
  |finePairDensityPrefactor ad bd| * bd^n *
    Real.cosh ((M+2 : ℕ) * intervalExteriorTau ad bd)

include hbd in
theorem finePairDensityCoefficientBudget_nonneg :
    0 ≤ finePairDensityCoefficientBudget ad bd M n := by
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hbd _)) (Real.cosh_pos _).le

end

theorem finePairCountCoefficient_product_bound {n : ℕ}
    {ad bd : ℝ} (ha : 0 < ad) (hab : ad < bd) (M : ℕ)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd) (S : Finset (Fin n)) :
    |finePairCountCoefficient ad bd M n S.card * (∏ i ∈ S, p i)| ≤
      finePairDensityCoefficientBudget ad bd M n := by
  have hb  := ha.trans hab
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    grind
  have hprod : |∏ i ∈ S, p i| ≤ bd^S.card := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hpabs i)).trans_eq
      (Finset.prod_const _)
  have hr0 : 0 ≤ (bd-ad)/(4*bd) := by positivity
  have hr1 : (bd-ad)/(4*bd) ≤ 1 := by
    bound
  let ratio := ((bd-ad)/(4*bd))^S.card
  have hrpow : ratio ≤ 1 := pow_le_one₀ hr0 hr1
  have hcoeff := finePairCountCoefficient_abs_bound ha hab M n S.card
  have he : |finePairDensityPrefactor ad bd| *
      (bd^(n-S.card) * ratio) *
      Real.cosh ((M+2 : ℕ)*intervalExteriorTau ad bd) * bd^S.card =
      finePairDensityCoefficientBudget ad bd M n * ratio := by
    unfold finePairDensityCoefficientBudget
    have hpow : bd^(n-S.card) * bd^S.card = bd^n := by
      rw [← pow_add, Nat.sub_add_cancel hcard]
    grind
  rw [abs_mul]
  apply (mul_le_mul hcoeff hprod (abs_nonneg _) (by positivity)).trans
  rw [he]
  exact (mul_le_mul_of_nonneg_left hrpow
    (finePairDensityCoefficientBudget_nonneg ad bd hb.le M n)).trans_eq (mul_one _)

end NearlyMinimax
