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

def finePairResponseActionBudget (d q : ℕ) C a ρ  :=
  (512 * d * C^2) * (∑ j : Fin (2*q+2), |responseWeight q j|) * highSeparatedDerivativeBudget a ρ

theorem finePairDistance_response_all_count_bound {d n F } q (hn : 1 ≤ n)
    C a V η ρ (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) g w
    c y
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d F → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ →
      ∀ i, |∑ γ, highFrameFeature (U i) γ * v γ| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    |responseMatrixAction q C (finePairDistanceMatrix d F) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
        finePairResponseActionBudget d q C a ρ * n^2 * η^2 := by
  have hh := high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
    (finePairDistanceMatrix d F) g w (fun i => highFrameFeature (U i)) c y hc hg hw hφ hp
  have hA := finePairDistanceMatrix_l1_le d F
  have hnonneg : 0 ≤ (∑ j : Fin (2*q+2), |responseWeight q j|) *
      (4 * (((2*ρ+a)/a^2)^2 + 2/a^2) * (n : ℝ)^2 * η^2) := by positivity
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2*C^2)) hnonneg
  exact (hh.trans hmul).trans_eq (by
    unfold finePairResponseActionBudget highSeparatedDerivativeBudget
    ring)

def finePairDensityCoefficientBudget ad bd M n  :=
  |finePairDensityPrefactor ad bd| * bd^n *
    Real.cosh ((M+2 : ℕ) * exteriorTau ((ad+bd)/(bd-ad)))

theorem finePairDensityCoefficientBudget_nonneg ad bd (hbd : 0 ≤ bd) M n :
    0 ≤ finePairDensityCoefficientBudget ad bd M n := by
  unfold finePairDensityCoefficientBudget
  positivity

theorem finePairCountCoefficient_product_bound {n }
    ad bd (ha : 0 < ad) (hab : ad < bd) M
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) S :
    |finePairCountCoefficient ad bd M n S.card * (∏ i ∈ S, p i)| ≤
      finePairDensityCoefficientBudget ad bd M n := by
  have hb  := ha.trans hab
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    grind
  have hprod : |∏ i ∈ S, p i| ≤ bd^S.card := by
    rw [Finset.abs_prod]
    grind only [Finset.prod_le_prod₀, abs_nonneg, Finset.prod_const]
  have hr0 : 0 ≤ (bd-ad)/(4*bd) := div_nonneg (sub_nonneg.mpr hab.le) (by positivity)
  have hr1 : (bd-ad)/(4*bd) ≤ 1 := by
    bound
  have hrpow : ((bd-ad)/(4*bd))^S.card ≤ 1 := pow_le_one₀ hr0 hr1
  have hcoeff := finePairCountCoefficient_abs_bound ad bd ha hab M n S.card
  have he : |finePairDensityPrefactor ad bd| *
      (bd^(n-S.card) * ((bd-ad)/(4*bd))^S.card) *
      Real.cosh ((M+2 : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) * bd^S.card =
      finePairDensityCoefficientBudget ad bd M n * ((bd-ad)/(4*bd))^S.card := by
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
