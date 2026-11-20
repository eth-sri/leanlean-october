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

def finePairResponseActionBudget (d q : ℕ) (C a ρ : ℝ) : ℝ :=
  (512 * d * C^2) * (∑ j : Fin (2*q+2), |responseWeight q j|) * highSeparatedDerivativeBudget a ρ

theorem finePairDistance_response_all_count_bound {d n F : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (U : Fin n → Covariate d) (g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3)
    (H : ResponseGuards C a V η ρ g w (fun i => highFrameFeature (D := F) (U i)))
    (hc : ∑ γ, |c γ| ≤ C⁻¹) :
    |responseMatrixAction q C (finePairDistanceMatrix d F) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
        finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2 := by
  have hh := high_response_matrix_all_count_bound q hn C a V η ρ
    (finePairDistanceMatrix d F) g w (fun i => highFrameFeature (U i)) c y H hc
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finePairDistanceMatrix_l1_le d F) (by positivity : (0 : ℝ) ≤ 2*C^2))
    (by unfold highLocalDerivativeConstant; positivity : 0 ≤ highLocalDerivativeConstant q a ρ * (n : ℝ)^2 * η^2)
  exact (hh.trans hmul).trans_eq (by
    unfold finePairResponseActionBudget highSeparatedDerivativeBudget highLocalDerivativeConstant
    ring)

def finePairDensityCoefficientBudget (ad bd : ℝ) (M n : ℕ) : ℝ :=
  |finePairDensityPrefactor ad bd| * bd^n *
    Real.cosh ((M+2 : ℕ) * exteriorTau ((ad+bd)/(bd-ad)))

theorem finePairDensityCoefficientBudget_nonneg (ad bd : ℝ) (hbd : 0 ≤ bd) (M n : ℕ) :
    0 ≤ finePairDensityCoefficientBudget ad bd M n := by
  apply mul_nonneg <;> positivity

theorem finePairCountCoefficient_product_bound {n : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (M : ℕ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (S : Finset (Fin n)) :
    |finePairCountCoefficient ad bd M n S.card * (∏ i ∈ S, p i)| ≤
      finePairDensityCoefficientBudget ad bd M n := by
  have hb := ha.trans hab
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    grind
  have hprod : |∏ i ∈ S, p i| ≤ bd^S.card := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hpabs i)).trans_eq
      (Finset.prod_const _)
  have hr0 : 0 ≤ (bd-ad)/(4*bd) := div_nonneg (sub_nonneg.mpr hab.le) (by positivity)
  have hr1 : (bd-ad)/(4*bd) ≤ 1 := by
    field_simp <;> linarith
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

/-- Common all-count cap for the density times response coefficient. -/
def finePairActionCap (d n M q : ℕ) (ad bd C a ρ η : ℝ) : ℝ :=
  finePairDensityCoefficientBudget ad bd M n * (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2)

end NearlyMinimax
