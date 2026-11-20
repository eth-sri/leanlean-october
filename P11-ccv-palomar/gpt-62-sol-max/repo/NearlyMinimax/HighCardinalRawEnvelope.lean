module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.HighFrameLocalBounds
public import NearlyMinimax.CardinalGlobalDefectL2
public import NearlyMinimax.CardinalGlobalBandL2

@[expose] public section

/-! Raw numerator of the genuine ordinary cardinal packet. Its alias and
Taylor pieces are evaluated before a likelihood denominator is introduced. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def highCardinalRawNumerator {d n F : ℕ} (ad bd lam T : ℝ) (m D q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  highPacketFirstAction (cardinalSeparatedMeasure d n T) ad bd m n D q C
    (cardinalSeparatedAmplitude lam) c p (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

section
variable {d n F : ℕ}

theorem highCardinalRawNumerator_eq_alias_defect
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      (∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
        g w (fun i => highFrameFeature (U i)) c y := by
  letI := cardinal_separated_measure_finite d n hT
  unfold highCardinalRawNumerator
  rw [highPacketSignedMeasure_product_integral _ ad bd haD hab m n D q hn C _
    ⟨cardinal_separated_amplitude_measurable lam, cardinal_separated_cost_integrable lam hT⟩ c p hp
    (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
    (fun i l => cardinal_separated_factor_measurable lam l (U i))
    (fun ζ i l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i))]
  have hact := high_cardinal_packet_action_exact ad bd lam haD hab hlam hT m D q hn hnm hnD C U hU p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)
  simp only [highCardinalDensityReset] at hact
  rw [hact, integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
  ring

theorem high_cardinal_alias_abs_bound (lam T a V η bd : ℝ)
    (hlam : 0 ≤ lam) (ha : 0 < a) (hbd : 0 ≤ bd)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (hp : ∀ i, |p i| ≤ bd) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ)
    (hMass : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c i) V u)
    (y : Fin n → Fin 3) :
    |η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      (η^2 * bd^n / a^2) * ∑ i, cardinalWeightDefect i lam T U := by
  have hterm (i : Fin n) :
      |(w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      cardinalWeightDefect i lam T U * (1/a^2) := by
    have hd := cardinalWeightDefect_mem_unit i hlam T U
    have hw2 : (w i)^2 ≤ 1 := by aesop
    have hv := high_response_variance_term_abs_bound a V η ha g w (fun i => highFrameFeature (U i)) c hMass y i
    rw [abs_mul, abs_mul, abs_sq, abs_sub_comm]
    change (w i)^2 * |cardinalWeightDefect i lam T U| *
      |highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤ _
    rw [abs_of_nonneg hd.1]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hw2 hd.1) hv (abs_nonneg _)
      (by grind)).trans_eq (by ring)
  have hsum :=
    (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun i _ => hterm i))
  rw [abs_mul, abs_mul, abs_sq]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p bd hp)
    (sq_nonneg η)) hsum (abs_nonneg _) (mul_nonneg (sq_nonneg η) (pow_nonneg hbd n))
  exact hh.trans_eq (by rw [← Finset.sum_mul]; ring)

end

def cardinalRawAliasCoefficient (n : ℕ) (bd a η : ℝ) : ℝ := η^2 * bd^n / a^2

def cardinalRawTaylorCoefficient (n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  bd^n * highResponseRemainderConstant q C a ρ * (n : ℝ)^(2*q+2) * η^(2*q+2)

section
variable {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3)
include haD hab hlam hT hn hnm hnD hnF hq hC ha hη hρ hηρ hU hpD hg hw hc hp

theorem highCardinalRawNumerator_abs_bound_of_chart :
    |highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y| ≤
      cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) +
        cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
  have hCpos := lt_of_lt_of_le zero_lt_one hC
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    rw [abs_of_pos (haD.trans_le (hpD i).1)]
    grind
  have H := highFrameResponseGuards (F := F) C a V η ρ hC ha hη hηρ U hU g w hg hw hp
  have hAlias := high_cardinal_alias_abs_bound lam T a V η bd hlam ha (haD.trans hab).le
    U p g w hpabs hw c (H.mass_nonneg hc) y
  have hRem := high_response_defect_abs_bound q hq C a V η ρ
    (integratedCardinalMatrix lam T U) g w (fun i => highFrameFeature (U i)) c y H hc
  have hTaylor : |(∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
      g w (fun i => highFrameFeature (U i)) c y| ≤
      cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
    rw [abs_mul]
    have hh := mul_le_mul (finite_density_product_abs_bound p bd hpabs) hRem
      (abs_nonneg _) (pow_nonneg (haD.trans hab).le n)
    exact hh.trans_eq (by unfold cardinalRawTaylorCoefficient spatialMatrixL1; ring)
  rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hCpos.ne' U hU p g w hpD c y]
  exact (abs_add_le _ _).trans (add_le_add hAlias hTaylor)

theorem highCardinalRawNumerator_square_bound_of_chart :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y ^ 2 ≤
      2 * cardinalRawAliasCoefficient n bd a η ^ 2 * (∑ i, cardinalWeightDefect i lam T U)^2 +
      2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
        spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U)^2 := by
  have h := highCardinalRawNumerator_abs_bound_of_chart ad bd lam haD hab hlam hT m D q
    hn hnm hnD hnF hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y
  have hsum : 0 ≤ ∑ i, cardinalWeightDefect i lam T U :=
    Finset.sum_nonneg (fun i _ => (cardinalWeightDefect_mem_unit i hlam T U).1)
  have hbd := (haD.trans hab).le
  have hA : 0 ≤ cardinalRawAliasCoefficient n bd a η := by
    unfold cardinalRawAliasCoefficient
    positivity
  have hB : 0 ≤ cardinalRawTaylorCoefficient n q bd C a ρ η := by
    unfold cardinalRawTaylorCoefficient highResponseRemainderConstant
    have hDer :=
      zero_le_one.trans (highResponseDerivativeBudget_guards a ρ).1
    positivity
  have hM : 0 ≤ spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hh := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg hA hsum) (mul_nonneg hB hM))).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh, sq_nonneg (cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) -
    cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U))]

end

end NearlyMinimax
