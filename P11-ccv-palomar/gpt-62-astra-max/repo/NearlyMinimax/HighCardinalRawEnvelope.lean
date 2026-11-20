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

variable {d n F : ℕ} {ad bd lam : ℝ} (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T)
    {m D q : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q) {C a V η ρ : ℝ}
    (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) {U : DesignSample d n}
    (hU : ∀ i l, |U i l| ≤ 2) {p g w : Fin n → ℝ} (hpD : ∀ i, p i ∈ Icc ad bd) (hg : ∀ i, |g i| ≤ ρ/2)
    (hw : ∀ i, |w i| ≤ 1) {c : HighFrameVector d F} (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : TernaryVector n)

def highCardinalRawNumerator (ad bd lam T : ℝ) (m D q : ℕ)
    (C a V η : ℝ) (U : DesignSample d n) (p g w : Fin n → ℝ)
    (c : HighFrameVector d F) (y : TernaryVector n) : ℝ :=
  (∫ᵛ e, highPacketObservable ad bd C c
    (fun ζ z eps => ∏ i, highCardinalDensityReset ad bd lam U p ζ z eps i)
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) e
    ∂<•highPacketSignedMeasure (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam)) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

include haD hab hlam hT in
theorem highCardinalRawNumerator_eq_alias_defect (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η : ℝ) (hC : C ≠ 0)
    {U : DesignSample d n} (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d F) (y : TernaryVector n) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      (∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
        g w (fun i => highFrameFeature (U i)) c y := by
  letI := cardinal_separated_measure_finite d n hT
  have hm z eps i :
      Measurable (fun ζ => highCardinalDensityReset ad bd lam U p ζ z eps i) := (Finset.measurable_fun_sum _ (fun l _ =>
      (cardinal_separated_factor_measurable lam l (U i)).const_mul (eps l))).const_mul _ |>.const_add z
  have hb ζ e i :
      |highCardinalDensityReset ad bd lam U p ζ (densityPacketAtom ad bd m n D e).1
        (densityPacketAtom ad bd m n D e).2 i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le e
    have h := localDensityReset_mem_interval ad bd haD hab n hn _ he.1 _ he.2
      (fun i l => cardinalSeparatedFactor lam ζ l (U i)) (hp i)
      (fun l => cardinal_separated_factor_abs_le_one lam ζ l (hU i))
    change |localDensityReset ad bd _ _ p _ i| ≤ _
    grind
  unfold highCardinalRawNumerator
  rw [highPacketSignedMeasure_factor_integral ad bd m n D
    (cardinal_separated_amplitude_measurable lam) (cardinal_separated_cost_integrable lam hT) _
    (fun z eps => by fun_prop) (by bound)
    (fun ζ e => finite_density_product_abs_bound _ (haD.trans hab).le (hb ζ e)) (finePairResponseAtomBound_le q C c _), high_cardinal_packet_action_exact haD hab hlam hT m D q hn hnm hnD C hU p c,
    integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
  ring

theorem high_cardinal_alias_abs_bound (lam T a V η bd : ℝ)
    (hlam : 0 ≤ lam) (ha : 0 < a) (hbd : 0 ≤ bd)
    {U : DesignSample d n} {p g w : Fin n → ℝ}
    (hp : ∀ i, |p i| ≤ bd) (hw : ∀ i, |w i| ≤ 1)
    {c : HighFrameVector d F}
    (hMass : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c i) V u)
    (y : TernaryVector n) :
    |η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      (η^2 * bd^n / a^2) * ∑ i, cardinalWeightDefect i lam T U := by
  have hterm i :
      |(w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (highFrameFeature ∘ U) c y i| ≤
      cardinalWeightDefect i lam T U * (1/a^2) := by
    have hd := cardinalWeightDefect_mem_unit i hlam T U
    have hw2 : (w i)^2 ≤ 1 := by simp_all
    have hv := high_response_variance_term_abs_bound a V η ha g w _ c hMass y i
    rw [abs_mul, abs_mul, abs_sq, abs_sub_comm]
    change (w i)^2 * |cardinalWeightDefect i lam T U| *
      _ ≤ _
    rw [abs_of_nonneg hd.1]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hw2 hd.1) hv (abs_nonneg _)
      (by simpa using hd.1)).trans_eq (by ring)
  have hsum  :=
    (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun i _ => hterm i))
  rw [abs_mul, abs_mul, abs_sq]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p hbd hp)
    (sq_nonneg η)) hsum (abs_nonneg _) (by positivity)
  exact hh.trans_eq (by rw [← Finset.sum_mul]; ring)

def cardinalRawAliasCoefficient (n : ℕ) (bd a η : ℝ) : ℝ := η^2 * bd^n / a^2

def cardinalRawTaylorCoefficient (n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  bd^n * highResponseRemainderConstant q C a ρ * n^(2*q+2) * η^(2*q+2)

include haD hab hlam hT hn hnm hnD hnF hq hC ha hη hρ hηρ hU hpD hg hw hc hp in
theorem highCardinalRawNumerator_abs_bound_of_chart :
    |highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y| ≤
      cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) +
        cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
  have hCpos := lt_of_lt_of_le zero_lt_one hC
  have hpabs i : |p i| ≤ bd := by
    grind
  have hMass i u  :=
    hp _ (highFrameCoefficientRegression_abs_le hC hη hηρ hU hg hw hc i) u
  have hAlias := high_cardinal_alias_abs_bound lam T a V η bd hlam ha (haD.trans hab).le hpabs hw hMass y
  have hRem := high_response_defect_abs_bound hq hCpos ha hη hρ hηρ (integratedCardinalMatrix lam T U) _ y hc hg hw (fun v hv i => highFrameProfile_abs_le_one hC (hU i) hv) hp
  have hTaylor : |(∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
      g w (highFrameFeature ∘ U) c y| ≤
      cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
    rw [abs_mul]
    have hh := mul_le_mul (finite_density_product_abs_bound p (haD.trans hab).le hpabs) hRem
      (abs_nonneg _) (pow_nonneg (haD.trans hab).le n)
    exact hh.trans_eq (by unfold cardinalRawTaylorCoefficient spatialMatrixL1; ring)
  rw [highCardinalRawNumerator_eq_alias_defect haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hCpos.ne' hU p g w hpD c y]
  exact (abs_add_le _ _).trans (add_le_add hAlias hTaylor)

include haD hab hlam hT hn hnm hnD hnF hq hC ha hη hρ hηρ hU hpD hg hw hc hp in
theorem highCardinalRawNumerator_square_bound_of_chart :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y ^ 2 ≤
      2 * cardinalRawAliasCoefficient n bd a η ^ 2 * (∑ i, cardinalWeightDefect i lam T U)^2 +
      2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
        spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U)^2 := by
  have h := highCardinalRawNumerator_abs_bound_of_chart haD hab hlam hT
    hn hnm hnD hnF hq hC ha hη hρ hηρ hU hpD hg hw hc hp y
  have hsum : 0 ≤ ∑ i, cardinalWeightDefect i lam T U :=
    Finset.sum_nonneg (fun i _ => (cardinalWeightDefect_mem_unit i hlam T U).1)
  have hbd  := (haD.trans hab).le
  have hA : 0 ≤ cardinalRawAliasCoefficient n bd a η := by
    unfold cardinalRawAliasCoefficient
    positivity
  have hB : 0 ≤ cardinalRawTaylorCoefficient n q bd C a ρ η := by
    unfold cardinalRawTaylorCoefficient highResponseRemainderConstant
    have hDer  :=
      zero_le_one.trans (highResponseDerivativeBudget_guards a ρ).1
    positivity
  have hM : 0 ≤ spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hh := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg hA hsum) (mul_nonneg hB hM))).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh, sq_nonneg (cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) -
    cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U))]

end NearlyMinimax
