module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.FinePairCountTwoSpatialEnergy
public import NearlyMinimax.HighSelectedScoreEnergy

@[expose] public section

/-! Universal deterministic spatial envelopes for the actual signed
response numerators. These depend only on the local chart and fixed caps. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 def cardinalGeometryEnvelope {d n F : ℕ} (q : ℕ) (bd C a ρ η T : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n * (2*cardinalRawAliasCoefficient n bd a η^2 *
    (∑ i, cardinalWeightDefect i (spatialInterpolationLambda d) T U)^2 +
    2*cardinalRawTaylorCoefficient n q bd C a ρ η^2 *
      spatialMatrixL1 (integratedCardinalMatrix (D := F) (spatialInterpolationLambda d) T U)^2)

 section
variable {d n F : ℕ}

theorem cardinalGeometryEnvelope_nonneg (q : ℕ) (bd C a ρ η T : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ cardinalGeometryEnvelope (F := F) q bd C a ρ η T U := by
  unfold cardinalGeometryEnvelope
  positivity

 theorem cardinalGeometryEnvelope_integrable_and_le (hd : 5 ≤ d) (hn : 2 ≤ n)
    (q : ℕ) (bd C a ρ η : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (cardinalGeometryEnvelope (d := d) (n := n) (F := F) q bd C a ρ η T)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, cardinalGeometryEnvelope (F := F) q bd C a ρ η T U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n * cardinalRawSpatialEnergyBudget d n q bd C a ρ η T := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hZ : Integrable (fun U => (∑ i : Fin n, cardinalWeightDefect i (spatialInterpolationLambda d) T U)^2)
      (fullSpatialPatchDesign d n) := by
    have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) Finset.univ
      (fun i U => cardinalWeightDefect i (spatialInterpolationLambda d) T U)
      (fun i _ => cardinalWeightDefect_measurable i _ hT)
      (fun i _ => cardinalWeightDefect_square_integrable i hlam hT)
    simpa only [abs_of_nonneg (cardinalWeightDefect_mem_unit _ hlam T _).1] using h
  have hE := integratedCardinalMatrix_full_square_integrable (D := F) hd hn hT
  have hi : Integrable (cardinalGeometryEnvelope (d := d) (n := n) (F := F) q bd C a ρ η T)
      (fullSpatialPatchDesign d n) := ((hZ.const_mul _).add (hE.const_mul _)).const_mul _
  refine ⟨hi, ?_⟩
  unfold cardinalGeometryEnvelope
  rw [integral_const_mul, integral_add (hZ.const_mul _) (hE.const_mul _), integral_const_mul, integral_const_mul]
  have h := add_le_add (mul_le_mul_of_nonneg_left (cardinalWeightDefect_sum_square_integral_le (d := d) (n := n) (by omega) hn hT)
    (by positivity : 0 ≤ 2*cardinalRawAliasCoefficient n bd a η^2))
    (mul_le_mul_of_nonneg_left (integratedCardinalMatrix_full_square_integral_le (D := F) hd hn hT)
      (by positivity : 0 ≤ 2*cardinalRawTaylorCoefficient n q bd C a ρ η^2))
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (3 : ℝ)^n)).trans_eq (by
    rfl)

 theorem highCardinalRawNumerator_sum_square_le_geometry
    (ad bd : ℝ) (haD : 0 < ad) (hab : ad < bd) {T : ℝ} (hT : 1 ≤ T)
    (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, highCardinalRawNumerator ad bd (spatialInterpolationLambda d) T m D q
      C a V η U p g w c y^2) ≤ cardinalGeometryEnvelope (F := F) q bd C a ρ η T U := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  exact ternary_sum_le (highCardinalRawNumerator_square_bound_of_chart ad bd _ haD hab hlam hT m D q hn hnm hnD hnF hq
    C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp)

end

section
variable {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)

/-- Geometry for any selected subset family, before making a count-specific
choice of the spatial moment budget. -/
def fineSelectedGeometryEnvelope (s : Finset (Finset (Fin n))) (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n * (finePairActionCap d n M q ad bd C a ρ η)^2 *
    (∑ S ∈ s, |finePairTimeSubsetMoment T0 N U S|)^2

def fineFieldGeometryEnvelope (U : Fin n → Covariate d) : ℝ :=
  fineSelectedGeometryEnvelope ad bd T0 N M q C a ρ η
    ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => 4 ≤ S.card ∧ Even S.card)) U

def finePairAliasGeometryEnvelope (U : Fin n → Covariate d) : ℝ :=
  fineSelectedGeometryEnvelope ad bd T0 N M q C a ρ η (Finset.univ.powersetCard 2) U

section
variable (U : Fin n → Covariate d)

theorem fineFieldGeometryEnvelope_nonneg :
    0 ≤ fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  unfold fineFieldGeometryEnvelope fineSelectedGeometryEnvelope
  positivity

theorem finePairAliasGeometryEnvelope_nonneg :
    0 ≤ finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  unfold finePairAliasGeometryEnvelope fineSelectedGeometryEnvelope
  positivity

end

private theorem fineSelectedGeometryEnvelope_integrable_and_le [NeZero d] (s : Finset (Finset (Fin n))) (B : ℝ)
    (hi : ∀ S ∈ s, Integrable (fun U : Fin n → Covariate d => finePairTimeSubsetMoment T0 N U S ^ 2)
      (fullSpatialPatchDesign d n))
    (hB : (∫ U : Fin n → Covariate d, (∑ S ∈ s, |finePairTimeSubsetMoment T0 N U S|)^2
      ∂fullSpatialPatchDesign d n) ≤ B) :
    Integrable (fineSelectedGeometryEnvelope (d := d) ad bd T0 N M q C a ρ η s) (fullSpatialPatchDesign d n) ∧
    (∫ U, fineSelectedGeometryEnvelope ad bd T0 N M q C a ρ η s U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n * ((finePairActionCap d n M q ad bd C a ρ η)^2 * B) := by
  refine ⟨(finite_sum_abs_square_integrable _ s _ (fun S _ => finePairTimeSubsetMoment_measurable T0 N S) hi).const_mul _, ?_⟩
  simp only [fineSelectedGeometryEnvelope, integral_const_mul, ← mul_assoc]
  gcongr

end

section
variable {d n : ℕ} [NeZero d]

theorem fineFieldGeometryEnvelope_integrable_and_le (hd : 3 ≤ d)
    (ad bd T0 N : ℝ) (hT0 : 0 < T0) (M q : ℕ) (C a ρ η : ℝ) :
    Integrable (fineFieldGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n*finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card)
  have hs (S) (hS : S ∈ s) := (Finset.mem_filter.mp hS).2.1
  have h := fineSelectedGeometryEnvelope_integrable_and_le (d := d) ad bd T0 N M q C a ρ η s _
    (fun S hS => finePairTimeSubsetMoment_square_integrable hd hT0 S (hs S hS))
    (finePairTimeSubsetMoment_sum_abs_square_integral_le hd (hi := N) hT0 s hs)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  unfold finePairEvenActionSpatialBudget
  ring

theorem finePairAliasGeometryEnvelope_integrable_and_le (hd : 4 < d)
    (ad bd T0 N : ℝ) (hT0 : 0 < T0) (hN : T0 ≤ N) (M q : ℕ) (C a ρ η : ℝ) :
    Integrable (finePairAliasGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n*finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hs (S) (hS : S ∈ s) := finePairTimeSubsetMoment_two_subset_square_integrable_and_le (d := d) hd hT0 hN S
    (Finset.mem_powersetCard.mp hS).2
  have hb := finite_sum_square_integral_le (fullSpatialPatchDesign d n) s
    (fun S U => |finePairTimeSubsetMoment T0 N U S|) _
    (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)
    (fun S hS => by simpa only [sq_abs] using (hs S hS).1)
    (fun S hS => by simpa only [sq_abs] using (hs S hS).2)
  have h := fineSelectedGeometryEnvelope_integrable_and_le ad bd T0 N M q C a ρ η s _
    (fun S hS => (hs S hS).1) hb
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp only [s, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, finePairAliasActionSpatialBudget]
  ring

end

section
variable {d n F : ℕ}
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
include haD hab hn hC ha hη hρ hηρ hU hpD hc hg hw hp

private theorem fineSelectedAction_sum_square_le_geometry (P : ℕ → Prop) [DecidablePred P] :
    (∑ y : Fin n → Fin 3, finePairSelectedAction P ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2) ≤
        fineSelectedGeometryEnvelope ad bd T0 N M q C a ρ η
          (Finset.univ.powerset.filter (fun W => P W.card)) U := by
  have H := highFrameResponseGuards (F := F) C a V η ρ hC ha hη hηρ U hU g w hg hw hp
  apply (ternary_sum_sq_le (fun y => finePairSelectedAction_abs_le P ad bd T0 N haD hab M q hn C a V η ρ
      U p g w hpD c hc H y)).trans_eq
  rw [fineSelectedGeometryEnvelope, mul_pow, mul_assoc]

theorem finePairPairAliasAction_sum_square_le_geometry :
    (∑ y : Fin n → Fin 3, finePairPairAliasAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2) ≤
        finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  rw [finePairAliasGeometryEnvelope, Finset.powersetCard_eq_filter]
  exact fineSelectedAction_sum_square_le_geometry ad bd T0 N haD hab M q hn C a V η ρ hC ha hη hρ hηρ
    U hU p g w hpD c hc hg hw hp (· = 2)

theorem finePairEvenFieldAction_sum_square_le_geometry :
    (∑ y : Fin n → Fin 3, finePairEvenFieldAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2) ≤
        fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U :=
  fineSelectedAction_sum_square_le_geometry ad bd T0 N haD hab M q hn C a V η ρ hC ha hη hρ hηρ
    U hU p g w hpD c hc hg hw hp (fun r => 4 ≤ r ∧ Even r)

end

 def finePairCountTwoGeometryEnvelope {d : ℕ} (bd a ρ η N : ℝ) (U : Fin 2 → Covariate d) : ℝ :=
  9*(η^2*bd^2*((2*ρ+a)/a^2)^2)^2*finePairDistanceFactor N (U 0) (U 1)^2

 section
variable {d : ℕ}

theorem finePairCountTwoGeometryEnvelope_nonneg (bd a ρ η N : ℝ)
    (U : Fin 2 → Covariate d) : 0 ≤ finePairCountTwoGeometryEnvelope bd a ρ η N U := by
  unfold finePairCountTwoGeometryEnvelope; positivity

 theorem finePairCountTwoGeometryEnvelope_integrable_and_le (hd : 0 < d)
    (bd a ρ η : ℝ) {N : ℝ} (hN : 0 < N) :
    Integrable (finePairCountTwoGeometryEnvelope (d := d) bd a ρ η N) (fullSpatialPatchDesign d 2) ∧
    (∫ U, finePairCountTwoGeometryEnvelope bd a ρ η N U ∂fullSpatialPatchDesign d 2) ≤
      9*finePairCountTwoSpatialBudget d bd a ρ η N := by
  have h := finePairDistanceFactor_square_moments hd hN
  have hm := fullSpatialPatchDesign_pair_moments h.1 h.2
  refine ⟨hm.1.const_mul _, ?_⟩
  unfold finePairCountTwoGeometryEnvelope
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hm.2 (by positivity : 0 ≤ 9*(η^2*bd^2*((2*ρ+a)/a^2)^2)^2)).trans_eq
    (by unfold finePairCountTwoSpatialBudget; ring)

end
theorem finePairCountTwoRawNumerator_sum_square_le_geometry {d F : ℕ} [NeZero d] (hF : 3 ≤ F)
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η ρ : ℝ) (hC : C ≠ 0) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p g w : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ)
    (hf : ∀ i, |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ) :
    (∑ y : Fin 2 → Fin 3, (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y)^2) ≤
      finePairCountTwoGeometryEnvelope bd a ρ η N U :=
    by apply finePairCountTwoRawNumerator_sum_square_le <;> assumption

end NearlyMinimax
