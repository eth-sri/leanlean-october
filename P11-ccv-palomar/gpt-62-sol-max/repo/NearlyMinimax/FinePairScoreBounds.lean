module

public import NearlyMinimax.FinePairHyperplanePacket
public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.SpatialLaplaceTail

@[expose] public section

/-! Exact count-two action of the genuine three source fine-pair rows.
The density selectors and the Lebesgue/field carrier are evaluated before
the single response variance correction is applied. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem finePairDensity_action_small_count {n : ℕ} (hn : n < 2) (a b : ℝ) (M : ℕ)
    (p ψ : Fin n → ℝ) :
    (∫ᵛ e, (∏ i, finePairDensityReset a b e.1 e.2 p ψ i)
      ∂<•finePairDensitySignedRule a b M) = 0 := by
  rw [finePairDensitySignedRule_product_expansion]
  apply Finset.sum_eq_zero
  intro W hW
  have hWn := Finset.card_le_card (Finset.mem_powerset.mp hW)
  simp only [Finset.card_univ, Fintype.card_fin] at hWn
  have hpar : W.card = 0 ∨ ¬Even W.card := by grind
  rcases hpar with h | h <;> simp [h]

theorem finePairTime_response_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) [NeZero d] (lo hi : ℝ) (hlo : 0 ≤ lo)
    (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d)
    (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∫ e, finePairTimeFieldValue e u * finePairTimeFieldValue e v *
      responseMatrixAction q C (finePairTimeMatrix d A e) c Φ
      ∂finePairTimeFieldMeasure d lo hi) =
      (∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm (fun r => u r - v r))) *
        responseMatrixAction q C A c Φ := by
  change (∫ e, finePairTimeFieldValue e u * finePairTimeFieldValue e v *
    responseMatrixAction q C (fun i j => e.1 * A i j) c Φ
    ∂finePairTimeFieldMeasure d lo hi) = _
  simp_rw [responseMatrixAction_scalar_matrix]
  have he (e : ℝ × FinePairFieldMark d) : finePairTimeFieldValue e u * finePairTimeFieldValue e v *
      (e.1 * responseMatrixAction q C A c Φ) =
      (e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)) *
        responseMatrixAction q C A c Φ := by ring
  simp [he, integral_mul_const, finePairTimeFieldValue_weighted_covariance d lo hi hlo u v hu hv]

theorem pairLaplaceKernel_split {T0 N : ℝ} (hT0 : 0 ≤ T0) (hN : T0 ≤ N) (r : ℝ) :
    (∫ T in Icc 0 T0, T * Real.exp (-(T*r))) +
      (∫ T in Icc T0 N, T * Real.exp (-(T*r))) = pairLaplaceKernel N r := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT0, ← intervalIntegral.integral_of_le hN]
  exact intervalIntegral.integral_add_adjacent_intervals
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)

theorem responseMatrixAction_matrix_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : ℝ) (A B : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => A i j + B i j) c Φ =
      responseMatrixAction q C A c Φ + responseMatrixAction q C B c Φ := by
  simp only [responseMatrixAction_entry_sum, add_mul, Finset.sum_add_distrib]

section ActualRows
variable {d F : ℕ} [NeZero d]

def finePairUnitFirstAction {n : ℕ} (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  highPacketFirstAction (Measure.dirac ()) ad bd D 2 D q C
    (fun _ => finePairUnitMatrix d F) c p (fun _ _ _ => 1) Φ

def finePairCoarseFirstAction {n : ℕ} (ad bd T0 : ℝ) (D q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  highPacketFirstAction (finePairTimeFieldMeasure d 0 T0) ad bd D 2 D q C
    (finePairTimeMatrix d (finePairDistanceMatrix d F)) c p
    (fun ζ i _ => finePairTimeFieldValue ζ (U i)) Φ

def finePairFineFirstAction {n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, finePairPacketObservable ad bd M q C c
    (fun ζ z eps => ∏ i, finePairDensityReset ad bd z eps p
      (fun i => finePairTimeFieldValue ζ (U i)) i) Φ e
    ∂<•finePairPacketSignedMeasure (finePairTimeFieldMeasure d T0 N) ad bd M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d F))

def finePairThreeRowFirstAction {n : ℕ} (ad bd T0 N : ℝ) (D M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  finePairUnitFirstAction ad bd D q C p c Φ + finePairCoarseFirstAction ad bd T0 D q C U p c Φ +
    finePairFineFirstAction ad bd T0 N M q C U p c Φ

section
variable {n : ℕ}

theorem finePairUnitFirstAction_count (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (C : ℝ) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairUnitFirstAction ad bd D q C p c Φ =
      if n = 2 then (∏ i, p i) * responseMatrixAction q C (finePairUnitMatrix d F) c Φ else 0 := by
  rw [finePairUnitFirstAction, highPacketFirstAction_identical_columns (Measure.dirac ()) ad bd ha hab
    D 2 D q (by omega) hD hnD C _ (SeparatedMatrixIntegrable.const _ _) c p hp hnD
    (fun _ _ => 1) (fun _ => measurable_const) (by simp)]
  simp

theorem finePairCoarseFirstAction_count (ad bd T0 : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (C : ℝ) (U : Fin n → Covariate d)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairCoarseFirstAction ad bd T0 D q C U p c Φ =
      if n = 2 then (∏ i, p i) * (∫ ζ, (∏ i, finePairTimeFieldValue ζ (U i)) *
        responseMatrixAction q C (finePairTimeMatrix d (finePairDistanceMatrix d F) ζ) c Φ
        ∂finePairTimeFieldMeasure d 0 T0) else 0 :=
  highPacketFirstAction_identical_columns _ ad bd ha hab D 2 D q (by omega) hD hnD C _
    (finePairTimeMatrix_integrable d 0 T0 _) c p hp hnD (fun ζ i => finePairTimeFieldValue ζ (U i))
    (fun i => finePairTimeFieldValue_section_measurable (U i)) (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ

theorem finePairFineFirstAction_integral (ad bd lo hi : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd lo hi M q C U p c Φ =
      ∫ ζ, (∫ᵛ e, ∏ i, finePairDensityReset ad bd e.1 e.2 p (fun i => finePairTimeFieldValue ζ (U i)) i
        ∂<•finePairDensitySignedRule ad bd M) *
        responseMatrixAction q C (finePairTimeMatrix d (finePairDistanceMatrix d F) ζ) c Φ
          ∂finePairTimeFieldMeasure d lo hi :=
  finePairPacketSignedMeasure_product_integral _ ad bd ha hab M q C _ (finePairTimeMatrix_integrable d lo hi _)
    c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
    (fun i => finePairTimeFieldValue_section_measurable (U i)) (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ

end

section
variable (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (hT0 : 0 ≤ T0)
include ha hab hT0

theorem finePairThreeRowFirstAction_pair (hN : T0 ≤ N) (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M)
    (C : ℝ) (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ = (p 0 * p 1) *
      responseMatrixAction q C
        (finePairCombinedMatrix d F (pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)))) c Φ := by
  rw [finePairThreeRowFirstAction,
    finePairUnitFirstAction_count ad bd ha hab D q (by omega) hD C p hp,
    finePairCoarseFirstAction_count ad bd T0 ha hab D q (by omega) hD C U p hp,
    finePairFineFirstAction_integral ad bd T0 N ha hab M q C U p hp]
  simp only [ite_true, Fin.prod_univ_two]
  have he (u v r : ℝ) : p 0 * p 1 * u * v * r = (p 0 * p 1) * (u * v * r) := by ring
  simp_rw [finePairDensitySignedRule_pair_exact ad bd ha hab M hM, he]
  rw [integral_const_mul,
    finePairTime_response_integral d 0 T0 (le_refl 0) (U 0) (U 1) (hU 0) (hU 1),
    finePairTime_response_integral d T0 N hT0 (U 0) (U 1) (hU 0) (hU 1)]
  change _ = (p 0 * p 1) * responseMatrixAction q C
    (fun i j => finePairUnitMatrix d F i j +
      pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)) * finePairDistanceMatrix d F i j) c Φ
  rw [responseMatrixAction_matrix_add, responseMatrixAction_scalar_matrix]
  rw [exactEuclideanDistance_eq_euclideanNorm]
  have hsplit := pairLaplaceKernel_split hT0 hN (euclideanNorm (fun r => U 0 r - U 1 r))
  grind

end

theorem finePairThreeRow_count_two_numerator (hF : 3 ≤ F)
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2 * (p 0 * p 1) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i =
      η^2 * w 0 * w 1 * p 0 * p 1 *
        ((1 + N * exactEuclideanDistance (U 0) (U 1)) *
          Real.exp (-(N * exactEuclideanDistance (U 0) (U 1)))) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  rw [finePairThreeRowFirstAction_pair ad bd T0 N ha hab hT0 hN D M q hD hM C U hU p hp,
    finePairResponseCountTwo_numerator hF q hq C a V η _ hC U p g w c y]
  have hr : 0 ≤ exactEuclideanDistance (U 0) (U 1) := Real.sqrt_nonneg _
  have hsq : (exactEuclideanDistance (U 0) (U 1))^2 = spatialSquaredDistance (U 0) (U 1) :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [← hsq, mul_comm (pairLaplaceKernel _ _), pairLaplaceKernel_defect N _ hr]

theorem finePairThreeRowFirstAction_small_count {n : ℕ} (hn : n < 2)
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (D M q : ℕ) (hD : 1 ≤ D)
    (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ = 0 := by
  have hnD : n ≤ D := by omega
  simp [finePairThreeRowFirstAction, finePairUnitFirstAction_count ad bd ha hab D q hD hnD C p hp,
    finePairCoarseFirstAction_count ad bd T0 ha hab D q hD hnD C U p hp,
    finePairFineFirstAction_integral ad bd T0 N ha hab M q C U p hp, show n ≠ 2 by omega,
    finePairDensity_action_small_count hn ad bd M]

end ActualRows

end NearlyMinimax
