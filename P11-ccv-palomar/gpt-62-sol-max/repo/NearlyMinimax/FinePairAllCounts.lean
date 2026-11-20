module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.FinePairMatrixCost

@[expose] public section

/-! Genuine even-subset expansion of the fine density/response row.
The time-weighted field moments are integrals of the actual hyperplane law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def finePairEvenSelector (j : ℕ) : ℝ := if j = 0 then 0 else if Even j then 1 else 0

theorem finePairEvenSelector_split (j : ℕ) :
    finePairEvenSelector j = (if j = 2 then 1 else 0) +
      (if 4 ≤ j ∧ Even j then 1 else 0) := by
  grind [finePairEvenSelector]

section
variable {d n : ℕ}

section
variable (U : Fin n → Covariate d)
    (S : Finset (Fin n))

theorem finePairTimeField_product_measurable :
    Measurable (fun e : ℝ × FinePairFieldMark d => ∏ i ∈ S, finePairTimeFieldValue e (U i)) :=
  Finset.measurable_fun_prod S (fun i _ =>
    finePairTimeFieldValue_section_measurable (U i))

theorem finePairTimeField_product_abs (e : ℝ × FinePairFieldMark d) :
    |∏ i ∈ S, finePairTimeFieldValue e (U i)| = 1 := by
  rw [Finset.abs_prod]
  simp only [finePairTimeFieldValue_abs, Finset.prod_const_one]

end

theorem finePairTimeField_weighted_product_integrable [NeZero d]
    (lo hi : ℝ) (U : Fin n → Covariate d) (S : Finset (Fin n)) :
    Integrable (fun e : ℝ × FinePairFieldMark d =>
      e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i))) (finePairTimeFieldMeasure d lo hi) :=
  (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
    (finePairTimeField_product_measurable U S).aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, finePairTimeField_product_abs])

end

def finePairTimeSubsetMoment {d n : ℕ} (lo hi : ℝ) (U : Fin n → Covariate d)
    (S : Finset (Fin n)) : ℝ :=
  ∫ e : ℝ × FinePairFieldMark d,
    e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i)) ∂finePairTimeFieldMeasure d lo hi

theorem finePairTimeSubsetMoment_actual {d n : ℕ} [NeZero d]
    (lo hi : ℝ) (U : Fin n → Covariate d) (S : Finset (Fin n)) :
    finePairTimeSubsetMoment lo hi U S =
      ∫ T in Icc lo hi, T * (∫ z, ∏ i ∈ S, boundedHyperplaneFieldValue z (U i)
        ∂boundedHyperplaneFieldLaw d T) := by
  rw [finePairTimeSubsetMoment, finePairTimeFieldMeasure_integral d lo hi _
    (finePairTimeField_weighted_product_integrable lo hi U S)]
  simp only [finePairTimeFieldValue, integral_const_mul]

section Generic
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

theorem finePairPacket_even_subset_expansion {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A) (c : ι → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => ∏ i, finePairDensityReset a b z eps p (ψ ζ) i) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient a b M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card *
          (∫ ζ, (∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  rw [finePairPacketSignedMeasure_product_integral σ a b ha hab M q C A hA c p hp ψ hmψ hbψ]
  have hiRsp :=
    responseMatrixAction_integrable σ q C A (hA.entry) c Φ
  have hi (W : Finset (Fin n)) :
      Integrable (fun ζ => (∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) σ := by
    apply hiRsp.bdd_mul (c := 1)
      (Finset.measurable_fun_prod W (fun i _ => hmψ i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ζ => by
      simpa using (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hbψ ζ i)).trans_eq
              (Finset.prod_const_one)
  have hsubset (ζ : Z) :
      (∫ᵛ e, (∏ i, finePairDensityReset a b e.1 e.2 p (ψ ζ) i)
        ∂<•finePairDensitySignedRule a b M) =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient a b M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) *
          finePairEvenSelector W.card := by
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, finePairEvenSelector] using
      finePairDensitySignedRule_product_expansion a b M Finset.univ p (ψ ζ)
  simp_rw [hsubset]
  have he (W : Finset (Fin n)) (ζ : Z) :
      finePairCountCoefficient a b M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) *
        finePairEvenSelector W.card * responseMatrixAction q C (A ζ) c Φ =
      (finePairCountCoefficient a b M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card) *
        ((∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [Finset.sum_mul, he]
  rw [integral_finsetSum _ (fun W _ => (hi W).const_mul _)]
  simp only [integral_const_mul]

end Generic

theorem finePairFineFirstAction_even_subset_expansion {d n F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd T0 N M q C U p c Φ =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card *
          finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by
  rw [finePairFineFirstAction, finePairPacket_even_subset_expansion _ ad bd ha hab M q C _
    (finePairTimeMatrix_integrable d T0 N _)
    c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
    (fun i => finePairTimeFieldValue_section_measurable (U i))
    (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le)]
  apply Finset.sum_congr rfl
  intro W _
  change _ * (∫ e : ℝ × FinePairFieldMark d, (∏ i ∈ W, finePairTimeFieldValue e (U i)) *
    responseMatrixAction q C (fun i j => e.1 * finePairDistanceMatrix d F i j) c Φ
    ∂finePairTimeFieldMeasure d T0 N) = _
  simp_rw [responseMatrixAction_scalar_matrix]
  have he (e : ℝ × FinePairFieldMark d) :
      (∏ i ∈ W, finePairTimeFieldValue e (U i)) *
        (e.1 * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) =
      (e.1 * (∏ i ∈ W, finePairTimeFieldValue e (U i))) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by ring
  simp_rw [he]
  rw [integral_mul_const]
  unfold finePairTimeSubsetMoment
  ring

/-- The pair alias and the higher even field are the same localized response
contraction on different families of subsets. -/
def finePairSelectedAction {d n F : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
    finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * (if P W.card then 1 else 0) *
      finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ

abbrev finePairPairAliasAction {d n F : ℕ} :=
  finePairSelectedAction (d := d) (n := n) (F := F) (· = 2)

noncomputable abbrev finePairEvenFieldAction {d n F : ℕ} :=
  finePairSelectedAction (d := d) (n := n) (F := F) (fun r => 4 ≤ r ∧ Even r)

section
variable {d n F : ℕ}

theorem finePairFineFirstAction_alias_even_field [NeZero d]
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd T0 N M q C U p c Φ =
      finePairPairAliasAction ad bd T0 N M q C U p c Φ +
        finePairEvenFieldAction ad bd T0 N M q C U p c Φ := by
  rw [finePairFineFirstAction_even_subset_expansion ad bd T0 N ha hab M q C U p hp c Φ]
  simp only [finePairEvenSelector_split, finePairPairAliasAction, finePairEvenFieldAction, finePairSelectedAction,
    mul_add, add_mul, Finset.sum_add_distrib]

theorem finePairPairAliasAction_zero_selected_count
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ)
    (hn : 3 ≤ n) (hM : n ≤ M) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairPairAliasAction ad bd T0 N M q C U p c Φ = 0 := by
  unfold finePairPairAliasAction finePairSelectedAction
  apply Finset.sum_eq_zero
  intro W _
  by_cases hW : W.card = 2
  · simp [hW, finePairCountCoefficient_two_exact ad bd ha hab M n (by omega) hM] <;> omega
  · simp [hW]

end

end NearlyMinimax
