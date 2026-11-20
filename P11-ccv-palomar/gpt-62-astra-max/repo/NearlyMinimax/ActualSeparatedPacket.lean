module

public import NearlyMinimax.HighSeparatedRows
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The actual joint signed measure of density, separated-representation,
and response marks used by the high-smoothness local update. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section SignedDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Integration against an actual real weighted signed measure, for a
bounded measurable observable. The signed-density integral identity is
derived from its positive and negative parts. -/
theorem signedDensity_integral {w : X → ℝ} (hw : Integrable w μ) (hmw : Measurable w)
    {f : X → ℝ} (hf : Measurable f) (M : ℝ) (hbound : ∀ x, ‖f x‖ ≤ M) :
    (∫ᵛ x, f x ∂<•(μ.withDensityᵥ w)) = ∫ x, w x * f x ∂μ := by
  let μp := μ.withDensity (fun x => ENNReal.ofReal (w x))
  let μn := μ.withDensity (fun x => ENNReal.ofReal (-w x))
  letI  := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  letI  := isFiniteMeasure_withDensity_ofReal hw.neg.hasFiniteIntegral
  have hp : Integrable f μp := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hn : Integrable f μn := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hpv : μp.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hp
  have hnv : μn.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hn
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hw,
    VectorMeasure.integral_sub_vectorMeasure hpv hnv, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  have hmn : Measurable (fun x => ENNReal.ofReal (-w x)) := hmw.neg.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmw.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hmn
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp [ENNReal.toReal_ofReal', smul_eq_mul]
  have hpf := hw.pos_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hnf := hw.neg_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [← integral_sub hpf hnf]
  grind

end SignedDensity

section FiniteProduct
variable {Z I : Type*} [MeasurableSpace Z] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

theorem joint_finite_integrable {σ : Measure Z} [IsFiniteMeasure σ] {f : Z × I → ℝ}
    (hf : ∀ i, Measurable (fun ζ => f (ζ, i)))
    (hi : ∀ i, Integrable (fun ζ => f (ζ, i)) σ) :
    Integrable f (σ.prod Measure.count) := by
  have hm  := measurable_from_prod_countable_left hf
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun ζ => Integrable.of_finite), ?_⟩
  simp
  exact integrable_finsetSum _ (fun i _ => (hi i).norm)

theorem signedDensity_finite_integral {σ : Measure Z} [IsFiniteMeasure σ] {w f : Z × I → ℝ}
    (hw : Integrable w (σ.prod Measure.count)) (hmw : Measurable w)
    (hf : ∀ i, Measurable (fun z => f (z,i))) (L : ℝ) (hb : ∀ z i, ‖f (z,i)‖ ≤ L) :
    (∫ᵛ e, f e ∂<•(σ.prod Measure.count).withDensityᵥ w) = ∫ z, ∑ i, w (z,i) * f (z,i) ∂σ := by
  have hm := measurable_from_prod_countable_left hf
  have hB (e : Z × I) := hb e.1 e.2
  rw [signedDensity_integral _ hw hmw hm L hB,
    integral_prod _ (hw.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hB))]
  simp

end FiniteProduct

section
variable (ι : Type*) (m r D q : ℕ)

abbrev HighDensityMarkIndex :=
  Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))

abbrev HighResponseMarkIndex := (ι × ι) × (Bool × Bool) × Fin (2 * q + 2)

abbrev HighPacketMarkIndex :=
  HighDensityMarkIndex m r D × HighResponseMarkIndex ι q

end

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

section
variable {σ : Measure Z} (a b : ℝ) (m r D q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (h : HighPacketMarkIndex ι m r D q)

def highResponseMarkAtom {q : ℕ} (h : HighResponseMarkIndex ι q) :
    ℝ × (ι → ℝ) :=
  (responseNode h.2.2, covarianceAtom C h.1.1 h.1.2 h.2.1.1 h.2.1.2)

def highResponseMarkWeight {q : ℕ} (A : ι → ι → ℝ)
    (h : HighResponseMarkIndex ι q) : ℝ :=
  responseWeight h.2.2 * covarianceWeight C A h.1.1 h.1.2 h.2.1.1 h.2.1.2

abbrev responseTensorWeight {I : Type*} (w : I → ℝ) (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (e : Z × I × HighResponseMarkIndex ι q) : ℝ :=
  w e.2.1 * highResponseMarkWeight C (A e.1) e.2.2

abbrev highPacketMarkWeight
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  responseTensorWeight (densityPacketWeight a b m r D) q C A e

end

/- Tensoring any finite density selector with the *same* response rule gives
one joint weight. Its measurability, integrability and exact variation need
no assumptions about how the density atoms are constructed. -/
section Tensor
variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {σ : Measure Z} (w : I → ℝ) (q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)

include hA in
private theorem tensorWeight_slice (h : I × HighResponseMarkIndex ι q) :
    Measurable (fun ζ => responseTensorWeight w q C A (ζ,h)) := by
  dsimp [responseTensorWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop

include hA in
theorem tensorWeight_measurable : Measurable (responseTensorWeight w q C A) :=
  measurable_from_prod_countable_left (tensorWeight_slice w q C hA)

include hA hcost in
theorem tensorWeight_integrable [IsFiniteMeasure σ] :
    Integrable (responseTensorWeight w q C A) (σ.prod Measure.count) := by
  apply joint_finite_integrable (tensorWeight_slice w q C hA)
  intro h
  exact (((((separatedMatrix_entry_integrable hA hcost h.2.1.1 h.2.1.2).const_mul
    (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul
      (responseWeight h.2.2.2)).const_mul (w h.1)

theorem highResponseMark_variation (A : ι → ι → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, |highResponseMarkWeight C A h|) =
      responseVariation q * (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) := by
  simp only [highResponseMarkWeight, Fintype.sum_prod_type, abs_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [covariance_weight_variation]

include hA hcost in
theorem tensorWeight_variation [IsFiniteMeasure σ] :
    (((σ.prod Measure.count).withDensityᵥ (responseTensorWeight w q C A)).variation univ).toReal =
      (∑ i, |w i|) * responseVariation q * (2*C^2) * ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  have hw := tensorWeight_integrable w q C hA hcost
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable, integral_prod _ hw.norm]
  simp only [integral_count, Real.norm_eq_abs, Fintype.sum_prod_type (f := fun h : I × HighResponseMarkIndex ι q => _), responseTensorWeight, abs_mul]
  simp_rw [← Finset.mul_sum, highResponseMark_variation, ← Finset.sum_mul]
  simp only [← mul_assoc, separatedMatrixCost, integral_const_mul]

end Tensor

section
variable {σ : Measure Z} (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : ι → ι → ℝ)

/-- The original joint Xi packet as a genuine signed measure, represented
on the finite atom indices together with the actual positive sigma mark. -/
def highPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × HighPacketMarkIndex ι m r D q) :=
  (σ.prod Measure.count).withDensityᵥ (highPacketMarkWeight a b m r D q C A)

theorem highResponseMark_action
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C A h *
      Φ (coefficientReset c (highResponseMarkAtom C h).2 (highResponseMarkAtom C h).1)) =
      responseMatrixAction q C A c Φ := by
  simp only [Fintype.sum_prod_type, highResponseMarkWeight, highResponseMarkAtom,
    responseMatrixAction, covarianceAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro h _
  ring

def highPacketObservable {m r D q : ℕ} (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  G e.1 (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom a b m r D e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C e.2.2).2 (highResponseMarkAtom C e.2.2).1)

theorem highPacketObservable_finite_action
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : HighPacketMarkIndex ι m r D q,
      highPacketMarkWeight a b m r D q C A (ζ, h) * highPacketObservable a b C c G Φ (ζ, h)) =
      densityPacketAction a b m r D (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) := by
  rw [Fintype.sum_prod_type]
  have he (h : HighDensityMarkIndex m r D) :
      (∑ v : HighResponseMarkIndex ι q,
        highPacketMarkWeight a b m r D q C A (ζ, (h, v)) *
          highPacketObservable a b C c G Φ (ζ, (h, v))) =
      densityPacketWeight a b m r D h *
        (G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2 *
          responseMatrixAction q C (A ζ) c Φ) := by
    rw [← highResponseMark_action q C (A ζ) c Φ]
    simp only [Finset.mul_sum, highPacketMarkWeight, responseTensorWeight, highPacketObservable]
    apply Finset.sum_congr rfl
    intro v _
    ring
  simp_rw [he]
  have hi := densityPacketSignedRule_integral a b m r D
    (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ)
  rw [densityPacketSignedRule, atomicSignedRule_integral] at hi
  exact hi

/-- The joint signed integral equals the actual iterated Xi action used
in the local-row theorem. -/
theorem highPacketSignedMeasure_factor_integral [IsFiniteMeasure σ]
    (a b : ℝ) (m r D : ℕ) {q : ℕ} {C : ℝ} {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    {c : ι → ℝ} (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) {L : ℝ} (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L)
    {Φ : (ι → ℝ) → ℝ} {M : ℝ}
    (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C h).2 (highResponseMarkAtom C h).1)| ≤ M) :
    (∫ᵛ e, highPacketObservable a b C c G Φ e
      ∂<•(highPacketSignedMeasure σ a b m r D q C A)) =
      highSeparatedPacketAction σ a b m r D q C A c G Φ := by
  have hmF (h : HighPacketMarkIndex ι m r D q) :
      Measurable (fun ζ => highPacketObservable a b C c G Φ (ζ, h)) := by
    change Measurable (fun ζ => G ζ (densityPacketAtom a b m r D h.1).1
      (densityPacketAtom a b m r D h.1).2 *
        Φ (coefficientReset c (highResponseMarkAtom C h.2).2 (highResponseMarkAtom C h.2).1))
    fun_prop
  rw [highPacketSignedMeasure, signedDensity_finite_integral (w := highPacketMarkWeight a b m r D q C A)
    (tensorWeight_integrable _ q C hA hcost) (tensorWeight_measurable _ q C hA) hmF (L * M)]
  · simp only [highPacketObservable_finite_action, highSeparatedPacketAction]
  · intro ζ h
    rw [highPacketObservable, Real.norm_eq_abs, abs_mul]
    bound

end

section
variable {σ : Measure Z} {a b : ℝ} (ha : 0 < a) (hab : a < b) (m r D : ℕ) (hr : 1 ≤ r)

/-- Exact raw-atom variation of Xi: the density packet cost, fixed scalar
response cost and signed covariance cost multiply the actual representation cost. -/
theorem highPacketSignedMeasure_totalVariation [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        responseVariation q * (2 * C ^ 2) *
          ∫ ζ, separatedMatrixCost A ζ ∂σ :=
  tensorWeight_variation (densityPacketWeight a b m r D) q C hA hcost

include hab hr in
theorem densityPacketAtom_injective : Function.Injective (densityPacketAtom a b m r D) := by
  intro e f he
  apply Prod.ext
  · exact (exteriorNode_strictAnti hab (m + r) (by omega)).injective (congrArg Prod.fst he)
  · funext l
    exact (lobattoNode_strictAnti (derivativeOrder D) (by unfold derivativeOrder; omega)).injective
      (congrArg (fun e : ℝ × (Fin r → ℝ) => e.2 l) he)

include ha hab hr in
theorem densityPacketWeight_exponential_cost (hD : 1 ≤ D) :
    (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) ≤
      (Real.exp (1 + intervalExteriorTau a b) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * intervalExteriorTau a b) := by
  have he := atomicSignedRule_totalVariation_eq
    (densityPacketWeight a b m r D) (densityPacketAtom_injective hab m r D hr)
  rw [← he]
  solve_by_elim [densityPacketSignedRule_exponential_cost]

theorem highPacketSignedMeasure_exponential_cost [IsFiniteMeasure σ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (C : ℝ) {A : Z → ι → ι → ℝ} (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal ≤
      ((Real.exp (1 + intervalExteriorTau a b) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * intervalExteriorTau a b)) *
          responseVariation q * (2 * C ^ 2) *
            ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  rw [highPacketSignedMeasure_totalVariation a b m r D q C hA hcost]
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (densityPacketWeight_exponential_cost ha hab m r D hr hD)
        (by positivity)
    · positivity
  · apply integral_nonneg
    intro ζ
    exact Finset.sum_nonneg (fun i _ => by positivity)

end

end Packet

end NearlyMinimax
