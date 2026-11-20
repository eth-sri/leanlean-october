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
theorem signedDensity_integral (w : X → ℝ) (hw : Integrable w μ) (hmw : Measurable w)
    (f : X → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ x, ‖f x‖ ≤ M) :
    (∫ᵛ x, f x ∂<•(μ.withDensityᵥ w)) = ∫ x, w x * f x ∂μ := by
  let μp := μ.withDensity (fun x => ENNReal.ofReal (w x))
  let μn := μ.withDensity (fun x => ENNReal.ofReal (-w x))
  letI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  letI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hw.neg.hasFiniteIntegral
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
  dsimp only [μp, μn]
  have hmn : Measurable (fun x => ENNReal.ofReal (-w x)) := hmw.neg.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmw.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hmn
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hpf := hw.pos_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hnf := hw.neg_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [← integral_sub hpf hnf]
  exact integral_congr_ae (.of_forall fun x => by
    dsimp only
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self])

end SignedDensity

section FiniteProduct
variable {Z I : Type*} [MeasurableSpace Z] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

theorem joint_finite_integrable (σ : Measure Z) [IsFiniteMeasure σ] (f : Z × I → ℝ)
    (hf : ∀ i, Measurable (fun ζ => f (ζ, i)))
    (hi : ∀ i, Integrable (fun ζ => f (ζ, i)) σ) :
    Integrable f (σ.prod Measure.count) := by
  have hm := measurable_from_prod_countable_left hf
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun ζ => integrable_count_iff.mpr ((hasSum_fintype _).summable)), ?_⟩
  simp only [integral_count]
  exact integrable_finsetSum _ (fun i _ => (hi i).norm)

end FiniteProduct

abbrev HighDensityMarkIndex (m r D : ℕ) :=
  Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))

abbrev HighResponseMarkIndex (ι : Type*) (q : ℕ) := (ι × ι) × (Bool × Bool) × Fin (2 * q + 2)

abbrev HighPacketMarkIndex (ι : Type*) (m r D q : ℕ) :=
  HighDensityMarkIndex m r D × HighResponseMarkIndex ι q

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def highResponseMarkAtom (C : ℝ) (q : ℕ) (h : HighResponseMarkIndex ι q) :
    ℝ × (ι → ℝ) :=
  (responseNode q h.2.2, covarianceAtom C h.1.1 h.1.2 h.2.1.1 h.2.1.2)

def highResponseMarkWeight (C : ℝ) (q : ℕ) (A : ι → ι → ℝ)
    (h : HighResponseMarkIndex ι q) : ℝ :=
  responseWeight q h.2.2 * covarianceWeight C A h.1.1 h.1.2 h.2.1.1 h.2.1.2

section
variable (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)

theorem highResponseMark_action
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C q A h *
      Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)) =
      responseMatrixAction q C A c Φ := by
  simp only [Fintype.sum_prod_type, highResponseMarkWeight, highResponseMarkAtom,
    responseMatrixAction, covarianceAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  grind

theorem highResponseMark_variation :
    (∑ h : HighResponseMarkIndex ι q, |highResponseMarkWeight C q A h|) =
      (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) := by
  simp only [highResponseMarkWeight, Fintype.sum_prod_type, abs_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [covariance_weight_variation]

end

private theorem sum_prod_mul {I J : Type*} [Fintype I] [Fintype J] (f : I → ℝ) (g : J → ℝ) :
    (∑ h : I × J, f h.1 * g h.2) = (∑ i, f i) * ∑ j, g j := by
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-! A signed response packet is the tensor product of a finite density rule
and a matrix-weighted response rule. Both the ordinary and the fine-pair
packets use the same integration, cost, and cancellation identities. -/
section ResponsePacket
variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable (w : I → ℝ) (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)

/-- The shared observable on finite density and response marks. -/
def responsePacketObservable {X : Type*} (atom : I → X) (c : ι → ℝ)
    (G : Z → X → ℝ) (Φ : (ι → ℝ) → ℝ) (e : Z × (I × HighResponseMarkIndex ι q)) : ℝ :=
  G e.1 (atom e.2.1) *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)

def responsePacketWeight (e : Z × (I × HighResponseMarkIndex ι q)) : ℝ :=
  w e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2

section
variable (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
include hA

private theorem responsePacketWeight_slice_measurable (h : I × HighResponseMarkIndex ι q) :
    Measurable (fun ζ => responsePacketWeight w q C A (ζ,h)) := by
  dsimp [responsePacketWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop

theorem responsePacketWeight_measurable :
    Measurable (responsePacketWeight w q C A) :=
  measurable_from_prod_countable_left (responsePacketWeight_slice_measurable w q C A hA)

end

section
variable (σ : Measure Z) [IsFiniteMeasure σ]
    (hA : SeparatedMatrixIntegrable σ A)
include hA

theorem responsePacketWeight_integrable :
    Integrable (responsePacketWeight w q C A) (σ.prod Measure.count) := by
  apply joint_finite_integrable σ _ (responsePacketWeight_slice_measurable w q C A hA.meas)
  intro ⟨i,h⟩
  dsimp [responsePacketWeight, highResponseMarkWeight, covarianceWeight]
  exact (((((hA.entry h.1.1 h.1.2).const_mul
    (C ^ 2 / 2)).mul_const (fairSign h.2.1.1)).mul_const (fairSign h.2.1.2)).const_mul
      (responseWeight q h.2.2)).const_mul (w i)

private theorem responsePacket_signed_integral
    (F : Z × (I × HighResponseMarkIndex ι q) → ℝ)
    (hF : ∀ h, Measurable (fun ζ => F (ζ,h))) (M : ℝ) (hb : ∀ ζ h, ‖F (ζ,h)‖ ≤ M) :
    (∫ᵛ e, F e ∂<•((σ.prod Measure.count).withDensityᵥ (responsePacketWeight w q C A))) =
      ∫ ζ, ∑ h, responsePacketWeight w q C A (ζ,h) * F (ζ,h) ∂σ := by
  have hmw := responsePacketWeight_measurable w q C A hA.meas
  have hw := responsePacketWeight_integrable w q C A σ hA
  have hm := measurable_from_prod_countable_left hF
  rw [signedDensity_integral _ _ hw hmw F hm M (fun e => hb e.1 e.2),
    integral_prod _ (hw.mul_bdd hm.aestronglyMeasurable (.of_forall (fun e => hb e.1 e.2)))]
  simp only [integral_count]

theorem responsePacket_signed_integral_mul
    (f : Z → I → ℝ) (g : HighResponseMarkIndex ι q → ℝ)
    (hf : ∀ i, Measurable (fun ζ => f ζ i)) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ ζ i, |f ζ i| ≤ L) :
    (∫ᵛ e, f e.1 e.2.1 * g e.2.2
        ∂<•((σ.prod Measure.count).withDensityᵥ (responsePacketWeight w q C A))) =
      ∫ ζ, (∑ i, w i * f ζ i) * (∑ h, highResponseMarkWeight C q (A ζ) h * g h) ∂σ := by
  classical
  let M := ∑ h, |g h|
  have hg (h) : |g h| ≤ M := Finset.single_le_sum (fun j _ => abs_nonneg (g j)) (Finset.mem_univ h)
  rw [responsePacket_signed_integral w q C A σ hA _ (fun h => (hf h.1).mul_const (g h.2)) (L*M)
    (fun ζ h => by
      simpa using mul_le_mul (hb ζ h.1) (hg h.2) (abs_nonneg _) hL)]
  simp only [responsePacketWeight, mul_mul_mul_comm (w _)]
  congr 1
  funext ζ
  exact sum_prod_mul (fun i => w i * f ζ i) (fun h => highResponseMarkWeight C q (A ζ) h * g h)

end

/-- Factor a product of density resets before evaluating the response action. -/
theorem responsePacket_signed_integral_product {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {n : ℕ} (σ : Measure Z) [IsFiniteMeasure σ]
    (hA : SeparatedMatrixIntegrable σ A) (atom : I → X) (c : ι → ℝ)
    (f : Z → X → Fin n → ℝ) (hf : ∀ i u, Measurable (fun ζ => f ζ (atom i) u))
    {b : ℝ} (hb : 0 ≤ b) (hle : ∀ ζ i u, |f ζ (atom i) u| ≤ b) (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, responsePacketObservable q C atom c (fun ζ x => ∏ u, f ζ x u) Φ e
      ∂<•((σ.prod Measure.count).withDensityᵥ (responsePacketWeight w q C A))) =
      ∫ ζ, (∫ᵛ x, ∏ u, f ζ x u ∂<•atomicSignedRule atom w) * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  refine (responsePacket_signed_integral_mul w q C A σ hA
    (fun ζ i => ∏ u, f ζ (atom i) u)
    (fun h => Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1))
    (fun i => Finset.measurable_fun_prod _ fun u _ => hf i u) (pow_nonneg hb n)
    (fun ζ i => by simpa using abs_prod_le_pow (s := Finset.univ) (fun u _ => hle ζ i u))).trans ?_
  simp only [atomicSignedRule_integral, highResponseMark_action]

theorem responsePacket_signed_variation (σ : Measure Z) [IsFiniteMeasure σ]
    (hA : SeparatedMatrixIntegrable σ A) :
    ((((σ.prod Measure.count).withDensityᵥ (responsePacketWeight w q C A)).variation univ).toReal) =
      (∑ i, |w i|) * (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
        ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  have hw := responsePacketWeight_integrable w q C A σ hA
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable,
    integral_prod _ hw.norm, ← integral_const_mul]
  simp only [integral_count, Real.norm_eq_abs, responsePacketWeight, abs_mul]
  congr 1
  funext ζ
  rw [sum_prod_mul (fun i => |w i|) (fun h => |highResponseMarkWeight C q (A ζ) h|),
    highResponseMark_variation, separatedMatrixCost]
  ring

theorem responsePacketWeight_density_sum_zero (F : I → ℝ) (ζ : Z) :
    (∑ h : I × HighResponseMarkIndex ι q, responsePacketWeight w q C A (ζ,h) * F h.1) = 0 := by
  have hz : (∑ h, highResponseMarkWeight C q (A ζ) h) = 0 := by
    simpa only [mul_one, responseMatrixAction_zero_mass] using
      highResponseMark_action q C (A ζ) (fun _ => 0) (fun _ => 1)
  simp only [responsePacketWeight, mul_right_comm (w _)]
  rw [sum_prod_mul (fun i => w i * F i) (highResponseMarkWeight C q (A ζ)), hz, mul_zero]

theorem responsePacketWeight_integral_zero (σ : Measure Z) [IsFiniteMeasure σ]
    (hA : SeparatedMatrixIntegrable σ A) :
    (∫ e, responsePacketWeight w q C A e ∂σ.prod Measure.count) = 0 := by
  rw [integral_prod _ (responsePacketWeight_integrable w q C A σ hA)]
  simp only [integral_count]
  have hz (ζ : Z) := responsePacketWeight_density_sum_zero w q C A (fun _ => 1) ζ
  simp only [mul_one] at hz
  simp [hz]

end ResponsePacket

def highPacketMarkWeight (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  responsePacketWeight (densityPacketWeight a b m r D) q C A e

theorem highPacketMarkWeight_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) :
    Measurable (highPacketMarkWeight a b m r D q C A) :=
  responsePacketWeight_measurable _ q C A hA

theorem highPacketMarkWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A) :
    Integrable (highPacketMarkWeight a b m r D q C A) (σ.prod Measure.count) :=
  responsePacketWeight_integrable _ q C A σ hA

/-- The original joint Xi packet as a genuine signed measure, represented
on the finite atom indices together with the actual positive sigma mark. -/
def highPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × HighPacketMarkIndex ι m r D q) :=
  (σ.prod Measure.count).withDensityᵥ (highPacketMarkWeight a b m r D q C A)

def highPacketObservable (a b : ℝ) (m r D q : ℕ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  responsePacketObservable q C (densityPacketAtom a b m r D) c (fun ζ x => G ζ x.1 x.2) Φ e

/-- The signed action of a separated packet on a product of density resets. -/
def highPacketFirstAction {n : ℕ} (σ : Measure Z) (a b : ℝ) (m r D q : ℕ)
    (C : ℝ) (A : Z → ι → ι → ℝ) (c : ι → ℝ) (p : Fin n → ℝ)
    (B : Z → Fin n → Fin r → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable a b m r D q C c
    (fun ζ z ε => ∏ i, localDensityReset a b r z ε p (B ζ) i) Φ e
    ∂<•highPacketSignedMeasure σ a b m r D q C A

/-- Factor a product of density resets before evaluating the response action. -/
theorem highPacketSignedMeasure_product_integral {n : ℕ} (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : SeparatedMatrixIntegrable σ A)
    (c : ι → ℝ) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b)
    (B : Z → Fin n → Fin r → ℝ) (hBm : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hB : ∀ ζ i l, |B ζ i l| ≤ 1) (Φ : (ι → ℝ) → ℝ) :
    highPacketFirstAction σ a b m r D q C A c p B Φ =
      highSeparatedPacketAction σ a b m r D q C A c
        (fun ζ z ε => ∏ i, localDensityReset a b r z ε p (B ζ) i) Φ := by
  unfold highPacketFirstAction
  have h := responsePacket_signed_integral_product (densityPacketWeight a b m r D) q C A σ hA
    (densityPacketAtom a b m r D) c (fun ζ x i => localDensityReset a b r x.1 x.2 p (B ζ) i)
    (fun h i => measurable_const.add ((Finset.measurable_fun_sum _ fun l _ =>
      (hBm i l).const_mul ((densityPacketAtom a b m r D h).2 l)).const_mul _))
    (ha.trans hab).le (fun ζ h i => densityPacketReset_abs_le a b ha hab m r D hr h p _ i (hp i) (hB ζ i)) Φ
  refine h.trans ?_
  change (∫ ζ, (∫ᵛ e, ∏ i, localDensityReset a b r e.1 e.2 p (B ζ) i ∂<•densityPacketSignedRule a b m r D) *
      responseMatrixAction q C (A ζ) c Φ ∂σ) = _
  unfold highSeparatedPacketAction
  congr 1
  funext ζ
  rw [densityPacketSignedRule_integral a b m r D (fun z eps => ∏ i, localDensityReset a b r z eps p (B ζ) i)]

section
variable {n : ℕ} (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : SeparatedMatrixIntegrable σ A)
    (c : ι → ℝ) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b)
include ha hab hr hD hnD hA hp

theorem highPacketFirstAction_count_expansion
    (B : Z → Fin n → Fin r → ℝ) (hm : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hb : ∀ ζ i l, |B ζ i l| ≤ 1) (Φ : (ι → ℝ) → ℝ) :
    highPacketFirstAction σ a b m r D q C A c p B Φ =
      densityCountCoefficient a b m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C (separatedSubsetMatrix σ r B A S) c Φ := by
  rw [highPacketSignedMeasure_product_integral σ a b ha hab m r D q hr C A hA c p hp B hm hb Φ]
  simpa using highSeparatedPacketAction_row σ a b ha hab m r D q hr hD Finset.univ
    (by simpa using hnD) p B hm hb C A hA c Φ

/-- Columns that agree drop out of the permutation average, for every target count. -/
theorem highPacketFirstAction_identical_columns (hnm : n ≤ m)
    (ψ : Z → Fin n → ℝ) (hm : ∀ i, Measurable (fun ζ => ψ ζ i))
    (hb : ∀ ζ i, |ψ ζ i| ≤ 1) (Φ : (ι → ℝ) → ℝ) :
    highPacketFirstAction σ a b m r D q C A c p (fun ζ i _ => ψ ζ i) Φ =
      if n = r then
        (∏ i, p i) * ∫ ζ, (∏ i, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ ∂σ else 0 := by
  classical
  rw [highPacketSignedMeasure_product_integral σ a b ha hab m r D q hr C A hA c p hp _
    (fun i _ => hm i) (fun ζ i _ => hb ζ i) Φ]
  unfold highSeparatedPacketAction
  simp_rw [density_packet_product_count_selector (Finset.univ : Finset (Fin n)) a b ha hab m r D hr hD
    (by simpa using hnD) (by simpa using hnm), Finset.card_univ, Fintype.card_fin]
  split_ifs with h
  · subst r
    have hs : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    have hc (ζ : Z) : densitySeparatedSym n (fun i _ => ψ ζ i) Finset.univ = ∏ i, ψ ζ i := by
      rw [densitySeparatedSym_eq_permutation_average _ _ _ (Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)).symm]
      simp [Fintype.card_perm, Finset.sum_const, mul_div_cancel_left₀,
        show (n.factorial : ℝ) ≠ 0 by positivity]
    simp only [hs, Finset.sum_singleton, hc, mul_assoc, integral_const_mul]
  · simp []

end

section
variable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ)

/-- Exact raw-atom variation of Xi: the density packet cost, fixed scalar
response cost and signed covariance cost multiply the actual representation cost. -/
theorem highPacketSignedMeasure_totalVariation (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : SeparatedMatrixIntegrable σ A) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
          ∫ ζ, separatedMatrixCost A ζ ∂σ :=
  responsePacket_signed_variation _ q C A σ hA

theorem highPacketSignedMeasure_exponential_cost (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : SeparatedMatrixIntegrable σ A) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal ≤
      ((Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a)))) *
          (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
            ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  rw [highPacketSignedMeasure_totalVariation σ a b m r D q C A hA]
  have h := densityPacketWeight_exponential_cost a b ha hab m r D hr hD
  gcongr
  exact integral_nonneg fun ζ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

end

end Packet

end NearlyMinimax
