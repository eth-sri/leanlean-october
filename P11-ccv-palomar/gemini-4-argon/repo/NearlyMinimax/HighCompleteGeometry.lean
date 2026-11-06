module
public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighUnionScorePrimitives
public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.AliasTailSummation
public import NearlyMinimax.HigherBandFamilyCollapse
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
section
section
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
end
section Reference
variable {ι J Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace Z]
def responseTensorWeight (q ) (C : ℝ) (weights : J → ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × (J × HighResponseMarkIndex ι q)) : ℝ :=
  weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2
theorem responseTensor_reference_all_count_bound {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (weights : J → ℝ) (A : Z → ι → ι → ℝ)
    (hm : Measurable (responseTensorWeight q C weights A))
    (hi : Integrable (responseTensorWeight q C weights A) (σ.prod Measure.count))
    (hpos : 0 < signedMarkMass (σ.prod Measure.count) (responseTensorWeight q C weights A))
    (pReset : Z → J → Fin n → ℝ)
    (hmReset : ∀ e i, Measurable (fun ζ => pReset ζ e i))
    (hReset : ∀ ζ e i, |pReset ζ e i| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (y : Fin n → Fin 3) :
    |highMarkedResponseAction
      (absoluteMarkLaw (σ.prod Measure.count) (responseTensorWeight q C weights A))
      (absoluteActivation (σ.prod Measure.count) (responseTensorWeight q C weights A)) a V η
      (fun e => pReset e.1 e.2.1)
      (fun e => coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
      g w φ y| ≤
      pPlus^n * highSeparatedDerivativeBudget a ρ * ↑n^2 * η^2 *
        signedMarkMass (σ.prod Measure.count) (responseTensorWeight q C weights A) := by
  let ν : Measure (Z × (J × HighResponseMarkIndex ι q)) := σ.prod Measure.count
  let W := responseTensorWeight q C weights A
  let Φ : (ι → ℝ) → ℝ := fun v => highResponseProduct a V η g w φ v y
  let O : Z × (J × HighResponseMarkIndex ι q) → ℝ := fun e => (∏ i, pReset e.1 e.2.1 i) *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
  let K := pPlus^n * highSeparatedDerivativeBudget a ρ * ↑n^2 * η^2
  have hResetJoint (i) : Measurable (fun e : Z × (J × HighResponseMarkIndex ι q) => pReset e.1 e.2.1 i) :=
    measurable_from_prod_countable_left (fun e => hmReset e.1 i)
  have hCoef (γ) : Measurable (fun e : Z × (J × HighResponseMarkIndex ι q) =>
      coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1 γ) :=
    (measurable_of_countable (fun e : J × HighResponseMarkIndex ι q =>
      coefficientReset c (highResponseMarkAtom C q e.2).2 (highResponseMarkAtom C q e.2).1 γ)).comp measurable_snd
  have hO : Measurable O := (Finset.measurable_fun_prod _ (fun i _ => hResetJoint i)).mul
    (highMarkedResponseProduct_measurable a V η _ hCoef g w φ y)
  have hΦ (r : HighResponseMarkIndex ι q) :
      |Φ (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1)| ≤ 1 := by
    have hb := coefficientReset_mem_ball C c (highResponseMarkAtom C q r).2
      (highResponseMarkAtom C q r).1 (responseNode_mem_unit q r.2.2) hc
      (covarianceAtom_mem_ball C hC _ _ _ _)
    apply highMarkedResponseProduct_abs_le_one a V η ha.ne' g w φ _
    intro i b
    apply hp _
    have hprof := hφ _ hb i
    change |g i+η*w i*(∑ γ, φ i γ*coefficientReset c
      (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1 γ)| ≤ ρ
    have hh : |η*w i*(∑ γ, φ i γ*coefficientReset c
        (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1 γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hη]
      have := mul_le_mul (hw i) hprof (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left this hη]
    exact (abs_add_le _ _).trans (by linarith [hg i])
  have hOb (e) : ‖O e‖ ≤ pPlus^n := by
    change |(∏ i, pReset e.1 e.2.1 i)*Φ _| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ pPlus hpPlus (hReset e.1 e.2.1))
      (hΦ e.2.2) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hWO := hi.mul_bdd hO.aestronglyMeasurable (Filter.Eventually.of_forall hOb)
  have hSlice (ζ) : |∫ e : J × HighResponseMarkIndex ι q, W (ζ,e)*O (ζ,e) ∂Measure.count| ≤
      K * ∫ e : J × HighResponseMarkIndex ι q, |W (ζ,e)| ∂Measure.count := by
    simp only [integral_count]
    have h_responseTensor_slice_all_count_bound : |∑ e : J × HighResponseMarkIndex ι q,
      weights e.1 * highResponseMarkWeight C q (A ζ) e.2 * (∏ i, (pReset ζ) e.1 i) *
        highResponseProduct a V η g w φ
          (coefficientReset c (highResponseMarkAtom C q e.2).2
            (highResponseMarkAtom C q e.2).1) y| ≤
      pPlus^n * highSeparatedDerivativeBudget a ρ * ↑n^2 * η^2 *
        ∑ e : J × HighResponseMarkIndex ι q, |weights e.1 * highResponseMarkWeight C q (A ζ) e.2| := by
      have hReset : ∀ e i, |(pReset ζ) e i| ≤ pPlus := hReset ζ
      have he : (∑ e : J × HighResponseMarkIndex ι q,
          weights e.1 * highResponseMarkWeight C q (A ζ) e.2 * (∏ i, (pReset ζ) e.1 i) *
            highResponseProduct a V η g w φ
              (coefficientReset c (highResponseMarkAtom C q e.2).2
                (highResponseMarkAtom C q e.2).1) y) =
          highDensityResponseAction q C weights (fun _ => (A ζ)) c
            (fun e => ∏ i, (pReset ζ) e i) (fun v => highResponseProduct a V η g w φ v y) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro e _
        have hh (r : HighResponseMarkIndex ι q) :
            weights e * highResponseMarkWeight C q (A ζ) r * (∏ i, (pReset ζ) e i) *
              highResponseProduct a V η g w φ
                (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1) y =
            weights e*(∏ i, (pReset ζ) e i) * (highResponseMarkWeight C q (A ζ) r *
              highResponseProduct a V η g w φ
                (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1) y) := by ring
        simp only [hh, ← Finset.mul_sum]
        rw [highResponseMark_action q C (A ζ) c (fun v => highResponseProduct a V η g w φ v y)]
      rw [he]
      apply (high_density_response_product_abs_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        weights (fun _ => (A ζ)) (pReset ζ) g w φ c hc hg hw hφ hp hReset y).trans_eq
      rw [Fintype.sum_prod_type]
      simp only [abs_mul]
      simp_rw [← Finset.mul_sum]
      rw [highResponseMark_variation q C (A ζ)]
      unfold highResponsePacketCost highLocalDerivativeConstant highSeparatedDerivativeBudget
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    simpa only [W,O,Φ,K,responseTensorWeight,mul_assoc] using
      h_responseTensor_slice_all_count_bound
  unfold highMarkedResponseAction
  have he : (fun e => absoluteActivation ν W e * (∏ i, pReset e.1 e.2.1 i) *
      highResponseProduct a V η g w φ
        (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1) y) =
      (fun e => absoluteActivation ν W e * O e) := by funext e; dsimp [O,Φ]; ring
  rw [he,absoluteMarkLaw_activation_integral ν W hm hpos O,integral_prod _ hWO]
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hWO.integral_prod_left.abs (hi.abs.integral_prod_left.const_mul K) hSlice).trans_eq
  rw [integral_const_mul, ← integral_prod _ hi.abs]
  rfl
end Reference
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
theorem highPacket_reference_all_count_bound 
    (σ ) [IsFiniteMeasure σ] (ad bd m r D q) (hn : 1 ≤ n)
    (C a V η ρ pPlus ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (A ) (hA : ∀ γ δ, Measurable (fun ζ => A ζ γ δ))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ ad bd m r D q C A)
    (reset : Z × HighDensityMarkIndex m r D → Fin n → ℝ)
    (hmReset : ∀ i, Measurable (fun e => reset e i))
    (hReset : ∀ e i, |reset e i| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction (highPacketAbsoluteLaw σ ad bd m r D q C A)
      (highPacketActivation σ ad bd m r D q C A) a V η
      (fun e => reset (e.1,e.2.1))
      (fun e => coefficientReset c (highResponseMarkAtom C q e.2.2).2
        (highResponseMarkAtom 0 q e.2.2).1) g w φ y| ≤
      pPlus^n*highSeparatedDerivativeBudget a ρ*↑n^2*η^2*
        highPacketMarkMass σ ad bd m r D q C A := by
  exact responseTensor_reference_all_count_bound σ q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
    (densityPacketWeight ad bd m r D) A
    (highPacketMarkWeight_measurable ad bd m r D q C A hA)
    (highPacketMarkWeight_integrable σ ad bd m r D q C A hA hcost) hpos
    (fun ζ e => reset (ζ,e))
    (fun e i => (hmReset i).comp (measurable_id.prodMk measurable_const))
    (fun ζ e i => hReset (ζ,e) i) g w φ c hc hg hw hφ hp y
end Packet
theorem sourceRow_reference_all_count_bound 
    (d ) [NeZero d] (k D M q ) (hn : 1 ≤ n)
    (ad bd C lam ℓ N μ a V η ρ pPlus )
    (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q ad bd C lam ℓ N μ)
    (reset : SourceRowDensityMark d D M q ad bd C lam ℓ N μ i → Fin n → ℝ)
    (hmReset : ∀ u, Measurable (fun e => reset e u))
    (hReset : ∀ e u, |reset e u| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → HighFrameIndex d D → ℝ)
    (c ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowLaw i)
      ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowActivation i) a V η
      (fun e => reset (sourceRowDensityProj d D M q ad bd C lam ℓ N μ i e))
      (fun e => coefficientReset c
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowVector i e)
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowTime i e)) g w φ y| ≤
      pPlus^n*highSeparatedDerivativeBudget a ρ*↑n^2*η^2*
        (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p =>
    cases p
    · exact highPacket_reference_all_count_bound (Measure.dirac ()) ad bd D 2 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inl .unit)) reset hmReset hReset g w φ c hc hg hw hφ hp y
    · exact highPacket_reference_all_count_bound (finePairTimeFieldMeasure d 0 ℓ) ad bd D 2 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (finePairTimeMatrix d (finePairDistanceMatrix d D))
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _)
        (hpos (.inl .coarse)) reset hmReset hReset g w φ c hc hg hw hφ hp y
    have hA : ∀ γ δ, Measurable (fun ζ => (finePairTimeMatrix d (finePairDistanceMatrix d D)) ζ γ δ) := finePairTimeMatrix_measurable d _
    have hcost : Integrable (separatedMatrixCost (finePairTimeMatrix d (finePairDistanceMatrix d D))) (finePairTimeFieldMeasure d ℓ N) := finePairTimeMatrix_cost_integrable d ℓ N _
    have hpos  := hpos (.inl .fine)
    have h_finePairPacket_reference_all_count_bound := responseTensor_reference_all_count_bound (finePairTimeFieldMeasure d ℓ N) q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (finePairDensityWeight ad bd M) (finePairTimeMatrix d (finePairDistanceMatrix d D))
        (finePairPacketWeight_measurable ad bd M q C (finePairTimeMatrix d (finePairDistanceMatrix d D)) hA)
        (finePairPacketWeight_integrable (finePairTimeFieldMeasure d ℓ N) ad bd M q C (finePairTimeMatrix d (finePairDistanceMatrix d D)) hA hcost) hpos
        (fun ζ e => reset (ζ,e))
        (fun e i => (hmReset i).comp (measurable_id.prodMk measurable_const))
        (fun ζ e i => hReset (ζ,e) i) g w φ c hc hg hw hφ hp y
    · exact h_finePairPacket_reference_all_count_bound
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacket_reference_all_count_bound (Measure.dirac ()) ad bd D 1 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inr (.inl ()))) reset hmReset hReset g w φ c hc hg hw hφ hp y
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let T := higherBandFamilyUpper d ℓ N μ i.val
      letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
      exact highPacket_reference_all_count_bound (higherBandCarrierMeasure d r ℓ T i.val.2)
        ad bd (higherBandFamilyGuardDegree M i.val) r D q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (higherBandCarrierAmplitude d r D lam i.val.2)
        (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
        (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2)
        (hpos (.inr (.inr i))) reset hmReset hReset g w φ c hc hg hw hφ hp y
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
def highMarkedLocalScoreNumerator  [Fintype ι] [MeasurableSpace E] 
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η^2*(∏ u, p u)*∑ u, (w u)^2*highResponseVarianceTerm a V η g w φ c y u
theorem highResponseProduct_ball_abs_le_one  [Fintype ι]
     (C a V η ρ ) (ha : a ≠ 0) (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (v : ι → ℝ) (hv : ∑ γ, |v γ| ≤ C⁻¹) (y : Fin n → Fin 3) :
    |highResponseProduct a V η g w φ v y| ≤ 1 := by
  apply highMarkedResponseProduct_abs_le_one a V η ha g w φ v
  intro u b
  apply hp _
  have hpv := hφ v hv u
  have : |η*w u*(∑ γ, φ u γ*v γ)| ≤ η := by
    rw [abs_mul,abs_mul,abs_of_nonneg hη]
    have ht := mul_le_mul (hw u) hpv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left ht hη]
  exact (abs_add_le _ _).trans (by linarith [hg u])
section Complete
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
include hD hq hM hCfr hℓ hℓN
theorem completeSourceResponseAction_all_count_bound (hn : 1 ≤ n)
    (j h a V η ρ) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (x : Fin n → Covariate d) (g w : Fin n → ℝ)
    (φ : Fin n → HighFrameIndex d D → ℝ)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ Cfr⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ y| ≤
      C.densityUpper^n*highSeparatedDerivativeBudget a ρ*↑n^2*η^2*
        highRowTotalMass (R).rowMass := by
  let ad := C.densityLower+1/↑M
  let bd := C.densityUpper-1/↑M
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  have hCf : 0 < Cfr := by linarith
  obtain ⟨had,hadbd⟩ := high_source_interval_numeric C ↑M hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq ad bd had hadbd Cfr hCf
    lam ℓ N μ hℓ hℓN
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) :=
    highUnionMark_standardBorel
  let c := (highUnionSourceState C R h).2 j
  have hc : ∑ γ, |c γ| ≤ Cfr⁻¹ := highUnionSourceState_coefficient_ball C R G h j
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  let reset : (i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ) →
      SourceRowDensityMark d D M q ad bd Cfr lam ℓ N μ i → Fin n → ℝ :=
    fun i z u => highUnionSourceResetDensity C R j h
      (Sum.inl ⟨i,sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i z⟩) (x u)
  have hresetMeas (i) (u) : Measurable (fun z => reset i z u) := by
    exact (highUnionSourceResetDensity_measurable C R G j h).comp
      ((measurable_inl.comp ((rowSigmaMk_measurable i).comp
        (sourceRowDensityLift_measurable d D M q ad bd Cfr lam ℓ N μ r₀ i))).prodMk measurable_const)
  have hresetBound (i) (z) (u) : |reset i z u| ≤ C.densityUpper :=
    highUnionSourceResetDensity_abs_le C R G j h _ _
  have hirrel (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) (x u) =
      reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e) u := by
    dsimp only [reset]
    unfold highUnionSourceResetDensity
    unfold highUnionSourceDensity
    change (highUnionSourceState C R _).1 (x u) = (highUnionSourceState C R _).1 (x u)
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if x u ∈ highTorusPatch d k j then (R).rowSlope j i e (x u)*_+(R).rowIntercept i e else _) =
      (if x u ∈ highTorusPatch d k j then (R).rowSlope j i
        (sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i
          (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e)) (x u)*_+
        (R).rowIntercept i (sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i
          (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e)) else _)
    simp only [completeSourceRows]
    rw [sourceRow_density_projection_slope d k D M q ad bd Cfr lam ℓ N μ r₀ j i e (x u),
      sourceRow_density_projection_intercept d k D M q ad bd Cfr lam ℓ N μ r₀ i e]
  let O := fun e => (∏ u, highUnionSourceResetDensity C R j h e (x u))*
    highResponseProduct a V η g w φ (highUnionSourceResetCoefficient C R j h e) y
  have hmO : Measurable O := (Finset.measurable_fun_prod _ (fun u _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp
      (measurable_id.prodMk measurable_const))).mul
        (highMarkedResponseProduct_measurable a V η _
          (highUnionSourceResetCoefficient_measurable C R G j h) g w φ y)
  have hOb (e) : ‖O e‖ ≤ C.densityUpper^n := by
    have hcReset := highUnionResponseReset_ball R Cfr hCf G.vector_ball G.time_interval e c hc
    have hResponse := highResponseProduct_ball_abs_le_one Cfr a V η ρ ha.ne' hη hηρ
      g w φ hg hw hφ hp _ hcReset y
    change |(∏ u, highUnionSourceResetDensity C R j h e (x u))*highResponseProduct a V η g w φ _ y| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ C.densityUpper (lt_trans zero_lt_one C.one_lt_densityUpper).le
      (fun u => highUnionSourceResetDensity_abs_le C R G j h e (x u))) hResponse
        (abs_nonneg _) (pow_nonneg (lt_trans zero_lt_one C.one_lt_densityUpper).le _)).trans_eq (mul_one _)
  have he : highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ y =
      ∑ i, highMarkedResponseAction ((R).rowLaw i) ((R).rowActivation i) a V η
        (fun e => reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e))
        (fun e => coefficientReset c ((R).rowVector i e) ((R).rowTime i e)) g w φ y := by
    unfold highMarkedResponseAction
    simp_rw [mul_assoc]
    rw [highUnionSource_bounded_action C R G hpos O hmO (C.densityUpper^n) hOb]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with e
    simp only [O,hirrel,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ =>
    sourceRow_reference_all_count_bound d k D M q hn ad bd Cfr lam ℓ N μ a V η ρ C.densityUpper
      hCf ha hη hρ hηρ (lt_trans zero_lt_one C.one_lt_densityUpper).le hpos i (reset i) (hresetMeas i) (hresetBound i)
      g w φ c hc hg hw hφ hp y)).trans_eq
  exact (Finset.mul_sum _ _ _).symm
end Complete
end
section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
theorem completeSourceNumerator_original_field_bound  [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 η0, 1 ≤ Cfr0 ∧ 0 < η0 ∧
      ∀ k D M q n : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → 1 ≤ n →
      highCenterResolutionThreshold C ≤ ↑M →
      ∀ Cfr lam ℓ N μ cf : ℝ, Cfr0 ≤ Cfr → 0 < ℓ → ℓ < N → 0 ≤ cf →
      cf*↑k^(-C.smoothness) ≤ η0 →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/↑M)
          (C.densityUpper-1/↑M) Cfr lam ℓ N μ)),
      ∀ x : Fin n → Covariate d, ∀ y : Fin n → Fin 3,
      let R := completeSourceRows C k D M q Cfr lam ℓ N μ
      let η := cf*↑k^(-C.smoothness)
      let c := (highUnionSourceState C R h).2
      |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
        (highUnionActivation R (highCenterMix C)) Q.a V η
        (fun u => highUnionSourceDensity C R h (x u))
        (fun e u => highUnionSourceResetDensity C R j h e (x u))
        (highUnionSourceResetCoefficient C R j h)
        (fun u => highLocalFieldWithout d k D η c j (x u))
        (fun u => highPeriodicTensor d k j (x u))
        (fun u => highLocalFrameFeature k j (x u)) (c j) y| ≤
        (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)^n*
          η^2*(highRowTotalMass R.rowMass+1) := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let η0 := Q.ρ/(2*(↑2^d+1))
  have hη0 : 0 < η0 := div_pos Q.ρ_pos (by positivity)
  refine ⟨Cfr0,η0,hfr0,hη0,?_⟩
  intro k D M q n hk0 horder hk hD hq hn hM Cfr lam ℓ N μ cf hfr hℓ hℓN hcf hη V hV j h x y
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ (hfr0.trans hfr) hℓ hℓN
  let c := (highUnionSourceState C R h).2
  let η := cf*↑k^(-C.smoothness)
  let g := fun u : Fin n => highLocalFieldWithout d k D η c j (x u)
  let w := fun u : Fin n => highPeriodicTensor d k j (x u)
  let φ : Fin n → HighFrameIndex d D → ℝ := fun u => highLocalFrameFeature k j (x u)
  have hηn : 0 ≤ η := by dsimp [η]; positivity
  have hamp : (↑2^d+1)*η ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*((2 : ℝ)^d+1))).mp hη
    nlinarith
  have hηρ : η ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (l) : frameCoefficientL1 (highFramePolynomial (c l)) ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (highUnionSourceState_coefficient_ball C R G h l).trans
      ((inv_le_inv₀ (by linarith : 0 < Cfr) (by linarith : 0 < Cfr0)).mpr hfr)
  have hF := (hfield k hk0 hk cf hcf (fun l => highFramePolynomial (c l)) hP).1
  have hw (u) : |w u| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j (x u))]
    exact highPeriodicTensor_le_one d k (by omega) j (x u)
  have hφ (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (u) :
      |∑ γ, φ u γ*v γ| ≤ 1 :=
    highLocalFrameFeature_ball_abs_le_one k j (x u) Cfr (hfr0.trans hfr) v hv
  have hg (u) : |g u| ≤ Q.ρ/2 := by
    have hprof := hφ (c j) (highUnionSourceState_coefficient_ball C R G h j) u
    have hh : |η*w u*(∑ γ, φ u γ*c j γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hηn]
      have ht := mul_le_mul (hw u) hprof (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left ht hηn]
    have hd := highFrameField_local_decomposition d k D hk η c j (x u)
    have he : g u = highFrameField d k η (fun l => highFramePolynomial (c l)) (x u)-
        η*w u*(∑ γ, φ u γ*c j γ) := by dsimp [g,w,φ]; linarith [hd]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hF (x u)) hh).trans (by nlinarith only [hamp]))
  have hCfr  := hfr0.trans hfr
  have hp  := fun f hf z => Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 z)
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  let c := (highUnionSourceState C R h).2 j
  let B := highRowTotalMass (R).rowMass
  have hc := highUnionSourceState_coefficient_ball C R G h j
  have hpCurrent (u) (b) : 0 ≤ ternaryMass Q.a (coefficientRegression η g w φ c u) V b := by
    apply hp _
    have hv := hφ c hc u
    have : |η*w u*(∑ γ, φ u γ*c γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hηn]
      have ht := mul_le_mul (hw u) hv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left ht hηn]
    exact (abs_add_le _ _).trans (by linarith [hg u])
  have hIncoming (u) : |highUnionSourceDensity C R h (x u)| ≤ C.densityUpper := by
    have hi := highUnionSourceDensity_coarse_interval C R G h (x u)
    rw [abs_of_nonneg (C.densityLower_pos.le.trans hi.1)]
    exact hi.2
  have haction := completeSourceResponseAction_all_count_bound C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN hn j h Q.a V η Q.ρ Q.a_pos hηn Q.ρ_pos.le hηρ x g w φ hg hw hφ hp y
  have hcorrection := high_response_variance_correction_abs_bound hn Q.a V η C.densityUpper
    Q.a_pos (lt_trans zero_lt_one C.one_lt_densityUpper).le (fun u => highUnionSourceDensity C R h (x u)) g w φ c
    hw hIncoming hpCurrent y
  have hraw : |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) Q.a V η
      (fun u => highUnionSourceDensity C R h (x u))
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ c y| ≤
      C.densityUpper^n*(highSeparatedDerivativeBudget Q.a Q.ρ*B+1/Q.a^2)*↑n^2*η^2 := by
    apply (abs_sub _ _).trans
    apply (add_le_add haction hcorrection).trans_eq
    ring
  apply hraw.trans
  simpa only [mul_one,div_one] using highSeparated_score_budget_absorb n hn Q.a Q.ρ C.densityUpper
    1 1 η B (lt_trans zero_lt_one C.one_lt_densityUpper).le (by norm_num) (by norm_num) G.total_positive.le
set_option backward.isDefEq.respectTransparency false
end
theorem fullSpatialPatchDesign_real_univ (d n ) :
    (fullSpatialPatchDesign d n).real univ = 2^(d*n) := by
  simp only [fullSpatialPatchDesign, measureReal_def, Measure.pi_univ,
    Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow]
  change (volume.real (spatialPatchBox d))^n = _
  rw [spatialPatchBox_real_volume, pow_mul]
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
theorem crude_raw_square_energy_pointwise {d n : ℕ} (Chi η B )
    (hChi : 0 ≤ Chi) (hB : 0 ≤ B)
    (R )
    (hcap : ∀ x y, |R x y| ≤ Chi^n*η^2*(B+1)) (x : Fin n → Covariate d) :
    selectedRawSquareEnergy R x ≤ (3*Chi^2)^n*η^4*(B+1)^2 := by
  have hp (y) : R x y ^ 2 ≤ Chi^(2*n)*η^4*(B+1)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Chi^n*η^2*(B+1))).mpr (hcap x y)
    simp only [sq_abs] at hh
    convert hh using 1 <;> (try rw [mul_pow,mul_pow,←pow_mul]) <;> ring
  calc
    _ = ∑ y : Fin n → Fin 3, R x y ^ 2 := (by unfold selectedRawSquareEnergy; apply Finset.sum_congr (by ext y; simp); intro y _; rfl)
    _ ≤ ∑ _y : Fin n → Fin 3, Chi^(2*n)*η^4*(B+1)^2 :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = (3*Chi^2)^n*η^4*(B+1)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow, Nat.cast_ofNat, nsmul_eq_mul, mul_pow, ←pow_mul]
      ring
section Marked
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
  [NeZero k] [LinearOrder (HighWindowLabels d k)]
def highUnionSourceMarkedNumerator (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    (n : ℕ) (a V η : ℝ) (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) : ℝ :=
  highMarkedSampleNumerator n (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) a V η
    (highUnionSourceDensity C R h) (highUnionSourceResetDensity C R j h)
    (highUnionSourceResetCoefficient C R j h)
    (highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
    ((highUnionSourceState C R h).2 j) x y
end Marked
end
section Pair
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]
theorem ordinaryPairPacket_zero_other_count  (hn : 3 ≤ n)
    (σ ) [IsFiniteMeasure σ] (a b ) (ha : 0 < a) (hab : a < b)
    (m D q ) (hnm : n ≤ m) (hnD : n ≤ D) (C A) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c )
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) = 0 := by
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c
    (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i)
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have hh := highSeparatedPacketAction_count_selector σ a b ha hab m 2 D q
    (by omega) (by omega) (Finset.univ : Finset (Fin n)) (by simpa using hnD)
    (by simpa using hnm) (by simpa using (show 2 ≤ n by omega)) p
    (fun ζ i _ => ψ ζ i) (fun i _ => hmψ i) (fun ζ i _ => hbψ ζ i) C A hA hcost c Φ
  simpa only [Finset.card_univ, Fintype.card_fin, if_neg (show n ≠ 2 by omega)] using hh
end Pair
section
variable {d n F : ℕ} {N lo hi : ℝ}
theorem finite_pair_kernel_integrable_and_integral_le 
    [MeasurableSpace X] (ν ) [SigmaFinite ν] (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ ≤ ν) (f ) (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) (K )
    (hi : ∀ x, Integrable (fun y => f (x,y)) ν)
    (hb : ∀ x, (∫ y, f (x,y) ∂ν) ≤ K) :
    Integrable f (μ.prod μ) ∧ (∫ z, f z ∂μ.prod μ) ≤ μ.real univ * K := by
  have hsection (x : X) : Integrable (fun y => f (x,y)) μ := (hi x).mono_measure hμ
  have hsectionBound (x : X) : (∫ y, f (x,y) ∂μ) ≤ K :=
    (integral_mono_measure hμ (Filter.Eventually.of_forall fun y => hn (x,y)) (hi x)).trans (hb x)
  have hinner : Integrable (fun x => ∫ y, ‖f (x,y)‖ ∂μ) μ := by
    have hmin : AEStronglyMeasurable (fun x => ∫ y, ‖f (x,y)‖ ∂μ) μ :=
      hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    apply (integrable_const K).mono' hmin
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact hsectionBound x
  have hf  :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection, hinner⟩
  refine ⟨hf, ?_⟩
  rw [integral_prod _ hf]
  simpa only [integral_const, smul_eq_mul] using
    integral_mono hf.integral_prod_left (integrable_const K) hsectionBound
theorem fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le  (hd : 4 < d)
    {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N) :
    Integrable (fun U =>
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance (U 0) (U 1)))^2)
      (fullSpatialPatchDesign d 2) ∧
    (∫ U : Fin 2 → Covariate d,
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance (U 0) (U 1)))^2
      ∂fullSpatialPatchDesign d 2) ≤
      6 * 2^d * spatialInverseFourConstant d / T0^(d-4) := by
  have h_fineAlias_spatial_squared_integrable_and_integral_le (x : Covariate d) : Integrable (fun y => (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) volume ∧
      (∫ y, (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
    have he := euclidean_fineAlias_squared_integrable_and_integral_le hd hT0 hN
    have hi := he.1
    rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hi
    have hi0 : Integrable (fun z : Covariate d => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2) volume := by
      simpa only [Function.comp_def] using hi
    refine ⟨by simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x, ?_⟩
    simp_rw [exactEuclideanDistance_eq_norm]
    rw [integral_sub_right_eq_self (μ := volume) (fun z : Covariate d => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2)]
    exact ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding
      (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2)).trans_le he.2
  have h_fineAlias_spatial_pair_squared_integrable_and_integral_le : Integrable (fun xy =>
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance xy.1 xy.2))^2)
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ∧
    (∫ xy : Covariate d × Covariate d,
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance xy.1 xy.2))^2
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      6 * 2^d * spatialInverseFourConstant d / T0^(d-4) := by
    have hm := ((fineAliasLaplaceKernel_measurable T0 N hN).comp
      (exactEuclideanDistance_continuous (d := d)).measurable).pow_const 2
    have h := finite_pair_kernel_integrable_and_integral_le volume (volume.restrict (spatialPatchBox d))
      Measure.restrict_le_self _ hm (fun _ => sq_nonneg _) (6*spatialInverseFourConstant d/T0^(d-4))
      (fun x => (h_fineAlias_spatial_squared_integrable_and_integral_le x).1)
      (fun x => (h_fineAlias_spatial_squared_integrable_and_integral_le x).2)
    refine ⟨h.1, h.2.trans_eq ?_⟩
    rw [measureReal_def, Measure.restrict_apply_univ]
    change volume.real (spatialPatchBox d) * _ = _
    rw [spatialPatchBox_real_volume]
    ring
  have h := h_fineAlias_spatial_pair_squared_integrable_and_integral_le
  have hp := measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))
  refine ⟨?_, ?_⟩
  · exact hp.integrable_comp_of_integrable h.1
  · exact (hp.integral_comp (MeasurableEquiv.finTwoArrow : (Fin 2 → Covariate d) ≃ᵐ (Covariate d × Covariate d)).measurableEmbedding _).trans_le h.2
theorem fullSpatialPatchDesign_ae_hyperplaneCube  :
    ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, U i ∈ hyperplaneCube d := by
  have hU : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, U i ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ => volume.restrict (spatialPatchBox d))
      (i := i)).eventually (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hU] with U hU i r
  exact abs_le.mpr ⟨(hU i).1 r, (hU i).2 r⟩
 theorem finePairTimeSubsetMoment_two_subset_square_integrable_and_le  [NeZero d]
    (hd : 4 < d)  (hlo : 0 < lo) (hhi : lo ≤ hi)
    (S : Finset (Fin n)) (hS : S.card = 2) :
    Integrable (fun U => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U : Fin n → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      2^(d*(n-2)) * (6*2^d*spatialInverseFourConstant d / lo^(d-4)) := by
  have h_finePairTimeSubsetMoment_pair_square_integrable_and_le {j} (hj : j = 2) : Integrable (fun U => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2)
        (fullSpatialPatchDesign d j) ∧
      (∫ U : Fin j → Covariate d, finePairTimeSubsetMoment lo hi U Finset.univ ^ 2
        ∂fullSpatialPatchDesign d j) ≤ 6 * 2^d * spatialInverseFourConstant d / lo^(d-4) := by
    subst j
    have he : (fun U => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) =ᵐ[fullSpatialPatchDesign d 2]
        (fun U => fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) ^ 2) := by
      filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
      have h_finePairTimeSubsetMoment_univ_pair : finePairTimeSubsetMoment lo hi U Finset.univ =
        fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) := by
        unfold finePairTimeSubsetMoment
        simp only [Fin.prod_univ_two]
        rw [finePairTimeFieldValue_weighted_covariance d lo hi hlo.le _ _ (hU 0) (hU 1), exactEuclideanDistance_eq_euclideanNorm]
        unfold fineAliasLaplaceKernel
        rw [intervalIntegral.integral_of_le hhi, ← integral_Icc_eq_integral_Ioc]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun T => by dsimp; rw [neg_mul])
      rw [h_finePairTimeSubsetMoment_univ_pair]
    have h := fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le hd hlo hhi
    refine ⟨h.1.congr he.symm, ?_⟩
    exact (integral_congr_ae he).trans_le h.2
  have h := h_finePairTimeSubsetMoment_pair_square_integrable_and_le hS
  refine ⟨?_, ?_⟩
  · simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
    exact spatial_subset_square_integrable_enumerated S _ h.1
  · rw [finePairTimeSubsetMoment_square_integral_reindex]
    simpa only [hS] using (mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (2 : ℝ)^(d*(n-S.card))))
 def finePairAliasActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    finePairResponseActionBudget d q C a ρ * n^2 * η^2)^2 *
      (n.choose 2 )^2 * 2^(d*(n-2)) *
        (6*2^d*spatialInverseFourConstant d / T0^(d-4))
def finePairDistanceFactor  (N : ℝ) (x y : Covariate d) : ℝ :=
  (1 + N * exactEuclideanDistance x y) * Real.exp (-(N * exactEuclideanDistance x y))
theorem finePairDistanceFactor_nonneg   (hN : 0 ≤ N) (x y : Covariate d) :
    0 ≤ finePairDistanceFactor N x y := by
  exact mul_nonneg (by have := exactEuclideanDistance_nonneg x y; positivity) (Real.exp_pos _).le
theorem finePairDistanceFactor_square_absorption   (hN : 0 ≤ N)
    (x y : Covariate d) :
    (finePairDistanceFactor N x y)^2 ≤ 6 * Real.exp (-(N * exactEuclideanDistance x y)) := by
  unfold finePairDistanceFactor
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : 2 * -(N * exactEuclideanDistance x y) = -(2 * (N * exactEuclideanDistance x y)) := by ring
  rw [he]
  exact pair_defect_exponential_absorption _
    (mul_nonneg hN (exactEuclideanDistance_nonneg x y))
theorem finePairDistanceFactor_square_integrable   (hN : 0 < N) :
    Integrable (fun xy : Covariate d × Covariate d => (finePairDistanceFactor N xy.1 xy.2)^2)
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) := by
  have h_finePairDistanceFactor_measurable : Measurable (fun xy : Covariate d × Covariate d => finePairDistanceFactor N xy.1 xy.2) := by
    unfold finePairDistanceFactor
    exact ((continuous_const.add (exactEuclideanDistance_continuous.const_mul N)).mul
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp)).measurable
  have hm := h_finePairDistanceFactor_measurable.pow_const 2
  have he : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(N * exactEuclideanDistance xy.1 xy.2)))
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) :=
    Integrable.of_bound
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun xy => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
          (mul_nonneg hN.le (exactEuclideanDistance_nonneg _ _))))
  apply (he.const_mul 6).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun xy => by
    rw [Real.norm_eq_abs, abs_sq]
    exact finePairDistanceFactor_square_absorption hN.le _ _
def finePairCountTwoRawNumerator  [NeZero d]
    (ad bd T0 N : ℝ) (D M q : ℕ) (C a V η : ℝ)
    (U : Fin 2 → Covariate d) (p g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) : ℝ :=
  finePairThreeRowFirstAction ad bd T0 N D M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η^2 * (p 0 * p 1) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i
theorem fine_pair_scalar_product_abs_le (η b L d w0 w1 p0 p1 m0 m1 : ℝ)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hw0 : |w0| ≤ 1) (hw1 : |w1| ≤ 1) (hp0 : |p0| ≤ b) (hp1 : |p1| ≤ b)
    (hm0 : |m0| ≤ L) (hm1 : |m1| ≤ L) :
    |η^2 * w0 * w1 * p0 * p1 * d * m0 * m1| ≤ η^2 * b^2 * L^2 * d := by
  have hw : |w0*w1| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hw0 hw1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
  have hp : |p0*p1| ≤ b^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hp0 hp1 (abs_nonneg _) hb
  have hm : |m0*m1| ≤ L^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hm0 hm1 (abs_nonneg _) hL
  have hprod := mul_le_mul (mul_le_mul hw hp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)) hm
    (abs_nonneg _) (by positivity : 0 ≤ 1 * b^2)
  have hs := mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg η) hd)
  calc
    _ = η^2*d * ((|w0*w1| * |p0*p1|) * |m0*m1|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_sq, abs_of_nonneg hd]
      simp only [abs_mul]
      ring
    _ ≤ η^2*d * ((1*b^2)*L^2) := hs
    _ = _ := by ring
def finePairCountTwoSpatialBudget (d : ℕ) (bd a ρ η N : ℝ) : ℝ :=
  (η^2*bd^2*((2*ρ+a)/a^2)^2)^2 * (6*2^d*spatialExponentialConstant d/N^d)
def cardinalGeometryEnvelope  (q : ℕ) (bd C a ρ η T : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  3^n * (2*cardinalRawAliasCoefficient n bd a η^2 *
    (∑ i, cardinalWeightDefect i (spatialInterpolationLambda d) T U)^2 +
    2*cardinalRawTaylorCoefficient n q bd C a ρ η^2 *
      spatialMatrixL1 (integratedCardinalMatrix (D := F) (spatialInterpolationLambda d) T U)^2)
 theorem cardinalGeometryEnvelope_nonneg  (q bd C a ρ η T)
    (U : Fin n → Covariate d) : 0 ≤ cardinalGeometryEnvelope (F := F) q bd C a ρ η T U := by
  unfold cardinalGeometryEnvelope
  positivity
 theorem cardinalGeometryEnvelope_integrable_and_le  (hd : 5 ≤ d) (hn : 2 ≤ n)
    (q bd C a ρ η)  (hT : 1 ≤ T) :
    Integrable (cardinalGeometryEnvelope (d := d) (n := n) (F := F) q bd C a ρ η T)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, cardinalGeometryEnvelope (F := F) q bd C a ρ η T U ∂fullSpatialPatchDesign d n) ≤
      3^n * cardinalRawSpatialEnergyBudget d n q bd C a ρ η T := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hZ : Integrable (fun U => (∑ i : Fin n, cardinalWeightDefect i (spatialInterpolationLambda d) T U)^2)
      (fullSpatialPatchDesign d n) := by
    have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) Finset.univ
      (fun i U => cardinalWeightDefect i (spatialInterpolationLambda d) T U)
      (fun i _ => cardinalWeightDefect_measurable i _ hT)
      (fun i _ => cardinalWeightDefect_square_integrable i hlam hT)
    simpa only [abs_of_nonneg (cardinalWeightDefect_mem_unit _ hlam T _).1] using h
  have hE := integratedCardinalMatrix_full_square_integrable (D := F) hd hn hT
  refine ⟨((hZ.const_mul _).add (hE.const_mul _)).const_mul _, ?_⟩
  unfold cardinalGeometryEnvelope
  rw [integral_const_mul, integral_add (hZ.const_mul _) (hE.const_mul _), integral_const_mul, integral_const_mul]
  have h := add_le_add (mul_le_mul_of_nonneg_left (cardinalWeightDefect_sum_square_integral_le (d := d) (n := n) (by omega) hn hT)
    (by positivity : 0 ≤ 2*cardinalRawAliasCoefficient n bd a η^2))
    (mul_le_mul_of_nonneg_left (integratedCardinalMatrix_full_square_integral_le (D := F) hd hn hT)
      (by positivity : 0 ≤ 2*cardinalRawTaylorCoefficient n q bd C a ρ η^2))
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (3 : ℝ)^n)).trans_eq (by
    unfold cardinalRawSpatialEnergyBudget; ring)
 theorem highCardinalRawNumerator_sum_square_le_geometry 
    (ad bd ) (haD : 0 < ad) (hab : ad < bd)  (hT : 1 ≤ T)
    (m D q ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U ) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, highCardinalRawNumerator ad bd (spatialInterpolationLambda d) T m D q
      C a V η U p g w c y^2) ≤ cardinalGeometryEnvelope (F := F) q bd C a ρ η T U := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ =>
    highCardinalRawNumerator_square_bound_of_chart ad bd _ haD hab hlam hT m D q hn hnm hnD hnF hq
      C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y)
  exact h.trans_eq (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]; rfl)
 def fineFieldGeometryEnvelope  (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  3^n * (finePairDensityCoefficientBudget ad bd M n *
    finePairResponseActionBudget d q C a ρ*n^2*η^2)^2 *
      (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card),
        |finePairTimeSubsetMoment T0 N U S|)^2
 def finePairAliasGeometryEnvelope  (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  3^n * (finePairDensityCoefficientBudget ad bd M n *
    finePairResponseActionBudget d q C a ρ*n^2*η^2)^2 *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, |finePairTimeSubsetMoment T0 N U S|)^2
 theorem fineFieldGeometryEnvelope_nonneg  (ad bd T0 N M q C a ρ η)
    (U : Fin n → Covariate d) : 0 ≤ fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  unfold fineFieldGeometryEnvelope; positivity
 theorem fineFieldGeometryEnvelope_integrable_and_le  [NeZero d] (hd : 3 ≤ d)
    (ad bd T0 N ) (hT0 : 0 < T0) (M q C a ρ η) :
    Integrable (fineFieldGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      3^n*finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card)
  have hs (S) (hS : S ∈ s) : 4 ≤ S.card := (Finset.mem_filter.mp hS).2.1
  have hi := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) s
    (fun S U => finePairTimeSubsetMoment T0 N U S)
    (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
    (fun S hS => finePairTimeSubsetMoment_square_integrable hd hT0 S (hs S hS))
  refine ⟨hi.const_mul _, ?_⟩
  unfold fineFieldGeometryEnvelope
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (finePairTimeSubsetMoment_sum_abs_square_integral_le hd (hi := N) hT0 s hs)
    (by positivity : 0 ≤ 3^n*(finePairDensityCoefficientBudget ad bd M n *
      finePairResponseActionBudget d q C a ρ*n^2*η^2)^2)
  exact h.trans_eq (by unfold finePairEvenActionSpatialBudget; ring)
 theorem finePairAliasGeometryEnvelope_integrable_and_le  [NeZero d] (hd : 4 < d)
    (ad bd T0 N ) (hT0 : 0 < T0) (hN : T0 ≤ N) (M q C a ρ η) :
    Integrable (finePairAliasGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      3^n*finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hs (S) (hS : S ∈ s) : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
  have hi := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) s
    (fun S U => finePairTimeSubsetMoment T0 N U S)
    (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
    (fun S hS => (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
  refine ⟨hi.const_mul _, ?_⟩
  unfold finePairAliasGeometryEnvelope
  rw [integral_const_mul]
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d n) s
    (fun S U => |finePairTimeSubsetMoment T0 N U S|)
    (2^(d*(n-2))*(6*2^d*spatialInverseFourConstant d/T0^(d-4)))
    (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)
    (fun S hS => by simpa only [sq_abs] using (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
    (fun S hS => by simpa only [sq_abs] using (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).2)
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 3^n*(finePairDensityCoefficientBudget ad bd M n *
    finePairResponseActionBudget d q C a ρ*n^2*η^2)^2)).trans_eq (by
      dsimp [s]
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      unfold finePairAliasActionSpatialBudget
      ring)
 def finePairCountTwoGeometryEnvelope  (bd a ρ η N : ℝ) (U : Fin 2 → Covariate d) : ℝ :=
  9*(η^2*bd^2*((2*ρ+a)/a^2)^2)^2*finePairDistanceFactor N (U 0) (U 1)^2
 theorem finePairCountTwoGeometryEnvelope_nonneg  (bd a ρ η N )
    (U : Fin 2 → Covariate d) : 0 ≤ finePairCountTwoGeometryEnvelope bd a ρ η N U := by
  unfold finePairCountTwoGeometryEnvelope; positivity
 theorem finePairCountTwoGeometryEnvelope_integrable_and_le  (hd : 0 < d)
    (bd a ρ η )  (hN : 0 < N) :
    Integrable (finePairCountTwoGeometryEnvelope (d := d) bd a ρ η N) (fullSpatialPatchDesign d 2) ∧
    (∫ U, finePairCountTwoGeometryEnvelope bd a ρ η N U ∂fullSpatialPatchDesign d 2) ≤
      9*finePairCountTwoSpatialBudget d bd a ρ η N := by
  have hp := measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))
  refine ⟨(hp.integrable_comp_of_integrable (finePairDistanceFactor_square_integrable hN)).const_mul _, ?_⟩
  unfold finePairCountTwoGeometryEnvelope
  rw [integral_const_mul]
  have h_finePairDistanceFactor_square_integral_le : (∫ xy : Covariate d × Covariate d, (finePairDistanceFactor N xy.1 xy.2)^2
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      6 * 2^d * spatialExponentialConstant d / N^d := by
    have he : Integrable (fun xy : Covariate d × Covariate d =>
        Real.exp (-(N * exactEuclideanDistance xy.1 xy.2)))
        ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) :=
      Integrable.of_bound
        (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun xy => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
            (mul_nonneg hN.le (exactEuclideanDistance_nonneg _ _))))
    have hi := integral_mono (finePairDistanceFactor_square_integrable hN) (he.const_mul 6)
      (fun xy => finePairDistanceFactor_square_absorption hN.le xy.1 xy.2)
    rw [integral_const_mul] at hi
    exact hi.trans ((mul_le_mul_of_nonneg_left (spatialPatchBox_pair_exponential_integral_le hd hN)
      (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by ring))
  have hInt  :=
    (hp.integral_comp (MeasurableEquiv.finTwoArrow : (Fin 2 → Covariate d) ≃ᵐ (Covariate d × Covariate d)).measurableEmbedding _).trans_le
      h_finePairDistanceFactor_square_integral_le
  exact (mul_le_mul_of_nonneg_left hInt (by positivity : 0 ≤ 9*(η^2*bd^2*((2*ρ+a)/a^2)^2)^2)).trans_eq
    (by unfold finePairCountTwoSpatialBudget; ring)
theorem finePairCountTwoRawNumerator_sum_square_le_geometry  [NeZero d] (hF : 3 ≤ F)
    (ad bd T0 N ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η ρ ) (hC : C ≠ 0) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (U ) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p g w ) (hp : ∀ i, p i ∈ Icc ad bd) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ)
    (hf : ∀ i, |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ) :
    (∑ y : Fin 2 → Fin 3, (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y)^2) ≤
      finePairCountTwoGeometryEnvelope bd a ρ η N U :=
    have h_finePairCountTwoRawNumerator_sum_square_le : (∑ y : Fin 2 → Fin 3,
        (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y)^2) ≤
        9 * (η^2 * bd^2 * ((2*ρ+a)/a^2)^2)^2 * (finePairDistanceFactor N (U 0) (U 1))^2 := by
      have hy (y : Fin 2 → Fin 3) :
          (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y)^2 ≤
          ((η^2 * bd^2 * ((2*ρ+a)/a^2)^2) * finePairDistanceFactor N (U 0) (U 1))^2 := by
        have h_finePairCountTwoRawNumerator_abs_le : |finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y| ≤
          η^2 * bd^2 * ((2*ρ+a)/a^2)^2 * finePairDistanceFactor N (U 0) (U 1) := by
          unfold finePairCountTwoRawNumerator
          rw [finePairThreeRow_count_two_numerator hF ad bd T0 N haD hab hT0 hN D M q hD hM hq
            C a V η hC U hU p hp g w c y]
          exact fine_pair_scalar_product_abs_le η bd ((2*ρ+a)/a^2) (finePairDistanceFactor N (U 0) (U 1))
            _ _ _ _ _ _ (haD.trans hab).le (by positivity)
            (finePairDistanceFactor_nonneg (hT0.trans hN) _ _) (hw 0) (hw 1)
            (by rw [abs_of_pos (haD.trans_le (hp 0).1)]; exact (hp 0).2)
            (by rw [abs_of_pos (haD.trans_le (hp 1).1)]; exact (hp 1).2)
            (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf 0) (y 0))
            (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf 1) (y 1))
        have h := h_finePairCountTwoRawNumerator_abs_le
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (finePairDistanceFactor_nonneg (hT0.trans hN) _ _))).mpr h
      exact (Finset.sum_le_sum (fun y _ => hy y)).trans_eq (by simp; ring)
    h_finePairCountTwoRawNumerator_sum_square_le
end
variable {d n F M R D : ℕ}
def ordinaryFineAliasAmplitudeFactor (n M R q : ℕ) (ad bd c0 C a rho eta : ℝ) : ℝ :=
  (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
    Real.exp (M*shrunkDensityExponent ad bd M) *
      ordinaryAliasResponseConstant q C a rho * n^2 * eta^2
def ordinaryFineAliasGeometryKernel  (r : ℕ) (L T : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
      (spatialSubsetConfiguration S U))
def ordinaryFineAliasFamilyResponseSquareEnvelope  (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  3^n *
    (∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r L (T r) U)^2
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg  (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ) (U : Fin n → Covariate d) :
    0 ≤ ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  unfold ordinaryFineAliasFamilyResponseSquareEnvelope
  positivity
theorem ordinaryFineAliasGeometryKernel_measurable  (r ) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 1 ≤ T) :
    Measurable (ordinaryFineAliasGeometryKernel (d := d) (n := n) (F := F) r L T) := by
  exact Finset.measurable_sum _ (fun S _ => Finset.measurable_sum _
    (fun gamma _ => Finset.measurable_sum _ (fun beta _ =>
      ((integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT gamma beta).measurable.abs).comp
        (spatialSubsetConfiguration_measurable S))))
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_dominates 
    (I ad bd c0 L T) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hI : ∀ r ∈ I, 1 ≤ r ∧ r ≤ R)
    (q ) (hn : 1 ≤ n) (C a V eta rho ) (hC : 1 ≤ C) (ha : 0 < a)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho) (hetarho : eta ≤ rho/2)
    (U ) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : (Fin n → Fin 3) → Fin n → ℝ)
    (c : (Fin n → Fin 3) → HighFrameIndex d F → ℝ)
    (hpD : ∀ y i, p y i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ y i, |g y i| ≤ rho/2) (hw : ∀ y i, |w y i| ≤ 1)
    (hc : ∀ y, ∑ gamma, |c y gamma| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3,
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
        L T M q C a V eta U (p y) (g y) (w y) (c y) y^2) ≤
      ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  let H := ∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hb (y : Fin n → Fin 3) :
      |ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y| ≤ H := by
    apply (Finset.abs_sum_le_sum_abs _ I).trans
    exact Finset.sum_le_sum (fun r hr =>
      ordinaryFineAliasRawAction_abs_bound_of_chart ad bd c0 (spatialInterpolationLambda d) L (T r)
        haD hshrink htau (hI r hr).1 (hI r hr).2 q hn C a V eta rho hC ha heta hrho hetarho
        U hU (p y) (g y) (w y) (hpD y) (hg y) (hw y) (c y) (hc y) hp y)
  have hsq (y : Fin n → Fin 3) :
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y^2 ≤ H^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hb y))).mpr (hb y)
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin n → Fin 3))) => hsq y)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ordinaryFineAliasFamilyResponseSquareEnvelope, H] using hs
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le 
    (hd : 5 ≤ d) (I : Finset ℕ) (hI : ∀ r ∈ I, 2 ≤ r ∧ r ≤ R)
    (ad bd c0 C a rho eta D K N : ℝ) (hbd : 0 ≤ bd)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M)
    (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) (T : ℕ → ℝ)
    (hLT : ∀ r ∈ I, N*Real.exp (-c0*D) ≤ T r) (q : ℕ) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T) (fullSpatialPatchDesign d n) ∧
    (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T U ∂fullSpatialPatchDesign d n) ≤
      ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho *
        eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialResponseBase d bd)^n := by
  let f := fun r (U : Fin n → Covariate d) =>
    ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r (N*Real.exp (-c0*D)) (T r) U
  let B := ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho *
    eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
      Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have := ordinaryAliasSpatialPrefactor_nonneg d q R ad bd c0 C a rho
    unfold ordinaryAliasSpatialCountBase
    positivity
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hell (hell.trans (hLT r hr))).const_mul _
  have hk (r) (hr : r ∈ I) := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
    hd (hI r hr).1 hell (hell.trans (hLT r hr)) (hLT r hr)
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U^2) (fullSpatialPatchDesign d n) := by
    have h := (hk r hr).1.const_mul ((ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)^2)
    convert h using 1
    funext U
    dsimp [f, ordinaryFineAliasGeometryKernel]
    ring
  have hb (r) (hr : r ∈ I) : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤ B := by
    have h : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤
        ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) := by
      have hid : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) =
          (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)^2 *
            (∫ U, (ordinaryFineAliasGeometryKernel (F := F) r (N*Real.exp (-c0*D)) (T r) U)^2
              ∂fullSpatialPatchDesign d n) := by
        rw [← integral_const_mul]
        congr 1
        funext U
        ring
      rw [hid]
      exact (mul_le_mul_of_nonneg_left (hk r hr).2 (sq_nonneg _)).trans_eq (by
        unfold ordinaryFineAliasSpatialBudget ordinaryFineAliasAmplitudeFactor
        ring)
    exact h.trans (ordinaryFineAliasSpatialBudget_source_scale_le hd (hI r hr).2 hbd hD hK hc0
      hDK hN hell hH q)
  have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) I f hm hi
  have hupper : ∀ U, (∑ r ∈ I, f r U)^2 ≤ (∑ r ∈ I, |f r U|)^2 := by
    intro U
    have hb := Finset.abs_sum_le_sum_abs (fun r => f r U) I
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr hb
  have hs := h.mono' ((Finset.measurable_sum I hm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => by simpa only [Real.norm_eq_abs, abs_sq] using hupper U))
  have hcard : I.card^2 ≤ (R+1 : ℝ)^2 := by
    have hsub : I ⊆ Finset.range (R+1) := fun r hr => Finset.mem_range.mpr (by have := (hI r hr).2; omega)
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact_mod_cast Nat.pow_le_pow_left h 2
  have hsum := (finite_sum_square_integral_le (fullSpatialPatchDesign d n) I f B hm hi hb).trans
    (mul_le_mul_of_nonneg_right hcard hB)
  refine ⟨hs.const_mul ((3 : ℝ)^n), ?_⟩
  rw [show (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T U ∂fullSpatialPatchDesign d n) =
      (3 : ℝ)^n * (∫ U, (∑ r ∈ I, f r U)^2 ∂fullSpatialPatchDesign d n) by
    rw [← integral_const_mul]; rfl]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (3 : ℝ)^n)).trans_eq (by
    unfold B ordinaryAliasFamilySpatialPrefactor ordinaryAliasSpatialResponseBase
    rw [mul_pow]
    ring)
theorem highCardinalRawNumerator_eq_matrix_heat 
    (ad bd lam ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
     (hT : 1 ≤ T) (m D q ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η ) (hC : C ≠ 0)
    (U ) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      (∏ i, p i)*responseMatrixAction q C (integratedCardinalMatrix lam T U) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2*(∏ i, p i)*∑ i, (w i)^2*highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
  rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hC U hU p g w hp c y, integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
  ring
 theorem completeSourceRawNumerator_higher_components  [NeZero d]
    (ad bd lam ℓ N μ ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hℓ : 1 ≤ ℓ)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N μ)
    (hFine : ∀ j : Fin (D-2), ℓ < higherBandTargetScale d (j.val+3) N μ → j.val+3 ≤ M)
    (C a V η : ℝ) (hC : C ≠ 0) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      highCardinalRawNumerator ad bd lam (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y +
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0) +
      (if M<n then finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) := by
  let j : Fin (D-2) := ⟨n-3, by omega⟩
  have hj : j.val+3 = n := by dsimp [j]; omega
  have hmat : integratedCardinalMatrix (D := D) lam (max 1 (higherBandTargetScale d n N μ)) U =
      integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U := by
    funext γ δ
    exact integrated_cardinal_matrix_max_one (by omega) lam (by simpa only [hj] using hnu j) U γ δ
  have h_completeSourceRawNumerator_higher : completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
      finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
    unfold completeSourceRawNumerator
    have h_completeSourceSignedFirstAction_higher (Φ : (HighFrameIndex d D → ℝ) → ℝ) : completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c Φ =
        higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ +
          finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
          finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
      have h_finePairThreeRowFirstAction_higher : finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ =
          finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
            finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
        have hu : finePairUnitFirstAction ad bd D q C p c Φ = 0 :=
          ordinaryPairPacket_zero_other_count hn (Measure.dirac ()) ad bd haD hab D D q hnD hnD C
            (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _) c p hp
            (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num) Φ
        have hc : finePairCoarseFirstAction ad bd ℓ D q C U p c Φ = 0 :=
          ordinaryPairPacket_zero_other_count hn _ ad bd haD hab D D q hnD hnD C _
            (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _) c p hp
            (fun ζ i => finePairTimeFieldValue ζ (U i))
            (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
            (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
        rw [finePairThreeRowFirstAction, hu, hc,
          finePairFineFirstAction_alias_even_field ad bd ℓ N haD hab M q C U p hp c Φ]
        ring
      rw [completeSourceSignedFirstAction_eq_family,
        singletonFirstAction_zero_other_count ad bd haD hab D q (by omega) hnD (by omega) C p hp c Φ,
        h_finePairThreeRowFirstAction_higher]
      ring
    rw [h_completeSourceSignedFirstAction_higher]
  have h_higherBandFamilyFirstAction_matched_and_full_fine_alias : higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0) := by
    have h_higherBandFamilyFirstAction_matched_and_alias_raw : higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
        (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U) c
          (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
        ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ℓ N μ).filter (fun r => r<n))
          ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y := by
      have h_higherBandFine_below_eq_alias_family : (∑ j : Fin (D-2), if j.val+3 < n then
        higherBandFineFirstAction ad bd lam ℓ N μ (j.val+3) M D q C U p c
          (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0) =
        ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ℓ N μ).filter (fun r => r<n))
          ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y := by
        have hD : 1 ≤ D := by omega
        unfold higherBandFineFirstAction
        have he : (∑ j : Fin (D-2), if j.val+3 < n then
            (if ℓ < higherBandTargetScale d (j.val+3) N μ then
              higherBandFirstAction ad bd lam ℓ (higherBandTargetScale d (j.val+3) N μ) (j.val+3) M D q C true U p c
                (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0) else 0) =
            ∑ j : Fin (D-2), if j.val+3 < n then
              (if ℓ < higherBandTargetScale d (j.val+3) N μ then
                ordinaryFineAliasRawAction ad bd lam ℓ (higherBandTargetScale d (j.val+3) N μ)
                  M (j.val+3) q C a V η U p g w c y else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs with hn ha'
          have h_higherBandFirstAction_fine_eq_aliasRawAction (L) (T) (hL : 0 < L) (hT : 1 ≤ T) (r) (hr : 2 ≤ r) : higherBandFirstAction ad bd lam L T r M D q C true U p c
              (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
              ordinaryFineAliasRawAction ad bd lam L T M r q C a V η U p g w c y := by
            rw [higherBandFirstAction_actual_count_expansion ad bd lam L T haD hab hlam hL hT
              r M D q hr hD hnD C true U hU p hp c]
            simp only [ordinaryFineAliasRawAction, higherBandActualMatrix, ite_true]
          · exact (h_higherBandFirstAction_fine_eq_aliasRawAction ℓ _ (by linarith) (hℓ.trans ha'.le) (j.val+3) (by omega))
          · rfl
          · rfl
        rw [he]
        have hi (j : Fin (D-2)) :
            (if j.val+3 < n then (if ℓ < higherBandTargetScale d (j.val+3) N μ then (fun r => ordinaryFineAliasRawAction ad bd lam ℓ (higherBandTargetScale d r N μ) M r q C a V η U p g w c y) (j.val+3) else 0) else 0) =
            if j.val+3 < n ∧ ℓ < higherBandTargetScale d (j.val+3) N μ then (fun r => ordinaryFineAliasRawAction ad bd lam ℓ (higherBandTargetScale d r N μ) M r q C a V η U p g w c y) (j.val+3) else 0 := by
          by_cases hn : j.val+3 < n <;> by_cases haD : ℓ < higherBandTargetScale d (j.val+3) N μ <;> simp [hn,haD]
        simp_rw [hi]
        rw [← Finset.sum_filter]
        apply Finset.sum_bij (fun j _ => j.val+3)
        · intro j hj
          have hg := (Finset.mem_filter.mp hj).2
          apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_range.mpr (by have := j.isLt; omega), by omega, hg.2⟩
          · exact hg.1
        · intro j hj j' hj' he
          apply Fin.ext
          omega
        · intro r hr
          have hr' := Finset.mem_filter.mp hr
          have hI := Finset.mem_filter.mp hr'.1
          have := Finset.mem_range.mp hI.1
          let j : Fin (D-2) := ⟨r-3, by omega⟩
          have hj : j.val+3 = r := by dsimp [j]; omega
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by simpa only [hj] using And.intro hr'.2 hI.2.2⟩, hj⟩
        · intro j hj
          rfl
      have h_higherBandFamilyFirstAction_matched_and_fine_below (ell : ℝ) (hell : 1 ≤ ell) (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N μ → j.val+3 ≤ M) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : higherBandFamilyFirstAction ad bd lam ell N μ D M q C U p c Φ =
          (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U) c Φ +
          ∑ j : Fin (D-2), if j.val+3 < n then
            higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ else 0 := by
        have hD : 1 ≤ D := by omega
        have hell0 : 0 < ell := by linarith
        let b : Fin (D-2) := ⟨n-3, by omega⟩
        have hb : b.val+3 = n := by dsimp [b]; omega
        have hcSum : (∑ j : Fin (D-2), higherBandCoarseFirstAction ad bd lam ell N μ (j.val+3) D q C U p c Φ) =
            higherBandCoarseFirstAction ad bd lam ell N μ n D q C U p c Φ := by
          calc
            _ = higherBandCoarseFirstAction ad bd lam ell N μ (b.val+3) D q C U p c Φ := by
              apply Finset.sum_eq_single b
              · intro j _ hj
                have hr : 1 ≤ (j.val+3) := by omega
                have hnu  := hnu j
                unfold higherBandCoarseFirstAction
                by_cases hT : 1 ≤ min ell (higherBandTargetScale d (j.val+3) N μ)
                · exact higherBandFirstAction_zero_other_count ad bd lam ell _ haD hab hT (j.val+3) D D q hr hD hnD hnD (by intro h; apply hj; apply Fin.ext; omega) C false U hU p hp c Φ
                · unfold higherBandFirstAction
                  rw [higherBand_coarse_below_one_signed_zero d (j.val+3) D D q ad bd C lam ell _ (lt_min hell0 hnu) (not_le.mp hT)]
                  simp
              · intro hb'
                exact False.elim (hb' (Finset.mem_univ b))
            _ = _ := by rw [hb]
        have hfPoint (j : Fin (D-2)) :
            higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ =
              (if j = b then higherBandFineFirstAction ad bd lam ell N μ n M D q C U p c Φ else 0) +
              (if j.val+3 < n then higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ else 0) := by
          by_cases hj : j = b
          · subst j
            simp only [hb, ite_true, lt_self_iff_false, ite_false, add_zero]
          · by_cases hlt : j.val+3 < n
            · simp only [ite_eq_right hj, ite_eq_left hlt, zero_add]
            · have hgt : n < j.val+3 := by
                have : j.val+3 ≠ n := by
                  intro he
                  apply hj
                  apply Fin.ext
                  omega
                omega
              have h_higherBandFineFirstAction_zero_small_count : higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ = 0 := by
                have hr : 1 ≤ (j.val+3) := by omega
                unfold higherBandFineFirstAction
                split_ifs with hactive
                · exact higherBandFirstAction_zero_small_count ad bd lam ell _ haD hab (hell.trans hactive.le)
                    (j.val+3) M D q hr hD hnD hgt C true U hU p hp c Φ
                · rfl
              have hz := h_higherBandFineFirstAction_zero_small_count
              simp only [ite_eq_right hj, ite_eq_right hlt, add_zero, hz]
        have hfSum : (∑ j : Fin (D-2), higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ) =
            higherBandFineFirstAction ad bd lam ell N μ n M D q C U p c Φ +
            ∑ j : Fin (D-2), if j.val+3 < n then
              higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ else 0 := by
          calc
            _ = ∑ j : Fin (D-2), ((if j = b then higherBandFineFirstAction ad bd lam ell N μ n M D q C U p c Φ else 0) +
              (if j.val+3 < n then higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ else 0)) :=
                Finset.sum_congr rfl (fun j _ => hfPoint j)
            _ = _ := by rw [Finset.sum_add_distrib]; simp
        have hnupos : 0 < higherBandTargetScale d n N μ := by simpa only [hb] using hnu b
        have hFineN : ell < higherBandTargetScale d n N μ → n ≤ M := by simpa only [hb] using hFine b
        have h_higherBandFamilyFirstAction_coarse_fine : higherBandFamilyFirstAction ad bd lam ell N μ D M q C U p c Φ =
            (∑ j : Fin (D-2), higherBandCoarseFirstAction ad bd lam ell N μ (j.val+3) D q C U p c Φ) +
            (∑ j : Fin (D-2), higherBandFineFirstAction ad bd lam ell N μ (j.val+3) M D q C U p c Φ) := by
          have h_higherBandFamilyFirstAction_eq_physical : (∑ i : HigherBandFamilyIndex d D M q ad bd C lam ell N μ,
              higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N μ i.val)
                (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ) =
              ∑ i : Fin (D-2) × Bool, higherBandPhysicalFirstAction ad bd lam ell N μ D M q C U p c Φ i := by
            let F := fun (i : Fin (D-2) × Bool)
                (e : HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2) =>
              highPacketObservable ad bd (higherBandFamilyGuardDegree M i) (higherBandFamilyTarget i) D q C c
                (fun ζ z eps => ∏ j, localDensityReset ad bd (higherBandFamilyTarget i) z eps p
                  (fun j l => higherBandCarrierFactor d (higherBandFamilyTarget i) lam i.2 ζ l (U j)) j) Φ e
            classical
            exact (Finset.sum_congr_set {i | HigherBandFamilySelected d D M q ad bd C lam ell N μ i}
              (higherBandPhysicalIntegral d D M q ad bd C lam ell N μ F)
              (fun i => higherBandFamilyRowIntegral d D M q ad bd C lam ell N μ F i.val)
              (fun i hi => higherBandPhysicalIntegral_selected d D M q ad bd C lam ell N μ F i hi)
              (fun i hi => higherBandPhysicalIntegral_unselected_zero d D M q ad bd C lam ell N μ hell hnu hFine F i hi)).symm
          rw [higherBandFamilyFirstAction, h_higherBandFamilyFirstAction_eq_physical,
            Fintype.sum_prod_type]
          simp only [Fintype.sum_bool, higherBandPhysicalFirstAction, higherBandFamilyTarget,
            higherBandFamilyUpper, higherBandFamilyGuardDegree, Bool.false_eq_true, ite_false, ite_true,
            higherBandCoarseFirstAction, higherBandFineFirstAction, Finset.sum_add_distrib]
          exact add_comm _ _
        have h_higherBand_matched_coarse_fine : higherBandCoarseFirstAction ad bd lam ell N μ n D q C U p c Φ +
            higherBandFineFirstAction ad bd lam ell N μ n M D q C U p c Φ =
            (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U) c Φ := by
          have hn : 2 ≤ n := by omega
          have hell0 : 0 < ell := by linarith
          by_cases hT : 1 ≤ higherBandTargetScale d n N μ
          · have hc := higherBandFirstAction_target_count ad bd lam ell (min ell (higherBandTargetScale d n N μ))
              haD hab hlam hell0 (le_min hell hT) D D q hn hD hnD hnD C false U hU p hp c Φ
            unfold higherBandCoarseFirstAction higherBandFineFirstAction
            rw [hc]
            by_cases hactive : ell < higherBandTargetScale d n N μ
            · rw [ite_eq_left hactive, higherBandFirstAction_target_count ad bd lam ell _ haD hab hlam hell0 hT
                M D q hn hD hnD (hFineN hactive) C true U hU p hp c Φ]
              simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
                min_eq_left hactive.le, globalCardinalBandMatrix]
              rw [← mul_add, ← responseMatrixAction_matrix_add]
              congr 2
              funext i j
              unfold globalCardinalBandMatrix
              ring
            · rw [ite_eq_right hactive]
              simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, min_eq_right (le_of_not_gt hactive), add_zero]
          · have hTlt := not_le.mp hT
            have hmin  :=
              min_eq_right (hTlt.le.trans hell)
            unfold higherBandCoarseFirstAction higherBandFineFirstAction higherBandFirstAction
            rw [higherBand_coarse_below_one_signed_zero d n D D q ad bd C lam ell _ (lt_min hell0 hnupos)
              (by rw [hmin]; exact hTlt)]
            have hactive : ¬ell < higherBandTargetScale d n N μ := by linarith
            rw [ite_eq_right hactive]
            simp only [VectorMeasure.integral_zero_vectorMeasure, add_zero]
            have hmat : (integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U : HighFrameIndex d D → _ → ℝ) =
                fun _ _ => 0 := by
              funext i j
              exact integrated_cardinal_matrix_below_one_eq_zero ⟨0, by omega⟩ lam hnupos hTlt U i j
            have h_responseMatrixAction_matrix_zero : responseMatrixAction q C (fun _ _ => 0) c Φ = 0 := by
              simp [responseMatrixAction, covarianceAction, covarianceWeight]
            rw [hmat, h_responseMatrixAction_matrix_zero, mul_zero]
        rw [h_higherBandFamilyFirstAction_coarse_fine, hcSum, hfSum,
          ← add_assoc, h_higherBand_matched_coarse_fine]
      rw [h_higherBandFamilyFirstAction_matched_and_fine_below ℓ hℓ hFine,
        h_higherBandFine_below_eq_alias_family]
    rw [h_higherBandFamilyFirstAction_matched_and_alias_raw]
    by_cases hnM : M<n
    have h_ordinaryFineAliasTargetSet_below_eq : (ordinaryFineAliasTargetSet d D ℓ N μ).filter (fun r => r<n) = ordinaryFineAliasTargetSet d D ℓ N μ := by
      apply Finset.filter_eq_self.mpr
      intro r hr
      have htarget := Finset.mem_filter.mp hr
      have := Finset.mem_range.mp htarget.1
      let j : Fin (D-2) := ⟨r-3, by omega⟩
      have hj : j.val+3 = r := by dsimp [j]; omega
      have hactive : ℓ < higherBandTargetScale d (j.val+3) N μ := by simpa only [hj] using htarget.2.2
      have hm := hFine j hactive
      rw [hj] at hm
      omega
    · rw [ite_eq_left hnM, h_ordinaryFineAliasTargetSet_below_eq]
    have h_ordinaryFineAliasFamilyRawAction_below_eq_zero : ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ℓ N μ).filter (fun r => r<n))
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y = 0 := by
      have hnM  := le_of_not_gt hnM
      apply Finset.sum_eq_zero
      intro r hr
      have hfilter := Finset.mem_filter.mp hr
      have htarget := Finset.mem_filter.mp hfilter.1
      have hr1 : 1 ≤ r := by have := htarget.2.1; omega
      have hnr  := hfilter.2
      unfold ordinaryFineAliasRawAction
      rw [densityCountCoefficient_exact ad bd haD hab M r n hr1 hnr.le hnM, if_neg (by omega : n ≠ r), zero_mul]
    · rw [ite_eq_right hnM, h_ordinaryFineAliasFamilyRawAction_below_eq_zero]
  rw [h_completeSourceRawNumerator_higher,
    h_higherBandFamilyFirstAction_matched_and_full_fine_alias,
    highCardinalRawNumerator_eq_matrix_heat ad bd lam haD hab hlam (le_max_left _ _) D D q (by omega) hnD hnD hnD
      C a V η hC U hU p g w hp c y, hmat]
  by_cases hnM : M<n
  · simp only [if_pos hnM]
    ring
  have h_finePairPairAliasAction_zero_selected_count {n} {d} {F} (T0) (hn : 3 ≤ n) (hM : n ≤ M) (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) : finePairPairAliasAction ad bd T0 N M q C U p c Φ = 0 := by
    apply Finset.sum_eq_zero
    intro W _
    by_cases hW : W.card = 2
    have h_finePairCountCoefficient_two_exact (hk : 2 ≤ n) : finePairCountCoefficient ad bd M n 2 = if n = 2 then 1 else 0 := by
      have h_finePairCountCoefficient_two : finePairCountCoefficient ad bd M n 2 = densityCountCoefficient ad bd M 2 n := by
        unfold finePairCountCoefficient finePairDensityPrefactor densityCountCoefficient
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro h _
        field_simp [densityMargin_zero_ne ad bd haD hab, (haD.trans hab).ne']
      rw [h_finePairCountCoefficient_two]
      exact densityCountCoefficient_exact ad bd haD hab M 2 n (by omega) hk hM
    · rw [hW, h_finePairCountCoefficient_two_exact (by omega)]
      simp [show n ≠ 2 by omega]
    · simp [hW]
  · rw [if_neg hnM, h_finePairPairAliasAction_zero_selected_count ℓ hn (le_of_not_gt hnM) U p c]
    simp only [if_neg hnM]
    ring
 def completeSourceHigherGeometryEnvelope  (aD bD c0 ℓ N μ : ℝ)
    (M R q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) : ℝ :=
  4*(cardinalGeometryEnvelope (F := D) q (bD-(M : ℝ)⁻¹) C a ρ η (max 1 (higherBandTargetScale d n N μ)) U +
    (if M<n then ordinaryFineAliasFamilyResponseSquareEnvelope (F := D) (ordinaryFineAliasTargetSet d D ℓ N μ)
      M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U else 0) +
    (if M<n then finePairAliasGeometryEnvelope (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U else 0) +
    fineFieldGeometryEnvelope (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U)
 theorem completeSourceHigherGeometryEnvelope_nonneg  (aD bD c0 ℓ N μ : ℝ)
    (M R q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) :
    0 ≤ completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η U := by
  unfold completeSourceHigherGeometryEnvelope
  have hA := cardinalGeometryEnvelope_nonneg (F := D) q (bD-(M : ℝ)⁻¹) C a ρ η (max 1 (higherBandTargetScale d n N μ)) U
  have := ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg (F := D) (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U
  have h_finePairAliasGeometryEnvelope_nonneg : 0 ≤ finePairAliasGeometryEnvelope (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U := by
    unfold finePairAliasGeometryEnvelope; positivity
  have := h_finePairAliasGeometryEnvelope_nonneg
  have hF := fineFieldGeometryEnvelope_nonneg (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N M q C a ρ η U
  split_ifs <;> positivity
 theorem completeSourceRawNumerator_higher_square_le_geometry  [NeZero d]
    (aD bD c0 ℓ N μ : ℝ) (haD : 0 < aD) (hℓ : 1 ≤ ℓ) (D M R q : ℕ)
    (hshrink : aD+(M : ℝ)⁻¹ < bD-(M : ℝ)⁻¹) (htau : shrunkDensityExponent aD bD M ≤ c0)
    (hn : 3 ≤ n) (hnD : n ≤ D) (hq : 1 ≤ q)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N μ)
    (hFine : ∀ j : Fin (D-2), ℓ < higherBandTargetScale d (j.val+3) N μ → j.val+3 ≤ M)
    (hI : ∀ r ∈ ordinaryFineAliasTargetSet d D ℓ N μ, 1 ≤ r ∧ r ≤ R)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹))
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1) (c : HighFrameIndex d D → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, completeSourceRawNumerator (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹)
      (spatialInterpolationLambda d) ℓ N μ D M q C a V η U p g w c y^2) ≤
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η U := by
  let ad := aD+(M : ℝ)⁻¹
  let bd := bD-(M : ℝ)⁻¹
  have had : 0 < ad := by dsimp [ad]; positivity
  let A := fun y => highCardinalRawNumerator ad bd (spatialInterpolationLambda d)
    (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y
  let B := fun y => if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
    ad bd (spatialInterpolationLambda d) ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0
  let P := fun y => if M<n then finePairPairAliasAction ad bd ℓ N M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0
  let F := fun y => finePairEvenFieldAction ad bd ℓ N M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)
  have hA := highCardinalRawNumerator_sum_square_le_geometry (T := max 1 (higherBandTargetScale d n N μ)) ad bd had hshrink (le_max_left _ _) D D q
    (by omega) hnD hnD hnD hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp
  have hB : (∑ y, B y^2) ≤ (if M<n then ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
      (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U else 0) := by
    by_cases hMn : M<n
    · simp only [B, if_pos hMn]
      exact ordinaryFineAliasFamilyResponseSquareEnvelope_dominates _ aD bD c0 ℓ _ haD hshrink htau hI q
        (by omega) C a V η ρ hC ha hη hρ hηρ U hU (fun _ => p) (fun _ => g) (fun _ => w) (fun _ => c)
          (fun _ => hpD) (fun _ => hg) (fun _ => hw) (fun _ => hc) hp
    · simp [B, hMn]
  have hP : (∑ y, P y^2) ≤ (if M<n then finePairAliasGeometryEnvelope ad bd ℓ N M q C a ρ η U else 0) := by
    by_cases hMn : M<n
    · simp only [P, if_pos hMn]
      have hn : 1 ≤ n := by omega
      let K := finePairDensityCoefficientBudget ad bd M n *
        (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2)
      let s := (Finset.univ : Finset (Fin n)).powersetCard 2
      let Z := ∑ S ∈ s, |finePairTimeSubsetMoment ℓ N U S|
      have hy (y : Fin n → Fin 3) : finePairPairAliasAction ad bd ℓ N M q C U p c
          (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2 ≤ K^2*Z^2 := by
        have h_finePairPairAliasAction_abs_bound_of_chart : |finePairPairAliasAction ad bd ℓ N M q C U p c
            (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
            finePairDensityCoefficientBudget ad bd M n *
              (finePairResponseActionBudget d q C a ρ * n^2 * η^2) *
                ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
                  if W.card = 2 then |finePairTimeSubsetMoment ℓ N U W| else 0 := by
          unfold finePairPairAliasAction
          exact fine_pair_filtered_sum_abs_bound ((Finset.univ : Finset (Fin n)).powerset) (fun W => W.card = 2)
            (fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i)
            (fun W => finePairTimeSubsetMoment ℓ N U W) _ _ _
            (finePairDensityCoefficientBudget_nonneg ad bd (had.trans hshrink).le M n)
            (fun W _ => finePairCountCoefficient_product_bound ad bd had hshrink M p hpD W)
            (finePairDistance_response_bound_of_chart q hn C a V η ρ hC ha hη hρ hηρ U hU g w c y hc hg hw hp)
        have h := h_finePairPairAliasAction_abs_bound_of_chart
        have he : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            if S.card = 2 then |finePairTimeSubsetMoment ℓ N U S| else 0) = Z := by
          dsimp [Z, s]
          rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
        rw [he] at h
        change |_| ≤ K*Z at h
        simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
      exact (Finset.sum_le_sum (s := Finset.univ) (fun y _ => hy y)).trans_eq (by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        unfold finePairAliasGeometryEnvelope
        dsimp [K, Z, s]
        ring)
    · simp [P, hMn]
  have h_finePairEvenFieldAction_sum_square_le_geometry : (∑ y : Fin n → Fin 3, finePairEvenFieldAction ad bd ℓ N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2) ≤
        fineFieldGeometryEnvelope ad bd ℓ N M q C a ρ η U := by
    have hn : 1 ≤ n := by omega
    let K := finePairDensityCoefficientBudget ad bd M n *
      (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2)
    let s := ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card)
    let Z := ∑ S ∈ s, |finePairTimeSubsetMoment ℓ N U S|
    have hy (y : Fin n → Fin 3) : finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)^2 ≤ K^2*Z^2 := by
      have h_finePairEvenFieldAction_abs_bound_of_chart : |finePairEvenFieldAction ad bd ℓ N M q C U p c
          (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
          finePairDensityCoefficientBudget ad bd M n *
            (finePairResponseActionBudget d q C a ρ * n^2 * η^2) *
              ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
                if 4 ≤ W.card ∧ Even W.card then |finePairTimeSubsetMoment ℓ N U W| else 0 := by
        unfold finePairEvenFieldAction
        exact fine_pair_filtered_sum_abs_bound ((Finset.univ : Finset (Fin n)).powerset) (fun W => 4 ≤ W.card ∧ Even W.card)
          (fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i)
          (fun W => finePairTimeSubsetMoment ℓ N U W) _ _ _
          (finePairDensityCoefficientBudget_nonneg ad bd (had.trans hshrink).le M n)
          (fun W _ => finePairCountCoefficient_product_bound ad bd had hshrink M p hpD W)
          (finePairDistance_response_bound_of_chart q hn C a V η ρ hC ha hη hρ hηρ U hU g w c y hc hg hw hp)
      have h := h_finePairEvenFieldAction_abs_bound_of_chart
      have he : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          if 4 ≤ S.card ∧ Even S.card then |finePairTimeSubsetMoment ℓ N U S| else 0) = Z := by
        dsimp [Z, s]
        rw [Finset.sum_filter]
      rw [he] at h
      change |_| ≤ K*Z at h
      simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
    exact (Finset.sum_le_sum (s := Finset.univ) (fun y _ => hy y)).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      unfold fineFieldGeometryEnvelope
      dsimp [K, Z, s]
      ring)
  have hF := h_finePairEvenFieldAction_sum_square_le_geometry
  have hb (y : Fin n → Fin 3) : completeSourceRawNumerator ad bd (spatialInterpolationLambda d) ℓ N μ
      D M q C a V η U p g w c y^2 ≤ 4*(A y^2+B y^2+P y^2+F y^2) := by
    rw [completeSourceRawNumerator_higher_components ad bd _ ℓ N μ had hshrink (by unfold spatialInterpolationLambda; positivity) hℓ D M q hn hnD
      hnu hFine C a V η (lt_of_lt_of_le zero_lt_one hC).ne' U hU p g w hpD c y]
    nlinarith only [sq_nonneg (A y-B y), sq_nonneg (P y-F y), sq_nonneg (A y+B y-P y-F y)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hb y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  exact h.trans (by
    unfold completeSourceHigherGeometryEnvelope
    convert mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hB) hP) hF)
      (by norm_num : (0 : ℝ) ≤ 4) using 1)
 theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable 
    (hd : 5 ≤ d) (I M R q ad bd c0 C a ρ η L T) (hL : 1 ≤ L) (hI : ∀ r ∈ I, 2 ≤ r ∧ L ≤ T r) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a ρ η L T) (fullSpatialPatchDesign d n) := by
  let f := fun r (U : Fin n → Covariate d) => ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hL (hL.trans (hI r hr).2)).const_mul _
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U^2) (fullSpatialPatchDesign d n) := by
    have h := (ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
      hd (hI r hr).1 hL (hL.trans (hI r hr).2) (hI r hr).2).1.const_mul
        ((ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η)^2)
    convert h using 1
    funext U
    dsimp [f, ordinaryFineAliasGeometryKernel]
    ring
  have hs : Integrable (fun U => (∑ r ∈ I, f r U)^2) (fullSpatialPatchDesign d n) := by
    have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) I f hm hi
    apply h.mono' ((Finset.measurable_sum I hm).pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro U
    have hb := Finset.abs_sum_le_sum_abs (fun r => f r U) I
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr hb
  exact hs.const_mul (3^n)
 theorem completeSourceHigherGeometryEnvelope_integrable  [NeZero d]
    (hd : 5 ≤ d) (hn : 2 ≤ n) (aD bD c0 ℓ N μ M R q C a ρ η)
    (hℓ : 1 ≤ ℓ) (hN : ℓ ≤ N) :
    Integrable (completeSourceHigherGeometryEnvelope (d := d) (n := n) (D := D)
      aD bD c0 ℓ N μ M R q C a ρ η) (fullSpatialPatchDesign d n) := by
  have hA := (cardinalGeometryEnvelope_integrable_and_le (F := D) hd hn q (bD-(M : ℝ)⁻¹) C a ρ η
    (T := max 1 (higherBandTargetScale d n N μ)) (le_max_left _ _)).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (n := n) (F := D) hd
    (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ
    (fun r => higherBandTargetScale d r N μ) hℓ (fun r hr => by
      have h := (Finset.mem_filter.mp hr).2
      exact ⟨by omega, h.2.le⟩)
  have hP := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) hN M q C a ρ η).1
  have hF := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) M q C a ρ η).1
  unfold completeSourceHigherGeometryEnvelope
  split_ifs
  · exact (((hA.add hB).add hP).add hF).const_mul 4
  · exact by simpa only [Pi.add_apply, add_zero] using (hA.add hF).const_mul 4
def completeSourceGeometryEnvelope {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) : (n : ℕ) → (Fin n → Covariate d) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, U => finePairCountTwoGeometryEnvelope (bD-(M : ℝ)⁻¹) a rho eta N U
  | n+3, U => if n+3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
    else (3*Chi^2)^(n+3)*eta^4*(Bl+1)^2
 theorem completeSourceGeometryEnvelope_nonneg  (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) (n : ℕ) (U : Fin n → Covariate d) :
    0 ≤ completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi Bl n U := by
  rcases n with _|_|_|n
  · norm_num [completeSourceGeometryEnvelope]
  · norm_num [completeSourceGeometryEnvelope]
  · exact finePairCountTwoGeometryEnvelope_nonneg _ _ _ _ _ U
  · try simp only [completeSourceGeometryEnvelope]
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · positivity
 theorem completeSourceGeometryEnvelope_integrable  [NeZero d] (hd : 5 ≤ d)
    (D M R q aD bD c0 ell N mu C a rho eta Chi Bl)
    (hell : 1 ≤ ell) (hN : ell ≤ N) (n ) :
    Integrable (completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl n)
      (fullSpatialPatchDesign d n) := by
  rcases n with _|_|_|n
  · exact integrable_zero _ _ _
  · exact integrable_zero _ _ _
  · exact (finePairCountTwoGeometryEnvelope_integrable_and_le (by omega) _ _ _ _
      (lt_of_lt_of_le zero_lt_one (hell.trans hN))).1
  · change Integrable (fun U => if n+3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
      else (3*Chi^2)^(n+3)*eta^4*(Bl+1)^2) (fullSpatialPatchDesign d (n+3))
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_integrable hd (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ hell hN
    · exact integrable_const _
 theorem fineFieldGeometryEnvelope_count_three  (ad bd T0 N : ℝ)
    (M q : ℕ) (C a rho eta : ℝ) (U : Fin 3 → Covariate d) :
    fineFieldGeometryEnvelope ad bd T0 N M q C a rho eta U = 0 := by
  have hs : ((Finset.univ : Finset (Fin 3)).powerset).filter
      (fun S => 4 ≤ S.card ∧ Even S.card) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have := (Finset.mem_filter.mp hS).2.1
    omega
  unfold fineFieldGeometryEnvelope
  rw [hs]
  simp
end NearlyMinimax
