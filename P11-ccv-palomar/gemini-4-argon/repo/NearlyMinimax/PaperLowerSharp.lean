module
public import NearlyMinimax.CompleteSaddleEnergyGuards
public import NearlyMinimax.CompleteGeometryEnergyAssembly
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000
section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
variable {d k D M q : ℕ}
section
set_option backward.isDefEq.respectTransparency true
def sourceRowSignedMeasure (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SignedMeasure (SourceRowMark d D M q a b C lam ℓ N μ i)
  | .inl .unit => highPacketSignedMeasure (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .inl .coarse => highPacketSignedMeasure (finePairTimeFieldMeasure d 0 ℓ) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inl .fine => finePairPacketSignedMeasure (finePairTimeFieldMeasure d ℓ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inr (.inl _) => highPacketSignedMeasure (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D)
  | .inr (.inr i) => higherBandSignedRow d (higherBandFamilyTarget i.val)
      (higherBandFamilyGuardDegree M i.val) D q a b C lam ℓ
      (higherBandFamilyUpper d ℓ N μ i.val) i.val.2
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
theorem completeSourceCanonicalAction_eq_signed_first_action
    {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j h)
    (x : Fin n → Covariate d) (hx : ∀ u, x u ∈ highTorusPatch d k j)
    (Φ ) (hmΦ : Measurable Φ)
    (B : ℝ) (hB : 0 ≤ B) (hΦ : ∀ v : HighFrameIndex d D → ℝ,
      (∑ γ, |v γ|) ≤ Cfr⁻¹ → |Φ v| ≤ B) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e*
      ((∏ u, highUnionSourceResetDensity C R j h e (x u))*
        Φ (highUnionSourceResetCoefficient C R j h e)) ∂highUnionLaw R (highCenterMix C)) =
      completeSourceSignedFirstAction (C.densityLower+1/M)
        (C.densityUpper-1/↑M) lam ℓ N μ D M q Cfr
        (fun u => highLocalCoordinates d k j (x u))
        (fun u => highUnionSourceDensity C R h (x u)) ((highUnionSourceState C R h).2 j) Φ := by
  dsimp only
  let ad := C.densityLower+1/↑M
  let bd := C.densityUpper-1/↑M
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  let c := (highUnionSourceState C R h).2 j
  let p := fun u : Fin n => highUnionSourceDensity C R h (x u)
  let U := fun u : Fin n => highLocalCoordinates d k j (x u)
  let O := fun e => (∏ u, highUnionSourceResetDensity C R j h e (x u))*
    Φ (highUnionSourceResetCoefficient C R j h e)
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) :=
    highUnionMark_standardBorel
  have hmO : Measurable O := (Finset.measurable_fun_prod _ (fun u _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp
      (measurable_id.prodMk measurable_const))).mul (hmΦ.comp (measurable_pi_iff.mpr (highUnionSourceResetCoefficient_measurable C R G j h)))
  have hOb (e) : ‖O e‖ ≤ C.densityUpper^n*B := by
    change |(∏ u, highUnionSourceResetDensity C R j h e (x u))*Φ _| ≤ _
    rw [abs_mul]
    exact mul_le_mul (finite_density_product_abs_bound _ C.densityUpper
      (lt_trans zero_lt_one C.one_lt_densityUpper).le
      (fun u => highUnionSourceResetDensity_abs_le C R G j h e (x u)))
      (hΦ _ (highUnionResponseReset_ball R Cfr (by linarith) G.vector_ball G.time_interval e c (highUnionSourceState_coefficient_ball C R G h j)))
      (abs_nonneg _) (pow_nonneg (lt_trans zero_lt_one C.one_lt_densityUpper).le n)
  have hreset (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) (x u) =
      R.rowSlope j i e (x u)*p u+R.rowIntercept i e := by
    unfold highUnionSourceResetDensity highUnionSourceDensity
    rw [highUnionSourceState_append]
    change (if x u ∈ highTorusPatch d k j then R.rowSlope j i e (x u)*_+R.rowIntercept i e else _) = _
    rw [if_pos (hx u)]
    dsimp only [p]
    unfold highUnionSourceDensity
    rfl
  have hO (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) :
      O (Sum.inl ⟨i,e⟩) = (∏ u, (R.rowSlope j i e (x u)*p u+R.rowIntercept i e))*
        Φ (coefficientReset c (R.rowVector i e) (R.rowTime i e)) := by
    simp only [O,hreset,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  have h_completeSourceUnion_signed_action (L) (hFbound : ∀ e, ‖O e‖ ≤ L) : let R := completeSourceRows C k D M q Cfr lam ℓ N μ
      (∫ e, highUnionActivation R (highCenterMix C) e*O e ∂highUnionLaw R (highCenterMix C)) =
        ∑ i, ∫ᵛ e, O (Sum.inl ⟨i,e⟩)
          ∂<•sourceRowSignedMeasure d k D M q (C.densityLower+1/M)
            (C.densityUpper-1/M) Cfr lam ℓ N μ i := by
    dsimp only
    let a := C.densityLower+1/M
    let b := C.densityUpper-1/M
    obtain ⟨ha,hab⟩ := high_source_interval_numeric C M hM
    have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr
      (by linarith) lam ℓ N μ hℓ hℓN
    rw [highUnionSource_bounded_action C (completeSourceRows C k D M q Cfr lam ℓ N μ) (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) hpos O hmO L hFbound]
    apply Finset.sum_congr rfl
    intro i _
    have h_sourceRow_activated_signed_action (O) (hmO : Measurable O) (hFbound : ∀ e, ‖O e‖ ≤ L) : (∫ e, (sourceRowData d k D M q a b Cfr lam ℓ N μ).rowActivation i e * O e
        ∂(sourceRowData d k D M q a b Cfr lam ℓ N μ).rowLaw i) =
        ∫ᵛ e, O e ∂<•sourceRowSignedMeasure d k D M q a b Cfr lam ℓ N μ i := by
      cases i with
      | inl p =>
        cases p
        · exact absoluteMarkLaw_signed_action ((Measure.dirac ()).prod Measure.count)
            (highPacketMarkWeight a b D 2 D q Cfr (fun _ => finePairUnitMatrix d D))
            (highPacketMarkWeight_integrable (Measure.dirac ()) a b D 2 D q Cfr _
              (fun _ _ => measurable_const) (integrable_const _))
            (highPacketMarkWeight_measurable a b D 2 D q Cfr _ (fun _ _ => measurable_const))
            (hpos (.inl .unit)) O hmO L hFbound
        · exact absoluteMarkLaw_signed_action ((finePairTimeFieldMeasure d 0 ℓ).prod Measure.count)
            (highPacketMarkWeight a b D 2 D q Cfr (finePairTimeMatrix d (finePairDistanceMatrix d D)))
            (highPacketMarkWeight_integrable _ a b D 2 D q Cfr _ (finePairTimeMatrix_measurable d _)
              (finePairTimeMatrix_cost_integrable d 0 ℓ _))
            (highPacketMarkWeight_measurable a b D 2 D q Cfr _ (finePairTimeMatrix_measurable d _))
            (hpos (.inl .coarse)) O hmO L hFbound
        · exact absoluteMarkLaw_signed_action ((finePairTimeFieldMeasure d ℓ N).prod Measure.count)
            (finePairPacketWeight a b M q Cfr (finePairTimeMatrix d (finePairDistanceMatrix d D)))
            (finePairPacketWeight_integrable _ a b M q Cfr _ (finePairTimeMatrix_measurable d _)
              (finePairTimeMatrix_cost_integrable d ℓ N _))
            (finePairPacketWeight_measurable a b M q Cfr _ (finePairTimeMatrix_measurable d _))
            (hpos (.inl .fine)) O hmO L hFbound
      | inr i =>
        cases i with
        | inl _ =>
          exact absoluteMarkLaw_signed_action ((Measure.dirac ()).prod Measure.count)
            (highPacketMarkWeight a b D 1 D q Cfr (fun _ => finePairUnitMatrix d D))
            (highPacketMarkWeight_integrable (Measure.dirac ()) a b D 1 D q Cfr _
              (fun _ _ => measurable_const) (integrable_const _))
            (highPacketMarkWeight_measurable a b D 1 D q Cfr _ (fun _ _ => measurable_const))
            (hpos (.inr (.inl ()))) O hmO L hFbound
        | inr i =>
          let r := higherBandFamilyTarget i.val
          let m := higherBandFamilyGuardDegree M i.val
          let T := higherBandFamilyUpper d ℓ N μ i.val
          letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
          exact absoluteMarkLaw_signed_action ((higherBandCarrierMeasure d r ℓ T i.val.2).prod Measure.count)
            (highPacketMarkWeight a b m r D q Cfr (higherBandCarrierAmplitude d r D lam i.val.2))
            (highPacketMarkWeight_integrable _ a b m r D q Cfr _
              (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
              (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2))
            (highPacketMarkWeight_measurable a b m r D q Cfr _
              (higherBandCarrierAmplitude_measurable d r D lam i.val.2))
            (hpos (.inr (.inr i))) O hmO L hFbound
    exact h_sourceRow_activated_signed_action (fun e => O (Sum.inl ⟨i,e⟩)) (hmO.comp (measurable_inl.comp (rowSigmaMk_measurable i))) (fun e => hFbound _)
  rw [(h_completeSourceUnion_signed_action (C.densityUpper^n*B) hOb)]
  change (∑ i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ,
      ∫ᵛ e, O (Sum.inl ⟨i,e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ i) =
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q Cfr U p c Φ
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  have hunit : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.unit,e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .unit)) =
      finePairUnitFirstAction ad bd D q Cfr p c Φ := by
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    apply Finset.prod_congr rfl
    intro u _
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, highUnionRowRestrict, finePairRowData, finePairRowSlope, finePairRowIntercept, highPacketSlope, highPacketIntercept, localDensityReset]
    ring
  have hcoarse : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.coarse,e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .coarse)) =
      finePairCoarseFirstAction ad bd ℓ D q Cfr U p c Φ := by
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    apply Finset.prod_congr rfl
    intro u _
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, highUnionRowRestrict, finePairRowData, finePairRowSlope, finePairRowIntercept, highPacketSlope, highPacketIntercept, localDensityReset, U]
    ring
  have hfine : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.fine,e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .fine)) =
      finePairFineFirstAction ad bd ℓ N M q Cfr U p c Φ := by
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    apply Finset.prod_congr rfl
    intro u _
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, highUnionRowRestrict, finePairRowData, finePairRowSlope, finePairRowIntercept, finePairPacketSlope, finePairPacketIntercept, finePairDensityReset, U]
    ring
  have hsingle : (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inl ()),e⟩)
      ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inr (.inl ()))) =
      singletonFirstAction ad bd D q Cfr p c Φ := by
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    apply Finset.prod_congr rfl
    intro u _
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, singletonRowData, highPacketSlope, highPacketIntercept, localDensityReset]
    ring
  have hhigher (i : HigherBandFamilyIndex d D M q ad bd Cfr lam ℓ N μ) :
      (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inr i),e⟩)
        ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inr (.inr i))) =
      higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q Cfr i.val.2 U p c Φ := by
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    apply Finset.prod_congr rfl
    intro u _
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, higherBandFamilyComponent, higherBandRowData, highPacketSlope, highPacketIntercept, localDensityReset, U]
    ring
  have htags : (Finset.univ : Finset FinePairRowTag) = {.unit,.coarse,.fine} := by decide
  simp only [htags]
  simp [hunit, hcoarse, hfine, hsingle, hhigher, completeSourceSignedFirstAction, finePairThreeRowFirstAction, add_assoc]
set_option backward.isDefEq.respectTransparency false
end
section
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
structure HighFrameOriginalLocalGuards (d k D : ℕ) [NeZero k] (Cfr eta rho : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) : Prop where
  amplitude_nonneg : 0 ≤ eta
  amplitude_half : eta ≤ rho/2
  coefficient_ball : ∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹
  weight_abs : ∀ j x, |highPeriodicTensor d k j x| ≤ 1
  without_abs : ∀ j x, |highLocalFieldWithout d k D eta c j x| ≤ rho/2
  regression_abs : ∀ j (v : HighFrameIndex d D → ℝ), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |highLocalFieldWithout d k D eta c j x + eta*highPeriodicTensor d k j x*
      (∑ γ, highLocalFrameFeature k j x γ*v γ)| ≤ rho
theorem completeSource_original_local_guards  [NeZero d]
    (C ) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ ↑M →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf*↑k^(-C.smoothness) ≤ eta0 →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/↑M)
          (C.densityUpper-1/↑M) Cfr lam ell N mu)),
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      HighFrameOriginalLocalGuards d k D Cfr (cf*↑k^(-C.smoothness)) Q.ρ
        (highUnionSourceState C R h).2 := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let eta0 := Q.ρ/(2*(↑2^d+1))
  refine ⟨Cfr0,eta0,hfr0,div_pos Q.ρ_pos (by positivity),?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have hc := highUnionSourceState_coefficient_ball C R (completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu (hfr0.trans hfr) hell hellN) h
  let c := (highUnionSourceState C R h).2
  let eta := cf*↑k^(-C.smoothness)
  have hfr1  := hfr0.trans hfr
  have hen : 0 ≤ eta := by dsimp [eta]; positivity
  have hamp : (↑2^d+1)*eta ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*((2 : ℝ)^d+1))).mp heta
    nlinarith
  have hehalf : eta ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (j) : frameCoefficientL1 (highFramePolynomial (c j)) ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (hc j).trans ((inv_le_inv₀ (by linarith : 0 < Cfr) (by linarith : 0 < Cfr0)).mpr hfr)
  have hF := (hfield k hk0 hk cf hcf (fun j => highFramePolynomial (c j)) hP).1
  have hw (j) (x) : |highPeriodicTensor d k j x| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j x)]
    exact highPeriodicTensor_le_one d k (by omega) j x
  have hterm (j) (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |eta*highPeriodicTensor d k j x*(∑ γ, highLocalFrameFeature k j x γ*v γ)| ≤ eta := by
    rw [abs_mul,abs_mul,abs_of_nonneg hen]
    have ht := mul_le_mul (hw j x) (highLocalFrameFeature_ball_abs_le_one k j x Cfr hfr1 v hv) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left ht hen]
  have hg (j) (x) : |highLocalFieldWithout d k D eta c j x| ≤ Q.ρ/2 := by
    have hd := highFrameField_local_decomposition d k D hk eta c j x
    have he : highLocalFieldWithout d k D eta c j x =
        highFrameField d k eta (fun l => highFramePolynomial (c l)) x -
          eta*highPeriodicTensor d k j x*(∑ γ, highLocalFrameFeature k j x γ*c j γ) := by
      linarith [hd]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hF x) (hterm j (c j) (hc j) x)).trans
      (by nlinarith only [hamp]))
  refine ⟨hen,hehalf,hc,hw,hg,?_⟩
  intro j v hv x
  exact (abs_add_le _ _).trans (by linarith only [hg j x,hterm j v hv x,hehalf])
theorem HighFrameOriginalLocalGuards.ternary_floor 
    [NeZero k]  (Q : LowSmoothnessTernaryConstants C)
    {Cfr eta V : ℝ} {c : HighWindowLabels d k → HighFrameIndex d D → ℝ}
    (H : HighFrameOriginalLocalGuards d k D Cfr eta Q.ρ c)
    (hV : |V-Q.v| ≤ Q.ρ) (j : HighWindowLabels d k)
    (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹)
    (x : Covariate d) (y : Fin 3) :
    Q.c ≤ highMarkedResponseMass Q.a V eta (highLocalFieldWithout d k D eta c j)
      (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) v x y := (Q.legal _ V (H.regression_abs j v hv x) hV).2.2.1 y
end
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
theorem completeSource_original_response_exact_and_low_counts  [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ ↑M →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf*↑k^(-C.smoothness) ≤ eta0 →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/↑M)
          (C.densityUpper-1/↑M) Cfr lam ell N mu)),
      ∀ n : ℕ, ∀ x : Fin n → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      ∀ y : Fin n → Fin 3,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let eta := cf*↑k^(-C.smoothness)
      let c := (highUnionSourceState C R h).2
      highUnionSourceMarkedNumerator C R n Q.a V eta j h x y =
        completeSourceRawNumerator (C.densityLower+1/↑M) (C.densityUpper-1/↑M)
          lam ell N mu D M q Cfr Q.a V eta (fun i => highLocalCoordinates d k j (x i))
          (fun i => highUnionSourceDensity C R h (x i))
          (fun i => highLocalFieldWithout d k D eta c j (x i))
          (fun i => highPeriodicTensor d k j (x i)) (c j) y ∧
        (n ≤ 1 → highUnionSourceMarkedNumerator C R n Q.a V eta j h x y = 0) := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hguards⟩ := completeSource_original_local_guards C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta V hV j h n x hx y
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf*↑k^(-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let U := fun i : Fin n => highLocalCoordinates d k j (x i)
  let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
  let g := fun i : Fin n => highLocalFieldWithout d k D eta c j (x i)
  let w := fun i : Fin n => highPeriodicTensor d k j (x i)
  have hfr1 := hfr0.trans hfr
  have hmass (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (i : Fin n) (b : Fin 3) :
      0 ≤ ternaryMass Q.a
        (coefficientRegression eta g w (fun u : Fin n => highLocalFrameFeature k j (x u)) v i) V b := by
    have hf := (hguards k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h).ternary_floor Q hV j v hv (x i) b
    exact Q.c_pos.le.trans hf
  have h_completeSourceRawNumerator_eq_canonical : highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) Q.a V eta
      (fun u => highUnionSourceDensity C R h (x u))
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) ((highUnionSourceState C R h).2 j) y =
      completeSourceRawNumerator (C.densityLower+1/↑M)
        (C.densityUpper-1/↑M) lam ell N mu D M q Cfr Q.a V eta U
        (fun u => highUnionSourceDensity C R h (x u)) g w ((highUnionSourceState C R h).2 j) y := by
    unfold highMarkedLocalScoreNumerator completeSourceRawNumerator
    have h_completeSourceResponseAction_eq_signed_first_action : highMarkedResponseAction (highUnionLaw R (highCenterMix C))
        (highUnionActivation R (highCenterMix C)) Q.a V eta
        (fun e u => highUnionSourceResetDensity C R j h e (x u))
        (highUnionSourceResetCoefficient C R j h) g w (fun u => highLocalFrameFeature (D := D) k j (x u)) y =
        completeSourceSignedFirstAction (C.densityLower+1/M)
          (C.densityUpper-1/M) lam ell N mu D M q Cfr U
          (fun u => highUnionSourceDensity C R h (x u)) ((highUnionSourceState C R h).2 j)
          (fun v => highResponseProduct Q.a V eta g w (fun u => highLocalFrameFeature (D := D) k j (x u)) v y) := by
      let Φ := fun v => highResponseProduct Q.a V eta g w (fun u => highLocalFrameFeature (D := D) k j (x u)) v y
      have hmΦ  := highMarkedResponseProduct_measurable Q.a V eta (fun v => v)
        (fun γ => measurable_pi_apply γ) g w (fun u => highLocalFrameFeature (D := D) k j (x u)) y
      have hbΦ (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) : |Φ v| ≤ 1 :=
        highMarkedResponseProduct_abs_le_one Q.a V eta Q.a_pos.ne' g w (fun u => highLocalFrameFeature (D := D) k j (x u)) v (hmass v hv) y
      have he := completeSourceCanonicalAction_eq_signed_first_action C hD hq hM Cfr lam ell N mu
        hfr1 hell hellN j h x hx Φ hmΦ 1 (by norm_num) hbΦ
      apply Eq.trans _ he
      apply integral_congr_ae
      filter_upwards [] with e
      ring
    rw [h_completeSourceResponseAction_eq_signed_first_action]
    rfl
  have he := h_completeSourceRawNumerator_eq_canonical
  change highUnionSourceMarkedNumerator C R n Q.a V eta j h x y =
    completeSourceRawNumerator _ _ lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y at he
  refine ⟨he,?_⟩
  intro hn
  rw [he]
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C ↑M hM
  have hp (i : Fin n) : p i ∈ Icc (C.densityLower+1/↑M) (C.densityUpper-1/↑M) :=
    highUnionSourceDensity_interval C R (completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hfr1 hell hellN) h (x i)
  have hU (i : Fin n) (r : Fin d) : |U i r| ≤ 2 :=
    (highLocalCoordinates_abs_le_one d k j (x i) r).trans (by norm_num)
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl
  have h_completeSourceRawNumerator_count_zero (ad) (bd) (ha : 0 < ad) (hab : ad < bd) (hD : 1 ≤ D) (a) (c : HighFrameIndex d D → ℝ) : completeSourceRawNumerator ad bd lam ell N mu D M q Cfr a V eta U p g w c y = 0 := by
    unfold completeSourceRawNumerator
    rw [completeSourceSignedFirstAction_eq_family,
      finePairThreeRowFirstAction_small_count (by omega) ad bd ell N ha hab D M q hD Cfr U p
        (fun i => Fin.elim0 i) c,
      singletonFirstAction_zero_other_count ad bd ha hab D q hD (by omega) (by omega)
        Cfr p (fun i => Fin.elim0 i) c,
      higherBandFamilyFirstAction_zero_small_count ad bd lam ell N mu ha hab D M q hD
        (by omega) (by omega) Cfr U (fun i => Fin.elim0 i) p (fun i => Fin.elim0 i) c]
    simp
  · exact (h_completeSourceRawNumerator_count_zero _ _ ha hab (by omega) Q.a (c j))
  have h_completeSourceRawNumerator_count_one (ad) (bd) (ha : 0 < ad) (hab : ad < bd) (hD : 1 ≤ D) (a) (hC : Cfr ≠ 0) (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ) : completeSourceRawNumerator ad bd lam ell N mu D M q Cfr a V eta U p g w c y = 0 := by
    unfold completeSourceRawNumerator
    have h_singletonFirstAction_response_heat : singletonFirstAction ad bd D q Cfr p c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) =
        eta^2 * (∏ i, p i) * ∑ i, (w i)^2 *
          highResponseVarianceTerm a V eta g w (fun i => highFrameFeature (U i)) c y i := by
      have h_singletonFirstAction_count_one (Φ : (HighFrameIndex d D → ℝ) → ℝ) : singletonFirstAction ad bd D q Cfr p c Φ =
        (∏ i, p i) * responseMatrixAction q Cfr (finePairUnitMatrix d D) c Φ := by
        rw [singletonFirstAction_eq_packet ad bd ha hab D q Cfr p hp c Φ]
        unfold highSeparatedPacketAction
        simp_rw [densityPacketAction_mul_right]
        have hh := density_packet_product_count_selector (Finset.univ : Finset (Fin 1))
          ad bd ha hab D 1 D (by norm_num) hD (by simpa using hD)
          (by simpa using hD) p (fun _ _ => 1)
        have hpow : (Finset.univ : Finset (Fin 1)).powersetCard 1 = {Finset.univ} := by
          simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 1))
        simp only [Finset.card_univ, Fintype.card_fin, ite_true, hpow, Finset.sum_singleton,
          densitySeparatedSym_one 1 (Finset.univ : Finset (Fin 1)) (by simp), mul_one] at hh
        simp_rw [hh]
        simp
      rw [h_singletonFirstAction_count_one]
      have he := high_response_matrix_heat q hq Cfr a V eta (finePairUnitMatrix d D) hC
        (finePairUnitMatrix_symmetric d D) g w (fun i => highFrameFeature (U i)) c y
        (fun _ => 1) (by
          intro i l
          have hil : i = l := Subsingleton.elim _ _
          simp only [finePairUnitMatrix_kernel, hil, ite_true])
      rw [he]
      simp only [mul_one]
      ring
    rw [completeSourceSignedFirstAction_eq_family,
      finePairThreeRowFirstAction_small_count (by omega) ad bd ell N ha hab D M q hD Cfr U p hp c,
      higherBandFamilyFirstAction_zero_small_count ad bd lam ell N mu ha hab D M q hD
        hD (by omega) Cfr U hU p hp c,
      h_singletonFirstAction_response_heat]
    ring
  · exact (h_completeSourceRawNumerator_count_one _ _ ha hab (by omega) Q.a (by linarith) hp (c j))
end
def rawCostConstants (CB C5 C6 C7 cf ch : ℝ) : Fin 7 → ℝ :=
  ![1, C6, ch, 1 + CB ^ 2, 3 * (C5 + C7) * cf ^ 4,
    3 * C6 ^ 2 * cf ^ 4, Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2]
def rawCostConstant (CB C5 C6 C7 cf ch : ℝ) : ℝ :=
  Finset.univ.sup' (by simp) (rawCostConstants CB C5 C6 C7 cf ch)
theorem rawCostConstant_ge (CB C5 C6 C7 cf ch i) :
    rawCostConstants CB C5 C6 C7 cf ch i ≤ rawCostConstant CB C5 C6 C7 cf ch :=
  Finset.le_sup' _ (Finset.mem_univ i)
theorem rawCostConstant_ge_one (CB C5 C6 C7 cf ch ) :
    1 ≤ rawCostConstant CB C5 C6 C7 cf ch := rawCostConstant_ge _ _ _ _ _ _ 0
theorem raw_energy_cost_bound {n v mu eta4 h4s B Bl E Fdef Fal CB C5 C6 C7 cf ch : ℝ}
    (hv : 0 < v) (hmu : mu = n * v) (hn : 0 ≤ n) (hp4s : 0 ≤ h4s)
    (heta : eta4 = cf ^ 4 * h4s) (hB : 1 ≤ B) (hBl : 0 ≤ Bl)
    (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7)
    (hcf : 0 ≤ cf) (hch : 0 ≤ ch) (hFdef : 0 ≤ Fdef) (hFal : 0 ≤ Fal)
    (hcost : Bl ≤ CB * B) (M D )
    (hE : E ≤ 3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef +
      3 * C6 * eta4 * Fal * (C6 * mu) ^ (M + 1) / (M + 1).factorial +
      Real.exp ch * eta4 * (Bl + 1) ^ 2 * (ch * mu) ^ (D + 1) / (D + 1).factorial) :
    let CG := rawCostConstant CB C5 C6 C7 cf ch
    1 + Bl ^ 2 + v⁻¹ * E ≤ CG * (B ^ 2 + n ^ 2 * v * h4s * Fdef +
      n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial +
      n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) := by
  have h_factorial_succ_energy_reduction {c : ℝ} {C : ℝ} {F : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C) (hF : 0 ≤ F) (m) : v⁻¹ * (eta4 * F * (c * mu) ^ (m + 1) / (m + 1).factorial) ≤
      c * cf ^ 4 * n * h4s * F * (C * mu) ^ m / (m + 1).factorial := by
    have hmu0 : 0 ≤ mu := by rw [hmu]; positivity
    have hp : (c * mu) ^ (m + 1) ≤ c * mu * (C * mu) ^ m := by
      rw [pow_succ]
      have hh : (c * mu) ^ m ≤ (C * mu) ^ m :=
        pow_le_pow_left₀ (mul_nonneg hc hmu0) (mul_le_mul_of_nonneg_right hcC hmu0) _
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (mul_nonneg hc hmu0)
    calc
      _ ≤ v⁻¹ * (eta4 * F * (c * mu * (C * mu) ^ m) / (m + 1).factorial) := by
        apply mul_le_mul_of_nonneg_left
        · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_left hp
          rw [heta]
          positivity
        · positivity
      _ = _ := by rw [heta, hmu]; field_simp
  let CG := rawCostConstant CB C5 C6 C7 cf ch
  change _ ≤ CG * _
  have hCG : 1 ≤ CG := rawCostConstant_ge_one _ _ _ _ _ _
  have hC6G : C6 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 1
  have hchG : ch ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 2
  have hBG : 1 + CB ^ 2 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 3
  have hpG : 3 * (C5 + C7) * cf ^ 4 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 4
  have haG : 3 * C6 ^ 2 * cf ^ 4 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 5
  have htG : Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2 ≤ CG :=
    rawCostConstant_ge _ _ _ _ _ _ 6
  have hB0 : 0 ≤ B := by linarith only [hB]
  have : 0 ≤ mu := by rw [hmu]; positivity
  have : 0 ≤ CG := by linarith only [hCG]
  have hb2 : Bl ^ 2 ≤ CB ^ 2 * B ^ 2 := by
    calc
      _ ≤ (CB * B) ^ 2 := (sq_le_sq₀ hBl (mul_nonneg hCB hB0)).mpr hcost
      _ = _ := mul_pow _ _ _
  have hb1 : 1 ≤ B ^ 2 := by nlinarith only [hB]
  have hbase : 1 + Bl ^ 2 ≤ CG * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hBG (sq_nonneg B)
    nlinarith only [hh, hb1, hb2]
  have hp : v⁻¹ * (3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef) ≤
      CG * (n ^ 2 * v * h4s * Fdef) := by
    calc
      _ = 3 * (C5 + C7) * (cf ^ 4 * (n ^ 2 * v * h4s * Fdef)) := by
        have h_inverse_volume_pair_energy {F : ℝ} : v⁻¹ * (eta4 * mu ^ 2 * F) = cf ^ 4 * (n ^ 2 * v * h4s * F) := by
          rw [heta, hmu]
          field_simp
        rw [show 3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef =
          3 * (C5 + C7) * (eta4 * mu ^ 2 * Fdef) by ring, mul_left_comm,
          h_inverse_volume_pair_energy]
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right hpG
          (by positivity : 0 ≤ n ^ 2 * v * h4s * Fdef) using 1 <;> ring
  have ha : v⁻¹ * (3 * C6 * eta4 * Fal * (C6 * mu) ^ (M + 1) / (M + 1).factorial) ≤
      CG * (n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial) := by
    have hr := h_factorial_succ_energy_reduction hC6 hC6G hFal M
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 3 * C6)
    apply le_trans (by convert hh using 1 <;> ring)
    convert mul_le_mul_of_nonneg_right haG
      (by positivity : 0 ≤ n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial) using 1 <;> ring
  have ht : v⁻¹ * (Real.exp ch * eta4 * (Bl + 1) ^ 2 * (ch * mu) ^ (D + 1) /
      (D + 1).factorial) ≤
      CG * (n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) := by
    have hr := h_factorial_succ_energy_reduction hch hchG
      (show 0 ≤ 1 by norm_num) D
    have hh := mul_le_mul_of_nonneg_left hr
      (by positivity : 0 ≤ Real.exp ch * (Bl + 1) ^ 2)
    have h_activity_plus_one_bound : (Bl + 1) ^ 2 ≤ (CB + 1) ^ 2 * B ^ 2 := by
      have h : Bl + 1 ≤ (CB + 1) * B := by nlinarith only [hcost, hB]
      calc
        _ ≤ ((CB + 1) * B) ^ 2 := (sq_le_sq₀ (by linarith only [hBl]) (by positivity)).mpr h
        _ = _ := mul_pow _ _ _
    have hab := h_activity_plus_one_bound
    have hk := mul_le_mul_of_nonneg_right hab
      (by positivity : 0 ≤ Real.exp ch * ch * cf ^ 4 * n * h4s *
        (CG * mu) ^ D / (D + 1).factorial)
    apply le_trans (by convert hh using 1 <;> ring)
    apply le_trans (by convert hk using 1 <;> ring)
    convert mul_le_mul_of_nonneg_right htG
      (by positivity : 0 ≤ n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) using 1 <;> ring
  nlinarith only [mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hv.le), hbase, hp, ha, ht]
def lowerSaddleRawEnergyBound (s d m θ C cf C5 C6 C7 ch Bl : ℝ)
    (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  let η := lowerSaddleEta s d m θ C cf x
  let μ := lowerSaddleMu d m θ C x
  let N := lowerSaddleN s d m θ C τM x
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  3*(C5+C7)*η^4*μ^2*N^(-d) +
    3*C6*η^4*(Real.exp (2*τM M*M)*N^(4-d))*(C6*μ)^(M+1)/(M+1).factorial +
    Real.exp ch*η^4*(Bl+1)^2*(ch*μ)^(D+1)/(D+1).factorial
theorem lowerSaddle_raw_energy_cost {s d m θ C cf CB C5 C6 C7 ch x Bl E : ℝ}
    (τM ) (hx : 0 ≤ x) (hcf : 0 ≤ cf) (hCB : 0 ≤ CB)
    (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7) (hch : 0 ≤ ch)
    (hB : 1 ≤ lowerSaddleActivity s d m θ C τM x) (hBl : 0 ≤ Bl)
    (hcost : Bl ≤ CB*lowerSaddleActivity s d m θ C τM x)
    (hE : E ≤ lowerSaddleRawEnergyBound s d m θ C cf C5 C6 C7 ch Bl τM x) :
    let CG := rawCostConstant CB C5 C6 C7 cf ch
    1+Bl^2+(lowerSaddleH d m θ C x)^(-d)*E ≤
      CG*((lowerSaddleActivity s d m θ C τM x)^2+
        lowerSaddleEnergyOne s d m θ C τM x+
        lowerSaddleEnergyTwo s d m θ C CG τM x+
        lowerSaddleEnergyThree s d m θ C CG τM x) := by
  let h := lowerSaddleH d m θ C x
  have hh : 0 < h := lowerSaddleH_positive _ _ _ _ _
  have hr := raw_energy_cost_bound (n := x) (v := h^d)
    (mu := lowerSaddleMu d m θ C x) (eta4 := (lowerSaddleEta s d m θ C cf x)^4)
    (h4s := h^(4*s)) (B := lowerSaddleActivity s d m θ C τM x) (Bl := Bl) (E := E)
    (Fdef := (lowerSaddleN s d m θ C τM x)^(-d))
    (Fal := Real.exp (2*τM (lowerSaddleM m x)*lowerSaddleM m x)*
      (lowerSaddleN s d m θ C τM x)^(4-d))
    (CB := CB) (C5 := C5) (C6 := C6) (C7 := C7) (cf := cf) (ch := ch)
    (Real.rpow_pos_of_pos hh _)
    (by rfl) hx (Real.rpow_nonneg hh.le _) (by unfold lowerSaddleEta; rw [mul_pow, ← Real.rpow_mul_natCast hh.le]; congr 1; congr 1; ring) hB hBl hCB hC5 hC6 hC7 hcf hch
    (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _))
    hcost (lowerSaddleM m x) (lowerSaddleD d m x) hE
  dsimp only at hr ⊢
  rw [Real.rpow_neg hh.le] at ⊢
  have he1 : x^2*h^d*h^(4*s)*(lowerSaddleN s d m θ C τM x)^(-d) =
      lowerSaddleEnergyOne s d m θ C τM x := by
    unfold lowerSaddleEnergyOne
    change x^2*h^d*h^(4*s)*(lowerSaddleN s d m θ C τM x)^(-d) =
      x^2*h^(d+4*s)*(lowerSaddleN s d m θ C τM x)^(-d)
    rw [Real.rpow_add hh]
    ring
  rw [he1] at hr
  simpa only [lowerSaddleEnergyTwo, lowerSaddleEnergyThree, ← mul_assoc] using hr
theorem eventually_actual_lowerSaddle_raw_cost {s d a b cf CB C5 C6 C7 ch C : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hcf : 0 ≤ cf) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch)
    (hC : 1+Real.log (rawCostConstant CB C5 C6 C7 cf ch)+
      (d^2-16*s)/(d*(d+4))*lowerSaddleTheta s d (densityIntervalExponent a b)+
      2*d*densityIntervalExponent a b/(d+4) < C) :
    ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let τM := shrunkDensityExponent a b
      let B := lowerSaddleActivity s d m θ C τM x
      ∀ Bl E, 1 ≤ B → 0 ≤ Bl → Bl ≤ CB*B →
        E ≤ lowerSaddleRawEnergyBound s d m θ C cf C5 C6 C7 ch Bl τM x →
      1+Bl^2+(lowerSaddleH d m θ C x)^(-d)*E ≤
        3*rawCostConstant CB C5 C6 C7 cf ch*B^2 := by
  filter_upwards [eventually_actual_lowerSaddle_numeric_cost hs hd ha hab (lt_of_lt_of_le zero_lt_one (rawCostConstant_ge_one _ _ _ _ _ _)) hC,
    eventually_ge_atTop 0] with x hx hx0
  dsimp only at hx ⊢
  intro Bl E hB hBl hcost hE
  exact (lowerSaddle_raw_energy_cost _ hx0 hcf hCB hC5 hC6 hC7 hch hB hBl hcost hE).trans hx
theorem lowerSaddle_cost_risk_reduction {s d m θ C cf x den CG ctr : ℝ}
    (τM ) (hden : 0 < den) (hCG : 0 < CG) (hctr : 0 ≤ ctr)
    (hcost : den ≤ 3*CG*(lowerSaddleActivity s d m θ C τM x)^2) :
    ctr/(3*CG)*(lowerSaddleRisk s d m θ C cf τM x)^2 ≤
      ctr*(lowerSaddleEta s d m θ C cf x)^4/den := by
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ ctr*(lowerSaddleEta s d m θ C cf x)^4) hden hcost
  apply le_trans _ hh
  apply le_of_eq
  unfold lowerSaddleRisk
  field_simp
section
section
section
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
end
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
end
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
end
 theorem rowMass_le_balanced_source_activity   [Fintype I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) (hR : 0 ≤ highRowTotalMass R.rowMass) :
    highRowTotalMass R.rowMass ≤ highRowTotalMass R.rowMass/highCenterMix C := by
  apply (le_div_iff₀ (highCenterMix_mem C).1).mpr
  exact mul_le_of_le_one_right hR (highCenterMix_mem C).2.le
def completeSaddleGeometryEnvelope  (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ) :
    (r : ℕ) → (Fin r → Covariate d) → ℝ :=
  let q := lowerSaddleResponseOrder C.smoothness d
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  completeSourceGeometryEnvelope (lowerSaddleD d m n) (lowerSaddleM m n) (ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper) q C.densityLower C.densityUpper c0 (lowerAliasCutoff C.smoothness d m theta Cω c0 (shrunkDensityExponent C.densityLower C.densityUpper) n) (lowerSaddleN C.smoothness d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) n) (lowerSaddleMu d m theta Cω n) Cfr Q.a Q.ρ (lowerSaddleEta C.smoothness d m theta Cω cf n) (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) (completeSourceSaddleActivity C q Cfr (spatialInterpolationLambda d) Cω n)
def completeSaddleScoreFactor  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  highFixedScoreDenominator C.densityLower Q.c*2^d
 def completeSaddleDegreeFactor (d : ℕ) : ℝ := (d+8)/4+1
 def completeSaddleOrdinaryConstant  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  ordinaryFineAliasFactorialConstant C.smoothness d (lowerSaddleResponseOrder C.smoothness d)
    C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleScoreFactor C Q)
 def completeSaddleDefectConstant  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryDefectConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleScoreFactor C Q)
 def completeSaddleFieldConstant  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryFieldConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleScoreFactor C Q)
 def completeSaddleAliasConstant  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryAliasConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleDegreeFactor d) (completeSaddleScoreFactor C Q) (completeSaddleOrdinaryConstant C Q Cfr)
 def completeSaddleExteriorConstant  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  completeGeometryExteriorConstant d (completeSaddleScoreFactor C Q)
    (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)
 def completeSaddleEnergyBudget  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (Cfr cf Cω : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleRawEnergyBound C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf (completeSaddleDefectConstant C Q Cfr)
    (completeSaddleAliasConstant C Q Cfr) (completeSaddleFieldConstant C Q Cfr) (completeSaddleExteriorConstant C Q)
    (completeSourceSaddleActivity C (lowerSaddleResponseOrder C.smoothness d) Cfr (spatialInterpolationLambda d) Cω n)
    (shrunkDensityExponent C.densityLower C.densityUpper) n
 theorem completeSaddleDefectConstant_pos {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) :
    0 < completeSaddleDefectConstant C Q Cfr := completeGeometryDefectConstant_pos _ _ _ _ _ _ _
 theorem completeSaddleAliasConstant_pos {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) :
    0 < completeSaddleAliasConstant C Q Cfr := completeGeometryAliasConstant_pos _ _ _ _ _ _ _ _ _ _ _
 theorem completeSaddleFieldConstant_pos {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) :
    0 < completeSaddleFieldConstant C Q Cfr := completeGeometryFieldConstant_pos _ _ _ _ _ _ _ _ _
 theorem completeSaddleExteriorConstant_pos {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    0 < completeSaddleExteriorConstant C Q := completeGeometryExteriorConstant_pos _ _ _
end NearlyMinimax
end
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace NearlyMinimax
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel
 theorem highCompleteSource_cost_risk_uniform_above {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (CfrMin : ℝ) :
    ∃ Cfr eta0 ctr : ℝ, 1 ≤ Cfr ∧ CfrMin ≤ Cfr ∧ 0 < eta0 ∧ 0 < ctr ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ eta0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ n : ℕ, ∀ E : ℝ, 0 ≤ E →
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ cm/(M:ℝ) →
      let Bl := highRowTotalMass R.rowMass/highCenterMix C
      let c := highPathConstant (3^d) Q.ρ eta0
      let I := Real.sqrt ((3^d:ℕ)*(k:ℝ)^d*E)
      let delta := localScorePathLength c Bl I
      ∀ H : ℝ → (HighCompleteSourceHistory C k D M q Cfr lam ell N mu) → HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ,
      (∀ t ∈ Icc 0 delta, ∀ h j r, Integrable (H t h j r)
        (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)))) →
      (∀ t ∈ Icc 0 delta, ∀ h j r u, 0 ≤ H t h j r u) →
      (∀ t ∈ Icc 0 delta, ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v-eta^2*t) eta h j) x ≤
          H t h j r (highPatchProductChart d k j x)) →
      (∀ t ∈ Icc 0 delta, ∀ h,
        highSourceSpatialSeries d k n C.densityLower Q.c (H t h) ≤ (3^d:ℕ)*(k:ℝ)^d*E) →
      ENNReal.ofReal (ctr*eta^4/(1+Bl^2+(k:ℝ)^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  have h_highCompleteSource_minimax_path_bound_uniform_above : ∃ Cfr eta0 : ℝ, 1 ≤ Cfr ∧ CfrMin ≤ Cfr ∧ 0 < eta0 ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ eta0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ n : ℕ, ∀ T B : ℝ, ∀ hT : 0 ≤ T, 0 ≤ B →
      T*(highRowTotalMass R.rowMass/highCenterMix C)/historyReferenceRho (3^d) ≤
        1/(2+8*((3^d:ℕ):ℝ)^2) →
      eta^2*T ≤ Q.ρ →
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ cm/(M:ℝ) →
      ∀ H : ℝ → Ω → HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ,
      (∀ t ∈ Icc 0 T, ∀ h j r, Integrable (H t h j r)
        (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)))) →
      (∀ t ∈ Icc 0 T, ∀ h j r u, 0 ≤ H t h j r u) →
      (∀ t ∈ Icc 0 T, ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v-eta^2*t) eta h j) x ≤
          H t h j r (highPatchProductChart d k j x)) →
      (∀ t ∈ Icc 0 T, ∀ h, highSourceSpatialSeries d k n C.densityLower Q.c (H t h) ≤ B) →
      ENNReal.ofReal (eta^4*T^2/(2+T*Real.sqrt B)^2-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
    obtain ⟨Cfm,etam,hCfm,hetam,hmodel⟩ := highUnionSource_original_model_uniform C Q
    obtain ⟨Cfq,etaq,hCfq,hetaq,hfloor⟩ := highUnionSource_ternary_floor_uniform C Q
    let Cfr := max (max Cfm Cfq) CfrMin
    let eta0 := min etam etaq
    have hCfr : 1 ≤ Cfr := (hCfm.trans (le_max_left _ _)).trans (le_max_left _ _)
    have hCfmfr : Cfm ≤ Cfr := (le_max_left _ _).trans (le_max_left _ _)
    have hCfqfr : Cfq ≤ Cfr := (le_max_right _ _).trans (le_max_left _ _)
    have heta0 : 0 < eta0 := lt_min hetam hetaq
    refine ⟨Cfr,eta0,hCfr,le_max_right _ _,heta0,?_⟩
    intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
    letI := hk0
    letI := horder
    let R := completeSourceRows C k D M q Cfr lam ell N mu
    let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
    let E := SourceRowMark d D M q (C.densityLower+1/(M:ℝ)) (C.densityUpper-1/(M:ℝ)) Cfr lam ell N mu
    have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
    have hpos := completeSourceRows_mass_positive (k := k) C hD hq hM Cfr lam ell N mu hCfr hell hellN
    letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
    letI := highUnionSourceLaw_probability C R G
    dsimp only
    intro cf hcf hcfH
    let eta := cf*(k : ℝ)^(-C.smoothness)
    intro heta cm hcm hcmU n T B hT hB hsmall hVbudget heps H hH hH0 hdom hbudget
    let p := highUnionSourceDensity C R
    let F := highUnionSourceRegression C R eta
    have hp : Measurable (Function.uncurry p) := highUnionSourceDensity_joint_measurable C R G
    have hF : Measurable (Function.uncurry F) := highUnionSourceRegression_joint_measurable C R G eta
    let π := highUnionLaw R (highCenterMix C)
    let act := highUnionActivation R (highCenterMix C)
    let Ba := highRowTotalMass R.rowMass/highCenterMix C
    let ν (t : ℝ) := historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t π act
    have hBa : 0 ≤ Ba := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
    have hν (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (ν t) :=
      completeSourcePrior_probability C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht
    have hV (t : ℝ) (ht : t ∈ Icc 0 T) : |(Q.v-eta^2*t)-Q.v| ≤ Q.ρ := by
      simp only [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg eta),abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hVbudget
    have hqFloor (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3) :
        Q.c ≤ ternaryMass Q.a (F h x) (Q.v-eta^2*t) y :=
      hfloor k D hk0 horder hk _ inferInstance E inferInstance R (M:ℝ)
        (G.mono_frame hCfq hCfqfr) cf hcf
        (heta.trans (min_le_right _ _)) h _ (hV t ht) x y
    have hqPos (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3) :
        0 < ternaryMass Q.a (F h x) (Q.v-eta^2*t) y := Q.c_pos.trans_le (hqFloor t ht h x y)
    have hqNonneg := fun t ht h x y => (hqPos t ht h x y).le
    let θ := highNormalizedParameterPath T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg
    let bad : ℝ → Set Ω := fun _ => {h | cm/(M:ℝ) < |highUnionSourceMass C R h-1|}
    let eps := 2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper))
    have hm : Measurable (highUnionSourceMass C R) := highUnionSourceMass_measurable C R G
    have hbad (t : ℝ) (_ : t ∈ Icc 0 T) : MeasurableSet (bad t) :=
      measurableSet_lt measurable_const ((hm.sub_const 1).abs)
    have hlegal (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (hh : h ∉ bad t) :
        Admissible (C.withDomain U) (θ t h) := by
      have hgood : |highUnionSourceMass C R h-1| ≤ cm/(M:ℝ) := le_of_not_gt hh
      obtain ⟨_,hlegal⟩ := hmodel U k D hk0 horder hk _ inferInstance E inferInstance inferInstance
        R (M:ℝ) (G.mono_frame hCfm hCfmfr) cf hcf hcfH
        (heta.trans (min_le_left _ _)) cm hcm hcmU h hgood _ (hV t ht)
      change Admissible (C.withDomain U)
        (highNormalizedParameterPath T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t h)
      rw [highNormalizedParameterPath_apply T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h]
      exact hlegal
    have hmassEq : (fun h => highRawDensityMass (p h)) = highUnionSourceMass C R := by
      funext h
      simp only [p,highRawDensityMass,highUnionSourceMass]
    have hmass (t : ℝ) (ht : t ∈ Icc 0 T) :
        Measure.map (fun h => highRawDensityMass (p h)) (ν t) =
        Measure.map (fun h => highRawDensityMass (p h)) (ν 0) := by
      have h1 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht
      have h0 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall 0 ⟨le_rfl,hT⟩
      rw [hmassEq]
      exact h1.trans h0.symm
    have hbadmass (t : ℝ) (ht : t ∈ Icc 0 T) :
        (massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n).real (bad t) ≤ eps := by
      rw [hmassEq]
      exact completeSourceMass_prior_tilted_tail C hD hq hM Cfr lam ell N mu hCfr hell hellN
        (by omega) T hT hsmall n (cm/(M:ℝ)) heps t ht
    have hfisher (t : ℝ) (ht : t ∈ Icc 0 T) := by
      letI := hν t ht
      exact highUnionSource_raw_fisher_bound C R G hpos (ν t) n hk Q.a (Q.v-eta^2*t) eta Q.c
        Q.a_pos.ne' Q.c_pos (hqFloor t ht)
        (fun j h x => completeSourceDensity_product_zero C hD hq hM Cfr lam ell N mu hCfr hell hellN j h n x)
        (H t) (hH t ht) (hH0 t ht) (hdom t ht) B hB (hbudget t ht)
    have hactm := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
    have hact := highUnionSourceActivation_centered C R G hpos
    have hab := highUnionSourceActivation_bound C R G hpos
    have hh := historyMarkedPrior_original_minimax_path_bound
      (fun i j => j ∈ highNeighborLabels d k i) (highNeighborLabels_self_mem d k)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
      (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
      π act hactm hact Ba T hBa hT hab hsmall (C.withDomain U) n Q.a Q.v eta
      C.densityLower C.densityUpper B eps Q.a_pos C.densityLower_pos p F hp hF
      (highUnionSourceDensity_coarse_interval C R G) hqPos hmass θ
      (fun t ht h => highNormalizedParameterPath_apply T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h)
      (fun t ht => Q.effective_interval (hV t ht)) bad hbad hlegal hbadmass
      (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
    let P (t : ℝ) := (highRealSampleKernel n Q.a (Q.v-eta^2*t) p F hp hF) ∘ₘ
      massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n
    let Score (t : ℝ) := highMarginalRealScore (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (ν t) π act n Q.a (Q.v-eta^2*t) eta p F
    letI := historyMarkedReference_probability (fun i j => j ∈ highNeighborLabels d k i)
      (highNeighborLabels_self_mem d k)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
      (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)) (highNeighbor_dependency_card d k) π
    have hInt := highHistoryScore_sqrt_energy_intervalIntegrable
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d) π act hactm
      Ba hBa hab n Q.a Q.v eta C.densityLower C.densityUpper T B Q.a_pos C.densityLower_pos
      hT p F hp hF hν (highUnionSourceDensity_coarse_interval C R G) hqPos
      (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
    have henergy (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ z, (Score t z)^2 ∂P t) ≤ B := by
      letI := hν t ht
      exact ((highMarginalRealScore_memLp_energy _ _ (ν t) π act hactm Ba hBa hab n Q.a
        (Q.v-eta^2*t) eta C.densityLower C.densityUpper Q.a_pos C.densityLower_pos
        p F hp hF (highUnionSourceDensity_coarse_interval C R G) (hqPos t ht)
        (hfisher t ht).1).2).trans (hfisher t ht).2
    have hscore := intervalIntegral_sqrt_energy_le
      (fun t => ∫ z, (Score t z)^2 ∂P t) T B hT hInt henergy
    have hsc0 : 0 ≤ ∫ t in (0:ℝ)..T, Real.sqrt (∫ z, (Score t z)^2 ∂P t) :=
      intervalIntegral.integral_nonneg hT (fun _ _ => Real.sqrt_nonneg _)
    have hfrac : eta^4*T^2/(2+T*Real.sqrt B)^2 ≤
        eta^4*T^2/(2+∫ t in (0:ℝ)..T, Real.sqrt (∫ z, (Score t z)^2 ∂P t))^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact (sq_le_sq₀ (by linarith) (by positivity)).mpr (by linarith)
    have hout := (ENNReal.ofReal_le_ofReal (sub_le_sub_right hfrac _)).trans hh
    simpa only [ModelConstants.withDomain,effectiveVarianceUpper] using hout
  obtain ⟨Cfr,eta0,hCfr,hmin,heta0,hpath⟩ := h_highCompleteSource_minimax_path_bound_uniform_above
  let c := highPathConstant (3^d) Q.ρ eta0
  have hc : 0 < c := highPathConstant_pos (3^d) Q.ρ_pos heta0
  refine ⟨Cfr,eta0,(c^2/(3*(3^d:ℕ)*(2+c)^2)),hCfr,hmin,heta0,(div_pos (sq_pos_of_pos hc) (by positivity)),?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  dsimp only
  intro cf hcf hcfH heta cm hcm hcmU n E hE heps H hH hH0 hdom hbudget
  let eta := cf*(k:ℝ)^(-C.smoothness)
  let Bl := highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass/highCenterMix C
  let I := Real.sqrt ((3^d:ℕ)*(k:ℝ)^d*E)
  let delta := localScorePathLength c Bl I
  have hBl : 0 ≤ Bl := div_nonneg (completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN).total_positive.le (highCenterMix_mem C).1.le
  have hI : 0 ≤ I := Real.sqrt_nonneg _
  have hdelt : 0 < delta := localScorePathLength_pos hc hBl hI
  have hnumE : 0 ≤ (k:ℝ)^d*E := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hE
  have hbudget0 : 0 ≤ (3^d:ℕ)*(k:ℝ)^d*E := by positivity
  have heta0' : 0 ≤ eta := mul_nonneg hcf (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hh := hpath U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
    cf hcf hcfH heta cm hcm hcmU n delta ((3^d:ℕ)*(k:ℝ)^d*E) hdelt.le hbudget0
    (highPath_update_budget (3^d) Q.ρ_pos heta0 hBl hI) (highPath_variance_budget (3^d) Q.ρ_pos heta0 hBl hI heta0' heta) heps H hH hH0 hdom hbudget
  have hK : (1:ℝ) ≤ (3^d:ℕ) := by exact_mod_cast one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)
  have hn := score_cost_scaled_numeric (eta := eta) hc hBl hI (mul_nonneg hdelt.le hI)
    (show delta*I ≤ localScorePathLength c Bl I*I from le_rfl) hK hnumE (by simpa only [I,mul_assoc] using Real.sq_sqrt hbudget0)
  exact ((ENNReal.ofReal_le_ofReal (sub_le_sub_right hn _)).trans hh)
end NearlyMinimax
namespace NearlyMinimax
open Filter MeasureTheory Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
theorem eventually_actual_lowerSaddle_penalized_rate_square
    {s d a b cf CG ctr cm Cmgf DV : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hcf : 0 < cf) (hCG : 0 < CG) (hctr : 0 < ctr)
    (hcm : 0 < cm) (hCmgf : 0 < Cmgf) (C : ℝ) :
    ∃ c, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let τM := shrunkDensityExponent a b
      (c*rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x)^2 ≤
      ctr/(3*CG)*(lowerSaddleRisk s d m θ C cf τM x)^2-
        DV^2*lowerSaddleExceptionalTail d m θ C (cm^2/(8*Cmgf)) x := by
  have h_actual_lowerSaddleRisk_rate_bracket : ∃ c A, 0 < c ∧ 0 < A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x ≤
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ∧
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ≤
      A * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x := by
    have hτ := densityIntervalExponent_pos ha hab
    obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
    have hh := eventually_lowerSaddleRisk_rate_bracket (C := C)
      hs hd (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ) hcf hcontrol
      (lowerSaddleTheta_relation hs)
    have h_lower_saddle_stretchConstant {τ} (hτ : 0 < τ) : 2 * d * τ / (d + 4) * lowerSaddleCoefficient s d τ = stretchConstant s d τ := by
      have : 0 < d := by linarith
      have : 0 < d + 4 := by linarith
      have : 0 < s - 1 := by linarith
      have : 0 < d - 4 * s := by linarith
      have hm : 0 ≤ 8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ) := by positivity
      have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
      unfold lowerSaddleCoefficient stretchConstant
      apply (sq_eq_sq₀ (by positivity) (by positivity)).1
      simp only [mul_pow, div_pow, Real.sq_sqrt hm, Real.sq_sqrt hk]
      field_simp
      ring
    rw [(h_lower_saddle_stretchConstant hτ)] at hh
    exact hh
  obtain ⟨c₀,A,hc₀,hA,hbracket⟩ := h_actual_lowerSaddleRisk_rate_bracket
  let α := ctr/(3*CG)
  have hα : 0 < α := by dsimp [α]; positivity
  let q := α*c₀^2/2
  have hq : 0 < q := by dsimp [q]; positivity
  let c := Real.sqrt q
  have hc : 0 < c := Real.sqrt_pos.mpr hq
  have hcsq : c^2 = q := Real.sq_sqrt hq.le
  have htol : 0 < q/(DV^2+1) := by positivity
  have h_actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero : Tendsto (fun x =>
      lowerSaddleExceptionalTail d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C (cm ^ 2 / (8 * Cmgf)) x /
        (rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
          (lowerLogPower s d) x) ^ 2) atTop (𝓝 0) := by
    have hτ := densityIntervalExponent_pos ha hab
    exact lowerSaddleExceptionalTail_over_rate_tends_zero (by linarith)
      (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ)
      (by positivity) C (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b)) (lowerLogPower s d)
  have ht := h_actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero.eventually (eventually_lt_nhds htol)
  refine ⟨c,hc,?_⟩
  filter_upwards [hbracket,ht] with x hb hx
  dsimp only at hb hx ⊢
  let S := rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
    (lowerLogPower s d) x
  let R := lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
    (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x
  let ε := lowerSaddleExceptionalTail d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
    (lowerSaddleTheta s d (densityIntervalExponent a b)) C (cm^2/(8*Cmgf)) x
  have : 0 < S := rateScale_pos _ _ _ _
  have hR : 0 < R := lowerSaddleRisk_positive hcf _
  have hlow : c₀*S ≤ R := hb.1
  have hsq : (c₀*S)^2 ≤ R^2 := (sq_le_sq₀ (by positivity) hR.le).mpr hlow
  have hε : ε ≤ (q/(DV^2+1))*S^2 := by
    apply (div_le_iff₀ (by positivity)).mp
    exact hx.le
  have hfrac : DV^2*(q/(DV^2+1)) ≤ q := by
    have hp : 0 ≤ q := hq.le
    have he : DV^2*(q/(DV^2+1)) = DV^2*q/(DV^2+1) := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hp]
  have hp1 := mul_le_mul_of_nonneg_left hε (sq_nonneg DV)
  have hp2 := mul_le_mul_of_nonneg_right hfrac (sq_nonneg S)
  have hpen : DV^2*ε ≤ q*S^2 := by nlinarith only [hp1,hp2]
  have hmain := mul_le_mul_of_nonneg_left hsq hα.le
  change (c*S)^2 ≤ α*R^2-DV^2*ε
  rw [mul_pow,hcsq]
  dsimp [q] at hpen ⊢
  nlinarith only [hpen,hmain]
theorem completeSourceSaddle_penalized_numeric_envelope  [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf CB C5 C6 C7 ch ctr cm Cω : ℝ}
    (hcf : 0 < cf) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch) (hctr : 0 < ctr) (hcm : 0 < cm)
    (hshift : 1+Real.log (rawCostConstant CB C5 C6 C7 cf ch)+
      ((d : ℝ)^2-16*C.smoothness)/((d : ℝ)*((d : ℝ)+4))*highCompleteSourceSaddleTheta C+
      2*d*densityIntervalExponent C.densityLower C.densityUpper/((d : ℝ)+4) < Cω) :
    ∃ c, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let tauM := shrunkDensityExponent C.densityLower C.densityUpper
      let k := lowerSaddleGrid d m theta Cω n
      let B := lowerSaddleActivity C.smoothness d m theta Cω tauM n
      ∀ Bl E, 1 ≤ B → 0 ≤ Bl → 0 ≤ E → Bl ≤ CB*B →
      E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf C5 C6 C7 ch Bl tauM n →
      (c*paperRiskScale C n)^2 ≤ ctr*(cf*k^(-C.smoothness))^4/(1+Bl^2+k^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2*highCompleteSourceSaddleTail C Cω cm n := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let CG := rawCostConstant CB C5 C6 C7 cf ch
  have hCG : 0 < CG := lt_of_lt_of_le zero_lt_one (rawCostConstant_ge_one _ _ _ _ _ _)
  obtain ⟨c,hc,hpen⟩ := eventually_actual_lowerSaddle_penalized_rate_square
    hs hd C.densityLower_pos hab hcf hCG hctr hcm (highHistoryMassMomentConstant_pos d C.densityLower C.densityUpper hab) Cω
  have hcost := eventually_actual_lowerSaddle_raw_cost hs hd C.densityLower_pos hab
    hcf.le hCB hC5 hC6 hC7 hch hshift
  refine ⟨c,hc,?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hpen,
    tendsto_natCast_atTop_atTop.eventually hcost,eventually_ge_atTop 2] with n hn hcst hn2
  dsimp only at hn hcst ⊢
  intro Bl E hB hBl hE hBlcap hEcap
  have hcost' : 1+Bl^2+
      (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d*E ≤
      3*CG*(lowerSaddleActivity C.smoothness d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) n)^2 := by
    have h_completeSourceSaddle_inverse_volume {d : ℕ} (C : ModelConstants d) : (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d =
        (lowerSaddleH d (highCompleteSourceSaddleCoefficient C)
          (highCompleteSourceSaddleTheta C) Cω n)^(-(d : ℝ)) := by
      unfold lowerSaddleH
      rw [Real.rpow_neg (inv_nonneg.mpr (Nat.cast_nonneg _)),Real.rpow_natCast,inv_pow,inv_inv]
    rw [(h_completeSourceSaddle_inverse_volume C)]
    exact hcst Bl E hB hBl hBlcap hEcap
  have hmain := lowerSaddle_cost_risk_reduction (cf := cf)
    (shrunkDensityExponent C.densityLower C.densityUpper) (by positivity) hCG hctr.le hcost'
  rw [← completeSourceSaddle_eta_eq C Cω cf n] at hmain
  rw [paperRiskScale_eq_rateScale C hn2]
  apply hn.trans
  exact sub_le_sub_right hmain _
theorem minimaxRMS_lower_of_squared_lower {d n : ℕ} (C : ModelConstants d)
    {r : ℝ} (hr : 0 ≤ r) (h : ENNReal.ofReal (r^2) ≤ minimaxRisk C n) :
    ENNReal.ofReal r ≤ minimaxRMS C n := by
  rw [ENNReal.ofReal_pow hr] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_natCast_mul] at hh
  norm_num only [Nat.cast_ofNat, mul_one_div_cancel, ENNReal.rpow_one] at hh
  exact hh
def CompleteSaddleCostRiskBudget  (C : ModelConstants d)
    (cf CB C5 C6 C7 ch ctr cm Cω : ℝ) (n : ℕ) : Prop :=
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tauM := shrunkDensityExponent C.densityLower C.densityUpper
  let k := lowerSaddleGrid d m theta Cω n
  let B := lowerSaddleActivity C.smoothness d m theta Cω tauM n
  ∃ Bl E, 1 ≤ B ∧ 0 ≤ Bl ∧ 0 ≤ E ∧ Bl ≤ CB*B ∧
    E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf C5 C6 C7 ch Bl tauM n ∧
    ∀ U,
      ENNReal.ofReal (ctr*(cf*k^(-C.smoothness))^4/(1+Bl^2+k^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2*highCompleteSourceSaddleTail C Cω cm n) ≤
        minimaxRisk (C.withDomain U) n
section
theorem completeSaddleSpatialSeries_eq  (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω ) (n : ℕ)
    [NeZero (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω n)] :
    highSourceSpatialSeries d (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω n) n C.densityLower Q.c
      (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) =
    (3^d : ℕ)*(lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d *
      (∑ r ∈ Finset.range (n+1), poissonCountWeight
        (completeSaddleScoreFactor C Q*completeSaddleMu C Cω n) r *
        ∫ u, completeSaddleGeometryEnvelope C Q Cfr cf Cω n r u ∂fullSpatialPatchDesign d r) := by
  let k := lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω n
  have h_high_design_factorial_parameter : ↑n * highFixedScoreDenominator C.densityLower Q.c * (2 / ↑k) ^ d =
      (highFixedScoreDenominator C.densityLower Q.c) * ↑2 ^ d * (completeSaddleMu C Cω n) := by
    have hmu : (completeSaddleMu C Cω n) = ↑n / ↑k ^ d := (by dsimp only [completeSaddleMu,lowerSaddleMu,lowerSaddleH,k]; rw [Real.rpow_natCast,inv_pow]; rfl)
    rw [hmu, div_pow]
    ring
  have hparameter : ↑n*highFixedScoreDenominator C.densityLower Q.c*(2/↑k)^d =
      completeSaddleScoreFactor C Q*completeSaddleMu C Cω n :=
    h_high_design_factorial_parameter
  change highSourceSpatialSeries d k n C.densityLower Q.c _ = _
  have h_highWindowLabels_card : Fintype.card (HighWindowLabels d k) = k ^ d := by
    simp only [HighWindowLabels, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  simp only [highSourceSpatialSeries,hparameter,Finset.sum_const,Finset.card_univ,
    h_highWindowLabels_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  simp only [poissonCountWeight,fullSpatialPatchDesign]
  ring
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
 theorem completeSaddleGeometry_witness {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ)) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ Cfr cf : ℝ, Cfr0 ≤ Cfr → 0 < cf → ∀ Cω : ℝ,
      ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let k := lowerSaddleGrid d m theta Cω n
      let D := completeSaddleD C n
      let M := completeSaddleM C n
      let q := lowerSaddleResponseOrder C.smoothness d
      let ell := completeSaddleEll C Cω n
      let N := completeSaddleN C Cω n
      let mu := completeSaddleMu C Cω n
      let eta := completeSaddleEta C Cω cf n
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      ∃ E : ℝ, 0 ≤ E ∧
        E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf (completeSaddleDefectConstant C Q Cfr)
          (completeSaddleAliasConstant C Q Cfr) (completeSaddleFieldConstant C Q Cfr) (completeSaddleExteriorConstant C Q)
          (highRowTotalMass R.rowMass/highCenterMix C) (shrunkDensityExponent C.densityLower C.densityUpper) n ∧
        (∀ r, Integrable (completeSaddleGeometryEnvelope C Q Cfr cf Cω n r) (fullSpatialPatchDesign d r)) ∧
        (∀ r U, 0 ≤ completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U) ∧
        (∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
          ∀ h : HighCompleteSourceHistory C k D M q Cfr (spatialInterpolationLambda d) ell N mu,
          ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
          selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a V eta h j) x ≤
            completeSaddleGeometryEnvelope C Q Cfr cf Cω n r (highPatchProductChart d k j x)) ∧
        highSourceSpatialSeries d k n C.densityLower Q.c (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) ≤
          (3^d : ℕ)*↑k^d*E := by
  have h_eventually_completeSaddleGeometry_factorial {cf : ℝ} (hcf : 0 < cf) (Cfr) (Cω) : ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.range (n+1), poissonCountWeight
        (completeSaddleScoreFactor C Q*completeSaddleMu C Cω n) r *
        ∫ U, completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U ∂fullSpatialPatchDesign d r) ≤
          completeSaddleEnergyBudget C Q Cfr cf Cω n := by
    have h_completeSaddleScoreFactor_pos : 0 < completeSaddleScoreFactor C Q := by
      unfold completeSaddleScoreFactor highFixedScoreDenominator
      positivity [C.densityLower_pos, Q.c_pos]
    have hCs := h_completeSaddleScoreFactor_pos.le
    have h : (4 : ℝ)<d := by linarith only [hs,hd]
    have : 4<d := by exact_mod_cast h
    have hOrdConst : 0 ≤ completeSaddleOrdinaryConstant C Q Cfr :=
      zero_le_one.trans (ordinaryFineAliasFactorialConstant_ge_one ((zero_lt_one.trans C.one_lt_densityUpper).le) hCs)
    have hCal : 0 ≤ finePairSaddleAliasFactorialConstant d (lowerSaddleResponseOrder C.smoothness d)
        C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C) (completeSaddleDegreeFactor d)
          (3*completeSaddleScoreFactor C Q) := by
      unfold finePairSaddleAliasFactorialConstant aliasTailConstant
      have := finePairUniformSpatialPrefactor_nonneg d (lowerSaddleResponseOrder C.smoothness d)
        C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C)
      have := spatialInverseFourConstant_nonneg d
      have := finePairAliasGeometricBase_nonneg d C.densityUpper
      positivity
    filter_upwards [eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
      tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
        hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω cf
        (lowerSaddleResponseOrder C.smoothness d) Cfr Q.a Q.ρ (completeSaddleScoreFactor C Q) hCs),
      tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters C hs hd hcf
        (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1) Cω)] with n G hO hphysical
    let M := completeSaddleM C n
    let D := completeSaddleD C n
    let q := lowerSaddleResponseOrder C.smoothness d
    let N := completeSaddleN C Cω n
    let mu := completeSaddleMu C Cω n
    let ell := completeSaddleEll C Cω n
    let eta := completeSaddleEta C Cω cf n
    let tau := completeSaddleTau C n
    let c0 := completeSaddleC0 C
    let Cs := completeSaddleScoreFactor C Q
    let K := completeSaddleDegreeFactor d
    let R := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
    let Cord := completeSaddleOrdinaryConstant C Q Cfr
    let Bl := completeSourceSaddleActivity C q Cfr (spatialInterpolationLambda d) Cω n
    let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
    have hD : 3 ≤ D := hphysical.2.1
    have hext : exteriorTau (((C.densityLower+(M : ℝ)⁻¹)+(C.densityUpper-(M : ℝ)⁻¹))/
        ((C.densityUpper-(M : ℝ)⁻¹)-(C.densityLower+(M : ℝ)⁻¹))) = tau := by
      have h := exteriorTau_sqrt_ratio (completeSaddleAD C n) (completeSaddleBD C n) G.ad_positive G.density_interval
      simpa only [tau,completeSaddleTau,shrunkDensityExponent,densityIntervalExponent,completeSaddleAD,completeSaddleBD,one_div] using h
    have hOrd : (∑ j ∈ Finset.range (D-M), poissonCountWeight (Cs*mu) (M+1+j) *
        ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := M+1+j) (F := D)
          (ordinaryFineAliasTargetSet d D ell N mu) M R q C.densityLower C.densityUpper c0 Cfr Q.a Q.ρ eta ell
          (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (M+1+j)) ≤
        Cord*(eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))*poissonCountWeight (Cord*mu) (M+1) := by
      simpa only [ordinaryFineAliasSaddleGeometryEnvelope,ordinaryFineAliasSaddleCoefficient,ordinaryFineAliasSaddleTheta,
        M,D,q,N,mu,ell,eta,tau,c0,Cs,R,Cord,completeSaddleOrdinaryConstant,
        highCompleteSourceSaddleCoefficient,highCompleteSourceSaddleTheta,completeSaddleM,completeSaddleD,
        completeSaddleN,completeSaddleMu,completeSaddleEll,completeSaddleEta,completeSaddleTau,completeSaddleC0] using hO (fun _ => D)
    have hHigher := finite_complete_higher_geometry_energy_le (by omega) hD C.densityLower C.densityUpper c0 K ell N mu
      M R q Cfr Q.a Q.ρ eta Cs _ C.densityLower_pos Q.a_pos
      (by simpa only [completeSaddleAD,completeSaddleBD,one_div] using G.density_interval) (hext.trans_le G.tau_le)
      (by dsimp [c0,completeSaddleC0]; linarith [densityIntervalExponent_pos C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)])
      (by dsimp [K,completeSaddleDegreeFactor]; positivity) hCs G.ell_one G.ell_lt_N.le rfl G.degree_multiple
      G.mu_positive G.mu_one G.mu_log G.response_taylor (by rw [hext]; convert G.field_scale_square using 1 <;> ring) hOrd
    have h_completeSourceGeometryEnvelope_factorial_from_higher {d} (hd : 0 < d) (aD : ℝ) (bD : ℝ) (a : ℝ) (rho : ℝ) (hN : 0 < N) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (hbd : 0 ≤ bD-(M : ℝ)⁻¹) (hbdB : bD-(M : ℝ)⁻¹ ≤ bD) (hCal : 0 ≤ finePairSaddleAliasFactorialConstant d q aD bD Cfr a rho c0 K (3*Cs)) (htau : 0 ≤ tau) (hhigher : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) * ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D) aD bD c0 ell N mu M R q Cfr a rho eta U ∂fullSpatialPatchDesign d (3+j)) ≤ 4*(cardinalGeometryFactorialConstant d q bD Cfr a rho Cs*eta^4*N^(-(d : ℝ))*mu^2 + Cord*(eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))*poissonCountWeight (Cord*mu) (M+1) + finePairSaddleAliasFactorialConstant d q aD bD Cfr a rho c0 K (3*Cs) * (eta^4*N^(4-(d : ℝ))) * poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD Cfr a rho c0 K (3*Cs)*mu) (M+1) + finePairFieldFactorialConstant d q aD bD Cfr a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ)))) : (∑ r ∈ Finset.range (n+1), poissonCountWeight (Cs*mu) r *
        ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu Cfr a rho eta Chi Bl r U
          ∂fullSpatialPatchDesign d r) ≤
        3*(completeGeometryDefectConstant d q bD Cfr a rho Cs+
          completeGeometryFieldConstant d q aD bD Cfr a rho c0 Cs)*eta^4*mu^2*N^(-(d : ℝ)) +
        3*completeGeometryAliasConstant d q aD bD Cfr a rho c0 K Cs Cord*eta^4*
          (Real.exp (2*tau*M)*N^(4-(d : ℝ)))*
            poissonCountWeight (completeGeometryAliasConstant d q aD bD Cfr a rho c0 K Cs Cord*mu) (M+1) +
        Real.exp (completeGeometryExteriorConstant d Cs Chi)*eta^4*(Bl+1)^2*
          poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) (D+1) := by
      let e := fun r => ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu Cfr a rho eta Chi Bl r U
        ∂fullSpatialPatchDesign d r
      have he (r : ℕ) : 0 ≤ e r := integral_nonneg
        (fun U => completeSourceGeometryEnvelope_nonneg D M R q aD bD c0 ell N mu Cfr a rho eta Chi Bl r U)
      have h_completeSourceGeometryEnvelope_pair_factorial_le : poissonCountWeight (Cs*mu) 2 *
          (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu
            Cfr a rho eta Chi Bl 2 U ∂fullSpatialPatchDesign d 2) ≤
          completeGeometryRadialConstant d bD a rho Cs * eta^4*mu^2*N^(-(d : ℝ)) := by
        have h_completeSourceGeometryEnvelope_pair_integral_le : (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu Cfr a rho eta Chi Bl 2 U
            ∂fullSpatialPatchDesign d 2) ≤ 9*finePairCountTwoSpatialBudget d (bD-(M : ℝ)⁻¹) a rho eta N := (finePairCountTwoGeometryEnvelope_integrable_and_le hd _ _ _ _ hN).2
        have hi := h_completeSourceGeometryEnvelope_pair_integral_le
        apply (mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (mul_nonneg hCs hmu) 2)).trans
        have hp  := pow_le_pow_left₀ hbd hbdB 4
        let K := 27*Cs^2*((2*rho+a)/a^2)^4*(2 : ℝ)^d*spatialExponentialConstant d *
          eta^4*mu^2/(N^d)
        have hK : 0 ≤ K := by
          have := spatialExponentialConstant_nonneg d
          positivity
        have h := mul_le_mul_of_nonneg_right hp hK
        rw [Real.rpow_neg hN.le, Real.rpow_natCast]
        convert h using 1 <;> simp only [poissonCountWeight, finePairCountTwoSpatialBudget, completeGeometryRadialConstant]
          <;> dsimp [K] <;> ring
      have h_completeSourceGeometryEnvelope_exterior_factorial_le : (∑ j ∈ Finset.range (n+1), poissonCountWeight (Cs*mu) (D+1+j) *
          ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu
            Cfr a rho eta Chi Bl (D+1+j) U ∂fullSpatialPatchDesign d (D+1+j)) ≤
          Real.exp (completeGeometryExteriorConstant d Cs Chi) * eta^4*(Bl+1)^2 *
            poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) (D+1) := by
        have hD  := (by omega)
        let B := 3*(2 : ℝ)^d*Chi^2
        let P := eta^4*(Bl+1)^2
        let ch := completeGeometryExteriorConstant d Cs Chi
        have hP : 0 ≤ P := by dsimp [P]; positivity
        have hbase : Cs*B ≤ ch := le_max_right _ _
        have heq (j : ℕ) :
            (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu
              Cfr a rho eta Chi Bl (D+1+j) U ∂fullSpatialPatchDesign d (D+1+j)) =
            B^(D+1+j)*P := by
          have h := completeSourceGeometryEnvelope_exterior_integral_of_three_le (d := d) D M R q (D+1+j)
            (by omega) (by omega) aD bD c0 ell N mu Cfr a rho eta Chi Bl
          simpa only [B, P, mul_assoc] using h
        simp_rw [heq]
        have hterm (j : ℕ) : poissonCountWeight (Cs*mu) (D+1+j) * (B^(D+1+j)*P) =
            P * poissonCountWeight (Cs*B*mu) (D+1+j) := by
          unfold poissonCountWeight
          rw [mul_pow, mul_pow, mul_pow]
          ring
        simp_rw [hterm]
        rw [← Finset.mul_sum]
        apply (mul_le_mul_of_nonneg_left (finite_poissonCountWeight_tail_le (by positivity : 0 ≤ Cs*B*mu) (D+1) (n+1)) hP).trans
        have hweight := poissonCountWeight_mono (by positivity : 0 ≤ Cs*B*mu)
          (mul_le_mul_of_nonneg_right hbase hmu) (D+1)
        have h := mul_le_mul (by apply Real.exp_le_exp.mpr; exact (mul_le_of_le_one_right (mul_nonneg hCs (by dsimp [B]; positivity)) hmu1).trans hbase) hweight (poissonCountWeight_nonneg (by positivity) _)
          (Real.exp_pos ch).le
        exact (mul_le_mul_of_nonneg_left h hP).trans_eq (by dsimp [P,ch]; ring)
      have hh : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j)*e (3+j)) ≤
          4*(cardinalGeometryFactorialConstant d q bD Cfr a rho Cs*eta^4*N^(-(d : ℝ))*mu^2 +
            Cord*(eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))*poissonCountWeight (Cord*mu) (M+1) +
            finePairSaddleAliasFactorialConstant d q aD bD Cfr a rho c0 K (3*Cs) *
              (eta^4*N^(4-(d : ℝ))) *
              poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD Cfr a rho c0 K (3*Cs)*mu) (M+1) +
            finePairFieldFactorialConstant d q aD bD Cfr a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ))) := by
        apply le_trans (le_of_eq ?_) hhigher
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [e]
        rw [completeSourceGeometryEnvelope_refined_integral D M R q j (by
          have hj' := Finset.mem_range.mp hj
          omega)]
      have hblocks := finite_count_energy_from_blocks (mul_nonneg hCs hmu) n D (by omega)
        e he (by simp [e,completeSourceGeometryEnvelope]) (by simp [e,completeSourceGeometryEnvelope]) _ _ _ (h_completeSourceGeometryEnvelope_pair_factorial_le) hh (h_completeSourceGeometryEnvelope_exterior_factorial_le)
      have ha := four_component_raw_energy_algebra hmu
        (by positivity : 0 ≤ eta^4*mu^2*N^(-(d : ℝ)))
        (by positivity : 0 ≤ eta^4*Real.exp (2*tau*M)*N^(4-(d : ℝ)))
        (by positivity : 0 ≤ eta^4*N^(4-(d : ℝ))) (by have heone : 1 ≤ Real.exp (2*tau*M) := Real.one_le_exp (by positivity); have h := mul_le_mul_of_nonneg_left heone (by positivity : 0 ≤ eta^4*N^(4-(d : ℝ))); convert h using 1 <;> ring) hOrdConst hCal M
        (A2 := completeGeometryRadialConstant d bD a rho Cs)
        (Ad := cardinalGeometryFactorialConstant d q bD Cfr a rho Cs)
        (Af := finePairFieldFactorialConstant d q aD bD Cfr a rho c0 (3*Cs))
      apply hblocks.trans
      have h := add_le_add_right ha
        (Real.exp (completeGeometryExteriorConstant d Cs Chi)*eta^4*(Bl+1)^2*
          poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) (D+1))
      convert h using 1 <;> (try dsimp [e,completeGeometryDefectConstant,completeGeometryFieldConstant,completeGeometryAliasConstant]) <;> ring
    have h := (h_completeSourceGeometryEnvelope_factorial_from_higher (NeZero.pos d) C.densityLower C.densityUpper Q.a Q.ρ (lt_of_lt_of_le zero_lt_one G.N_one) G.mu_positive.le G.mu_one (by simpa only [completeSaddleBD,one_div] using G.bd_nonneg) (by simpa only [completeSaddleBD,one_div] using G.bd_le) hCal G.tau_nonneg hHigher)
    convert h using 1 <;> (try dsimp only [completeSaddleGeometryEnvelope,completeSaddleEnergyBudget,
      completeSaddleDefectConstant,completeSaddleAliasConstant,completeSaddleFieldConstant,completeSaddleExteriorConstant,
      lowerSaddleRawEnergyBound,M,D,q,N,mu,ell,eta,tau,c0,Cs,K,R,Cord,Bl,Chi,
      completeSaddleM,completeSaddleD,completeSaddleN,completeSaddleMu,completeSaddleEll,
      completeSaddleEta,completeSaddleTau,completeSaddleC0]) <;> (try simp only [poissonCountWeight]) <;> ring
  have h_completeSource_original_all_geometry : ∃ Cfr0 eta0, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 2 ≤ q → highCenterResolutionThreshold C ≤ ↑M →
      ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 1 ≤ ell → ell < N → 0 ≤ cf →
      cf*↑k^(-C.smoothness) ≤ eta0 →
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 →
      (∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu) →
      (∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) →
      ∀ Rbound : ℕ, (∀ r ∈ ordinaryFineAliasTargetSet d D ell N mu, 1 ≤ r ∧ r ≤ Rbound) →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/↑M)
          (C.densityUpper-1/↑M) Cfr (spatialInterpolationLambda d) ell N mu)),
      ∀ n : ℕ, ∀ x : Fin n → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      let eta := cf*↑k^(-C.smoothness)
      let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
        completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta
          Chi (highRowTotalMass R.rowMass) n (highPatchProductChart d k j x) := by
    obtain ⟨CG,eG,hCG,heG,hguards⟩ := completeSource_original_local_guards C Q
    obtain ⟨CR,eR,hCR,heR,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
    have h_completeSource_original_count_two : ∃ Cfr0 eta0, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
        ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
        4 ≤ k → 3 ≤ D → 2 ≤ q → highCenterResolutionThreshold C ≤ ↑M →
        ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
        cf*↑k^(-C.smoothness) ≤ eta0 →
        ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
        ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
          (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/↑M)
            (C.densityUpper-1/↑M) Cfr lam ell N mu)),
        ∀ x : Fin 2 → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
        ∀ y : Fin 2 → Fin 3,
        let R := completeSourceRows C k D M q Cfr lam ell N mu
        let eta := cf*↑k^(-C.smoothness)
        let c := (highUnionSourceState C R h).2
        let U := fun i : Fin 2 => highLocalCoordinates d k j (x i)
        let g := fun i : Fin 2 => highLocalFieldWithout d k D eta c j (x i)
        let w := fun i : Fin 2 => highPeriodicTensor d k j (x i)
        highUnionSourceMarkedNumerator C R 2 Q.a V eta j h x y =
          eta^2*w 0*w 1*highUnionSourceDensity C R h (x 0)*highUnionSourceDensity C R h (x 1)*
          ((1+N*exactEuclideanDistance (U 0) (U 1))*Real.exp (-(N*exactEuclideanDistance (U 0) (U 1))))*
          ternaryMeanDerivative Q.a (coefficientRegression eta g w (fun i => highFrameFeature (U i)) (c j) 0) (y 0)*
          ternaryMeanDerivative Q.a (coefficientRegression eta g w (fun i => highFrameFeature (U i)) (c j) 1) (y 1) := by
      obtain ⟨Cfr0,eta0,hfr0,heta0,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
      refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
      intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta V hV j h x hx y
      letI := hk0
      letI := horder
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let eta := cf*↑k^(-C.smoothness)
      let c := (highUnionSourceState C R h).2
      let U := fun i : Fin 2 => highLocalCoordinates d k j (x i)
      let p := fun i : Fin 2 => highUnionSourceDensity C R h (x i)
      let g := fun i : Fin 2 => highLocalFieldWithout d k D eta c j (x i)
      let w := fun i : Fin 2 => highPeriodicTensor d k j (x i)
      have he := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
        hfr hell hellN hcf heta V hV j h 2 x hx y).1
      have G := completeSourceRows_guards C k D M q hD (by omega) hM Cfr lam ell N mu
        (hfr0.trans hfr) hell hellN
      obtain ⟨ha,hab⟩ := high_source_interval_numeric C ↑M hM
      have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards C ↑M hM).1
      have hp (i : Fin 2) : p i ∈ Icc (C.densityLower+1/↑M) (C.densityUpper-1/↑M) :=
        highUnionSourceDensity_interval C R G h (x i)
      have hU (i : Fin 2) (r : Fin d) : |U i r| ≤ 2 :=
        (highLocalCoordinates_abs_le_one d k j (x i) r).trans (by norm_num)
      have hQ (i : Fin 2) : U i ∈ hyperplaneCube d :=
        highLocalCoordinates_abs_le_one d k j (x i)
      exact he.trans (completeSourceRawNumerator_count_two _ _ lam ell N mu ha hab hell.le hellN.le
        D M q hD hM2 hq Cfr Q.a V eta (by linarith) U hU hQ p g w hp (c j) y)
    obtain ⟨CP,eP,hCP,heP,hpair⟩ := h_completeSource_original_count_two
    have h_completeSource_original_higher_geometry : ∃ Cfr0 eta0, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
        ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
        4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ ↑M →
        ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 1 ≤ ell → ell < N → 0 ≤ cf →
        cf*↑k^(-C.smoothness) ≤ eta0 →
        shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 →
        (∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu) →
        (∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) →
        ∀ Rbound : ℕ, (∀ r ∈ ordinaryFineAliasTargetSet d D ell N mu, 1 ≤ r ∧ r ≤ Rbound) →
        ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
        ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
          (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/↑M)
            (C.densityUpper-1/↑M) Cfr (spatialInterpolationLambda d) ell N mu)),
        ∀ n : ℕ, 3 ≤ n → n ≤ D → ∀ x : Fin n → Covariate d,
        (∀ i, x i ∈ highTorusPatch d k j) →
        let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
        let eta := cf*↑k^(-C.smoothness)
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
          completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
            M Rbound q Cfr Q.a Q.ρ eta (highPatchProductChart d k j x) := by
      obtain ⟨CfrG,etaG,hfrG,hetaG,hguards⟩ := completeSource_original_local_guards C Q
      obtain ⟨CfrR,etaR,hfrR,hetaR,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
      refine ⟨max CfrG CfrR, min etaG etaR, hfrG.trans (le_max_left _ _), lt_min hetaG hetaR,?_⟩
      intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
        Rbound hI V hV j h n hn hnD x hx
      letI := hk0
      letI := horder
      let lam := spatialInterpolationLambda d
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let eta := cf*↑k^(-C.smoothness)
      let c := (highUnionSourceState C R h).2
      let U := highPatchProductChart d k j x
      let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
      let g := fun i : Fin n => highLocalFieldWithout d k D eta c j (x i)
      let w := fun i : Fin n => highPeriodicTensor d k j (x i)
      have hfrg := (le_max_left CfrG CfrR).trans hfr
      have hfr1 := hfrG.trans hfrg
      have hellp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
      have H := hguards k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfrg hellp hellN hcf (heta.trans (min_le_left _ _)) h
      obtain ⟨had,hab⟩ := high_source_interval_numeric C ↑M hM
      have hUi (i : Fin n) (l : Fin d) : |U i l| ≤ 2 :=
        (highLocalCoordinates_abs_le_one d k j (x i) l).trans (by norm_num)
      have hpi (i : Fin n) : p i ∈ Icc (C.densityLower+1/↑M) (C.densityUpper-1/↑M) :=
        highUnionSourceDensity_interval C R (completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hfr1 hellp hellN) h (x i)
      have hp (f : ℝ) (hf : |f| ≤ Q.ρ) (u : Fin 3) : 0 ≤ ternaryMass Q.a f V u :=
        Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 u)
      have hcap := completeSourceRawNumerator_higher_square_le_geometry C.densityLower C.densityUpper c0 ell N mu
        C.densityLower_pos hell D M Rbound q (by simpa only [one_div] using hab) htau hn hnD hq hnu hFine hI Cfr Q.a V eta Q.ρ
        hfr1 Q.a_pos H.amplitude_nonneg Q.ρ_pos.le H.amplitude_half U hUi p g w (by simpa only [one_div] using hpi)
        (fun i => H.without_abs j (x i)) (fun i => H.weight_abs j (x i)) (c j) (H.coefficient_ball j) hp
      have he (y : Fin n → Fin 3) : highUnionSourceRawNumerator C R n Q.a V eta h j x y =
          completeSourceRawNumerator (C.densityLower+1/↑M) (C.densityUpper-1/↑M) lam ell N mu
            D M q Cfr Q.a V eta U p g w (c j) y :=
        (hresponse k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf ((le_max_right CfrG CfrR).trans hfr) hellp hellN hcf (heta.trans (min_le_right _ _))
          V hV j h n x hx y).1
      have hs : selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x =
          ∑ y : Fin n → Fin 3, completeSourceRawNumerator (C.densityLower+1/↑M) (C.densityUpper-1/↑M) lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y^2 := by
        unfold selectedRawSquareEnergy
        apply Finset.sum_congr (by ext y; simp)
        intro y _
        rw [he]
      change selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
        completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu M Rbound q Cfr Q.a Q.ρ eta U
      exact hs.trans_le (by simpa only [one_div] using hcap)
    obtain ⟨CH,eH,hCH,heH,hhigher⟩ := h_completeSource_original_higher_geometry
    obtain ⟨CB,eB,hCB,heB,hcrude⟩ := completeSourceNumerator_original_field_bound C Q
    let C0 := max (max CG CR) (max CP (max CH CB))
    let e0 := min (min eG eR) (min eP (min eH eB))
    have hG0 : CG ≤ C0 := (le_max_left _ _).trans (le_max_left _ _)
    have hR0 : CR ≤ C0 := (le_max_right _ _).trans (le_max_left _ _)
    have heR0 : e0 ≤ eR := (min_le_left _ _).trans (min_le_right _ _)
    refine ⟨C0,e0,hCG.trans hG0,lt_min (lt_min heG heR) (lt_min heP (lt_min heH heB)),?_⟩
    intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
      Rbound hI V hV j h n x hx
    letI := hk0
    letI := horder
    let lam := spatialInterpolationLambda d
    let R := completeSourceRows C k D M q Cfr lam ell N mu
    let eta := cf*↑k^(-C.smoothness)
    let c := (highUnionSourceState C R h).2
    let U := highPatchProductChart d k j x
    let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
    let g := fun i : Fin n => highLocalFieldWithout d k D eta c j (x i)
    let w := fun i : Fin n => highPeriodicTensor d k j (x i)
    let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
    have hellp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
    have H := hguards k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
      (hG0.trans hfr) hellp hellN hcf (heta.trans ((min_le_left _ _).trans (min_le_left _ _))) h
    have G := completeSourceRows_guards C k D M q hD (by omega) hM Cfr lam ell N mu (hCG.trans (hG0.trans hfr)) hellp hellN
    change selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
      completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta
        Chi (highRowTotalMass R.rowMass) n U
    rcases n with _|_|_|n
    · have hz (y : Fin 0 → Fin 3) := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
        (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 0 x hx y).2 (by omega)
      change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 0 Q.a V eta h j) x ≤ 0
      simp only [selectedRawSquareEnergy]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro y _
      change highUnionSourceMarkedNumerator C R 0 Q.a V eta j h x y^2 = 0
      rw [hz, zero_pow (by decide : 2 ≠ 0)]
    · have hz (y : Fin 1 → Fin 3) := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
        (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 1 x hx y).2 (by omega)
      change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 1 Q.a V eta h j) x ≤ 0
      simp only [selectedRawSquareEnergy]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro y _
      change highUnionSourceMarkedNumerator C R 1 Q.a V eta j h x y^2 = 0
      rw [hz, zero_pow (by decide : 2 ≠ 0)]
    · obtain ⟨had,hab⟩ := high_source_interval_numeric C ↑M hM
      have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards C ↑M hM).1
      have hpi (i : Fin 2) : p i ∈ Icc (C.densityLower+1/↑M) (C.densityUpper-1/↑M) :=
        highUnionSourceDensity_interval C R G h (x i)
      have hUi (i : Fin 2) : U i ∈ hyperplaneCube d := highLocalCoordinates_abs_le_one d k j (x i)
      have hf (i : Fin 2) : |coefficientRegression eta g w (fun i => highFrameFeature (U i)) (c j) i| ≤ Q.ρ :=
        H.regression_abs j (c j) (H.coefficient_ball j) (x i)
      have he (y : Fin 2 → Fin 3) : highUnionSourceRawNumerator C R 2 Q.a V eta h j x y =
          finePairCountTwoRawNumerator (C.densityLower+1/↑M) (C.densityUpper-1/↑M) ell N D M q
            Cfr Q.a V eta U p g w (c j) y := by
        have hp := hpair k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf
          (((le_max_left _ _).trans (le_max_right _ _)).trans hfr) hellp hellN hcf (heta.trans ((min_le_right _ _).trans (min_le_left _ _))) V hV j h x hx y
        have hfine := finePairThreeRow_count_two_numerator hD _ _ ell N had hab hellp.le hellN.le
          D M q (by omega) hM2 hq Cfr Q.a V eta (by linarith) U hUi p hpi g w (c j) y
        change highUnionSourceRawNumerator C R 2 Q.a V eta h j x y = _ at hp
        exact hp.trans hfine.symm
      have hcap := finePairCountTwoRawNumerator_sum_square_le_geometry hD _ _ ell N had hab hellp.le hellN.le
        D M q (by omega) hM2 hq Cfr Q.a V eta Q.ρ (by linarith) Q.a_pos Q.ρ_pos.le U hUi
        p g w hpi (fun i => H.weight_abs j (x i)) (c j) hf
      change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 2 Q.a V eta h j) x ≤
        finePairCountTwoGeometryEnvelope (C.densityUpper-(M : ℝ)⁻¹) Q.a Q.ρ eta N U
      have hs : selectedRawSquareEnergy (highUnionSourceRawNumerator C R 2 Q.a V eta h j) x =
          ∑ y : Fin 2 → Fin 3, finePairCountTwoRawNumerator (C.densityLower+1/↑M)
            (C.densityUpper-1/↑M) ell N D M q Cfr Q.a V eta U p g w (c j) y^2 := by
        unfold selectedRawSquareEnergy
        apply Finset.sum_congr (by ext y; simp)
        intro y _
        rw [he]
      exact hs.trans_le (by simpa only [one_div] using hcap)
    · by_cases hnD : n+3 ≤ D
      · change selectedRawSquareEnergy (highUnionSourceRawNumerator C R (n+3) Q.a V eta h j) x ≤
          if n+3 ≤ D then completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
            M Rbound q Cfr Q.a Q.ρ eta U else (3*Chi^2)^(n+3)*eta^4*(highRowTotalMass R.rowMass+1)^2
        rw [if_pos hnD]
        exact hhigher k D M q hk0 horder hk hD (by omega) hM Cfr c0 ell N mu cf
          ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hfr) hell hellN hcf (heta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) htau hnu hFine Rbound hI V hV j h (n+3) (by omega) hnD x hx
      · change selectedRawSquareEnergy (highUnionSourceRawNumerator C R (n+3) Q.a V eta h j) x ≤
          if n+3 ≤ D then completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
            M Rbound q Cfr Q.a Q.ρ eta U else (3*Chi^2)^(n+3)*eta^4*(highRowTotalMass R.rowMass+1)^2
        rw [if_neg hnD]
        apply crude_raw_square_energy_pointwise Chi eta (highRowTotalMass R.rowMass)
        have h_highSeparatedScoreExponentialConstant_pos : 0 < highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1 := by
          exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
            (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
        · exact h_highSeparatedScoreExponentialConstant_pos.le
        · exact G.total_positive.le
        · intro z y
          exact hcrude k D M q (n+3) hk0 horder hk hD (by omega) (by omega) hM Cfr lam ell N mu cf
            ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hfr) hellp hellN hcf (heta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) V hV j h z y
  obtain ⟨Cfr0,eta0,hfr0,heta0,hcap⟩ := h_completeSource_original_all_geometry
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro Cfr cf hfr hcf Cω
  have h : (4 : ℝ)<d := by linarith only [hs,hd]
  have h' : 4<d := by exact_mod_cast h
  have h_eventually_completeSaddleSpatialSeries_le : ∀ᶠ n : ℕ in atTop,
      ∀ hk0 : NeZero (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n),
      highSourceSpatialSeries d (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n) n C.densityLower Q.c
        (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) ≤
      (3^d : ℕ)*(lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω n : ℝ)^d *
          completeSaddleEnergyBudget C Q Cfr cf Cω n := by
    filter_upwards [h_eventually_completeSaddleGeometry_factorial hcf Cfr Cω] with n hn
    intro hk0
    letI := hk0
    rw [completeSaddleSpatialSeries_eq]
    exact mul_le_mul_of_nonneg_left hn (by positivity)
  have h_sourceSaddleHigherFamily_eventually_legal (hab : C.densityLower < C.densityUpper) : let tau := densityIntervalExponent C.densityLower C.densityUpper
      let m := lowerSaddleCoefficient C.smoothness ↑d tau
      let theta := lowerSaddleTheta C.smoothness ↑d tau
      ∀ᶠ x in atTop,
        let N := lowerSaddleN C.smoothness ↑d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
        let mu := lowerSaddleMu ↑d m theta Cω x
        let ell := lowerAliasCutoff C.smoothness ↑d m theta Cω (tau+1) (shrunkDensityExponent C.densityLower C.densityUpper) x
        1 ≤ ell ∧ (∀ r : ℕ, 0 < higherBandTargetScale d r N mu) ∧
          (∀ r : ℕ, ell < higherBandTargetScale d r N mu → r ≤ (lowerSaddleM m x)) := by
    let tau := densityIntervalExponent C.densityLower C.densityUpper
    let m := lowerSaddleCoefficient C.smoothness ↑d tau
    let theta := lowerSaddleTheta C.smoothness ↑d tau
    have hτ := densityIntervalExponent_pos C.densityLower_pos hab
    obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
    have hN := lowerSaddleN_tendsto_atTop hs hd (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ) hcontrol Cω
    filter_upwards [(actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd C.densityLower_pos hab (by norm_num) (by norm_num) Cω), hN.eventually (eventually_ge_atTop ↑1), eventually_gt_atTop ↑0]
      with x hx hNx hxp
    rcases hx with ⟨hell, _, _, _, _, _, _, _, _, _, hRM, hFine⟩
    refine ⟨hell.le, ?_, ?_⟩
    · intro r
      exact mul_pos (by linarith) (Real.rpow_pos_of_pos (mul_pos (by rw [lowerSaddleMu_eq_exp hxp]; exact Real.exp_pos _) (by linarith [Real.log_nonneg hNx])) _)
    · intro r hr
      exact (hFine r hr).trans hRM
  have h_completeSourceSaddle_higher_family_eventually_legal := tendsto_natCast_atTop_atTop.eventually
      (h_sourceSaddleHigherFamily_eventually_legal (C.densityLower_lt_one.trans C.one_lt_densityUpper))
  filter_upwards [h_eventually_completeSaddleGeometry_factorial hcf Cfr Cω,
    h_eventually_completeSaddleSpatialSeries_le,
    eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
    h_completeSourceSaddle_higher_family_eventually_legal,
    tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAlias_saddle_guards hs hd
      C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω),
    tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters C hs hd hcf
      heta0 (by norm_num : (0 : ℝ)<1) Cω)] with n henergy hseries G hselection GO hphysical
  dsimp only
  let k := lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n
  let D := completeSaddleD C n
  let M := completeSaddleM C n
  let q := lowerSaddleResponseOrder C.smoothness d
  let ell := completeSaddleEll C Cω n
  let N := completeSaddleN C Cω n
  let mu := completeSaddleMu C Cω n
  let eta := completeSaddleEta C Cω cf n
  let lam := spatialInterpolationLambda d
  let Rbound := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  intro hk0 horder
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have hk : 4 ≤ k := hphysical.1
  have hD : 3 ≤ D := hphysical.2.1
  have hq : 2 ≤ q := le_max_left _ _
  have hfr1 : 1 ≤ Cfr := hfr0.trans hfr
  have GS := completeSourceRows_guards C k D M q hD (by omega) G.resolution Cfr lam ell N mu
    hfr1 (lt_of_lt_of_le zero_lt_one G.ell_one) G.ell_lt_N
  have h_completeSaddleEnergyBudget_nonneg : 0 ≤ completeSaddleEnergyBudget C Q Cfr cf Cω n := by
    unfold completeSaddleEnergyBudget lowerSaddleRawEnergyBound
    have := (completeSaddleDefectConstant_pos C Q Cfr).le
    have := (completeSaddleAliasConstant_pos C Q Cfr).le
    have := (completeSaddleFieldConstant_pos C Q Cfr).le
    have := (completeSaddleExteriorConstant_pos C Q).le
    have := lowerSaddleN_positive C.smoothness d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) n
    have : 0 ≤ lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n := by
      unfold lowerSaddleMu
      positivity [lowerSaddleH_positive d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n]
    positivity
  refine ⟨completeSaddleEnergyBudget C Q Cfr cf Cω n,h_completeSaddleEnergyBudget_nonneg,le_rfl,?_,?_,?_,?_⟩
  · intro r
    apply completeSourceGeometryEnvelope_integrable (by omega)
    · exact G.ell_one
    · exact G.ell_lt_N.le
  have h_completeSaddleGeometryEnvelope_nonneg (r : ℕ) (U : Fin r → Covariate d) : 0 ≤ completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U := completeSourceGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r U
  · exact h_completeSaddleGeometryEnvelope_nonneg
  · intro V hV h j r x hx
    have hI (t : ℕ) (ht : t ∈ ordinaryFineAliasTargetSet d D ell N mu) : 1 ≤ t ∧ t ≤ Rbound :=
      ⟨by have hh := (GO.targets t ht).1; omega,(GO.targets t ht).2⟩
    have hdom := hcap k D M q hk0 horder hk hD hq G.resolution Cfr (completeSaddleC0 C) ell N mu cf
      hfr G.ell_one G.ell_lt_N hcf.le hphysical.2.2.2.2.2.1 G.tau_le
      (fun j => hselection.2.1 (j.val+3)) (fun j => hselection.2.2 (j.val+3)) Rbound hI V hV j h r x hx
    have hmass  := GS.total_positive.le
    have h_completeSourceGeometryEnvelope_mono_total {B1 : ℝ} {B2 : ℝ} (aD) (bD) (c0) (a) (rho) (Chi) (hB1 : 0 ≤ B1) (hB : B1 ≤ B2) (n : ℕ) (U : Fin n → Covariate d) : completeSourceGeometryEnvelope D M Rbound q aD bD c0 ell N mu Cfr a rho eta Chi B1 n U ≤
        completeSourceGeometryEnvelope D M Rbound q aD bD c0 ell N mu Cfr a rho eta Chi B2 n U := by
      rcases n with _|_|_|n
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
      · change (if n+3 ≤ D then _ else (3*Chi^2)^(n+3)*eta^4*(B1+1)^2) ≤
          (if n+3 ≤ D then _ else (3*Chi^2)^(n+3)*eta^4*(B2+1)^2)
        split_ifs
        · exact le_rfl
        · have hs : (B1+1)^2 ≤ (B2+1)^2 :=
            (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)
          exact mul_le_mul_of_nonneg_left hs (by positivity)
    have hm := (h_completeSourceGeometryEnvelope_mono_total C.densityLower C.densityUpper (completeSaddleC0 C) Q.a Q.ρ (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) hmass (rowMass_le_balanced_source_activity C R hmass) r (highPatchProductChart d k j x))
    rw [completeSourceSaddle_eta_eq C Cω cf n] at hdom
    exact hdom.trans hm
  · exact hseries hk0
end
attribute [local irreducible] sourceRowData highRowTotalMass
  highUnionSourceDensity highUnionSourceState historyMarkedAppend
theorem paper_lower_sharp  (C : ModelConstants d) : LowerSharpClaim C := by
  classical
  intro hreg
  obtain ⟨hs,hd⟩ := hreg
  letI : NeZero d := NeZero.of_pos C.dimension_pos
  obtain ⟨Q⟩ := lowSmoothnessTernaryConstants_exists C
  obtain ⟨Cfr0,etaG,hCfr0,hetaG,hgeometry⟩ := completeSaddleGeometry_witness C Q hs hd
  obtain ⟨Cfr,eta0,ctr,hCfr,hmin,heta0,hctr,hcost⟩ :=
    highCompleteSource_cost_risk_uniform_above C Q Cfr0
  have h_completeSourceSaddle_numeric_constants : ∃ cf cm, 0 < cf ∧ highWindowHolderConstant C*cf ≤ C.holderBound ∧
      0 < cm ∧ cm ≤ 1/C.densityUpper := by
    let cf := C.holderBound/highWindowHolderConstant C
    refine ⟨cf,1/C.densityUpper,div_pos C.holderBound_pos (highWindowHolderConstant_pos C),?_,
      one_div_pos.mpr (lt_trans zero_lt_one C.one_lt_densityUpper),le_rfl⟩
    rw [mul_div_cancel₀ _ (highWindowHolderConstant_pos C).ne']
  obtain ⟨cf,cm,hcf,hHolder,hcm,hcmU⟩ := h_completeSourceSaddle_numeric_constants
  let q := lowerSaddleResponseOrder C.smoothness d
  let lam := spatialInterpolationLambda d
  let CB := completeSourceSaddleActivityConstant C q Cfr lam
  let C5 := completeSaddleDefectConstant C Q Cfr
  let C6 := completeSaddleAliasConstant C Q Cfr
  let C7 := completeSaddleFieldConstant C Q Cfr
  let ch := completeSaddleExteriorConstant C Q
  have h_completeSaddle_lower_rate_of_actual_cost_budget (hcost : ∀ Cω, ∀ᶠ n : ℕ in atTop,
      CompleteSaddleCostRiskBudget C cf CB C5 C6 C7 ch ctr cm Cω n) : ∃ c, 0 < c ∧ ∃ n₀, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) n, n₀ ≤ n →
        ENNReal.ofReal (c*paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n := by
    have h_completeSourceSaddleActivityConstant_pos : 0 < completeSourceSaddleActivityConstant C q Cfr lam := by
      exact div_pos (sourceSaddleActivityConstant_positive d q _ _ _ _ C.densityLower_pos
        (C.densityLower_lt_one.trans C.one_lt_densityUpper)) (highCenterMix_mem C).1
    have hCB : 0 ≤ CB := h_completeSourceSaddleActivityConstant_pos.le
    have hC5 : 0 ≤ C5 := (completeSaddleDefectConstant_pos C Q Cfr).le
    have hC6 : 0 ≤ C6 := (completeSaddleAliasConstant_pos C Q Cfr).le
    have hC7 : 0 ≤ C7 := ((completeSaddleFieldConstant_pos C Q Cfr).le)
    have hch : 0 ≤ ch := ((completeSaddleExteriorConstant_pos C Q).le)
    let Cω := 1+Real.log (rawCostConstant CB C5 C6 C7 cf ch)+
      (d^2-16*C.smoothness)/(d*(d+4))*highCompleteSourceSaddleTheta C+
      2*d*densityIntervalExponent C.densityLower C.densityUpper/(d+4)+1
    obtain ⟨c,hc,hrate⟩ := completeSourceSaddle_penalized_numeric_envelope C hs hd
      hcf hCB hC5 hC6 hC7 hch hctr hcm (Cω := Cω) (by dsimp only [Cω]; linarith)
    have hall : ∀ᶠ n : ℕ in atTop,
        2 ≤ n ∧ ∀ U,
          ENNReal.ofReal (c*paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n := by
      filter_upwards [hcost Cω,hrate,eventually_ge_atTop 2] with n hcostn hraten hn
      rcases hcostn with ⟨Bl,E,hB,hBl,hE,hBlcap,hEcap,hrisk⟩
      refine ⟨hn,fun U => ?_⟩
      apply minimaxRMS_lower_of_squared_lower (C.withDomain U)
        (mul_pos hc (paperRiskScale_pos C hn)).le
      exact (ENNReal.ofReal_le_ofReal (hraten Bl E hB hBl hE hBlcap hEcap)).trans (hrisk U)
    obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hall
    exact ⟨c,hc,n₀,(hn₀ n₀ le_rfl).1,fun U n hn => (hn₀ n hn).2 U⟩
  apply h_completeSaddle_lower_rate_of_actual_cost_budget
  intro Cω
  have h_completeSourceSaddleActivity_eventually_bound : ∀ᶠ x : ℝ in atTop,
      completeSourceSaddleActivity C q Cfr lam Cω x ≤
        completeSourceSaddleActivityConstant C q Cfr lam *
          lowerSaddleActivity C.smoothness d (highCompleteSourceSaddleCoefficient C)
            (highCompleteSourceSaddleTheta C) Cω
              (shrunkDensityExponent C.densityLower C.densityUpper) x := by
    have h_sourceSaddleTotalMass_eventually_bound : ∀ᶠ x in atTop, ∀ k,
        sourceSaddleTotalMass d k q C.smoothness C.densityLower C.densityUpper Cfr lam Cω x ≤
          sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam *
            (lowerSaddleN C.smoothness d (lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper))
              (lowerSaddleTheta C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x)^2 *
            Real.exp (shrunkDensityExponent C.densityLower C.densityUpper (lowerSaddleM (lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)) x)*
              (lowerSaddleM (lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)) x : ℝ)) := by
      have hab : C.densityLower < C.densityUpper := (C.densityLower_lt_one.trans C.one_lt_densityUpper)
      let tau := densityIntervalExponent C.densityLower C.densityUpper
      let c0 := tau+1
      let m := lowerSaddleCoefficient C.smoothness d tau
      let theta := lowerSaddleTheta C.smoothness d tau
      have hτ : 0 < tau := densityIntervalExponent_pos C.densityLower_pos hab
      have hc0 : 1 ≤ c0 := by dsimp [c0]; linarith
      have hm : 0 < m := lowerSaddleCoefficient_pos hs hd hτ
      have htheta : 0 < theta := lowerSaddleTheta_pos hs hd hτ
      have hdR : (0 : ℝ) < d := by linarith
      have hdNat : 0 < d := by exact_mod_cast hdR
      obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
      have hB : 0 < uniformOrdinaryDensityActivityBase C.densityLower C.densityUpper c0 :=
        mul_pos (Real.exp_pos _) (div_pos (sub_pos.mpr hab) C.densityLower_pos)
      have hhier := actual_lowerAlias_hierarchy (Cact := higherBandSourceCact d C.densityLower C.densityUpper c0 lam)
        (Cs := 1) hs hd C.densityLower_pos hab (by unfold higherBandSourceCact higherBandGeometricConstant higherBandInterpolationBase; positivity) (by norm_num) Cω
      have hM := lowerSaddleM_tendsto_atTop hm
      have hN := lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol Cω
      filter_upwards [hhier, (hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : 0 < (C.densityUpper-C.densityLower)/2))), hM.eventually (eventually_ge_atTop 1),
        hN.eventually (eventually_ge_atTop 1), eventually_gt_atTop 0] with x hx hsh hMx hNx hxp
      intro k
      let M := lowerSaddleM m x
      let D := lowerSaddleD d m x
      let N := lowerSaddleN C.smoothness d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
      let mu := lowerSaddleMu d m theta Cω x
      change LowerAliasHierarchy C.smoothness d m theta Cω (higherBandSourceCact d C.densityLower C.densityUpper c0 lam) 1 c0
        (shrunkDensityExponent C.densityLower C.densityUpper) x at hx
      rcases hx with ⟨hell, htau, hbase, _, _, hq21, hq1, hDq, _, hsingle, _, _⟩
      have hD : 1 ≤ D := by
        have : ((d : ℝ)+8)/4*(M : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
        have hh : (1 : ℝ) ≤ D := by change (1 : ℝ) ≤ lowerSaddleD (d : ℝ) m x; change (1 : ℝ) ≤ M at hMx; nlinarith
        exact_mod_cast hh
      have he : Real.exp (c0*D) ≤ Real.exp (c0*(D+1)) := Real.exp_le_exp.mpr (by nlinarith)
      have hh := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg D)
      have h_sourceRows_shrunk_activity_bound (a : ℝ) (b : ℝ) (q1 : ℝ) (q2 : ℝ) (ha : 0 < a) (hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹) (htau : shrunkDensityExponent a b M ≤ c0) (hμ : 0 ≤ mu) (hDN : (D : ℝ)*Real.exp (c0*(D : ℝ)) ≤ N) (hq1 : q1 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam) (1+Real.log N) (mu*(1+Real.log N)) 1) (hq2 : q2 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam) (1+Real.log N) (mu*(1+Real.log N)) 2) (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1) : highRowTotalMass (sourceRowData d k D M q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) Cfr lam
          (N*Real.exp (-c0*(D : ℝ))) N mu).rowMass ≤
          sourceActivityConstant d q Cfr (uniformOrdinaryDensityActivityBase a b c0) lam *
            N^2 * Real.exp (shrunkDensityExponent a b M*(M : ℝ)) := by
        have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
        have hap : 0 < a+(M : ℝ)⁻¹ := by linarith
        have hab : a < b := by linarith
        have hc00 : 0 ≤ c0 := by linarith
        have hd0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
        have hN0 : 0 ≤ N := by linarith
        have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b c0 := by
          exact mul_nonneg (Real.exp_pos _).le (div_nonneg (sub_pos.mpr hab).le ha.le)
        have hbB := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
        have he : exteriorTau (((a+(M : ℝ)⁻¹)+(b-(M : ℝ)⁻¹))/((b-(M : ℝ)⁻¹)-(a+(M : ℝ)⁻¹))) =
            shrunkDensityExponent a b M := by
          rw [exteriorTau_sqrt_ratio _ _ hap hshrink]
          rfl
        have hℓ : 0 ≤ N*Real.exp (-c0*(D : ℝ)) := by positivity
        have hh : Real.exp (-c0*(D : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have hsingle : (D : ℝ)*Real.exp ((D : ℝ)*shrunkDensityExponent a b M) ≤ N := by
          apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith :
            (D : ℝ)*shrunkDensityExponent a b M ≤ c0*(D : ℝ))) hd0).trans hDN
        have hpair := source_pair_coarse_scale_le (D := (D : ℝ)) (N := N) hd0 hc0 htau
        have hcoarse : Real.exp ((D : ℝ)*shrunkDensityExponent a b M)*(N*Real.exp (-c0*(D : ℝ))) ≤ N := by
          have hh  :=
            Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htau) hd0)
          have h := mul_le_mul_of_nonneg_left hh hN0
          calc
            _ = N*Real.exp (((shrunkDensityExponent a b M)-c0)*(D : ℝ)) := by
              rw [sub_mul, Real.exp_sub, show -c0*(D : ℝ) = -(c0*(D : ℝ)) by ring, Real.exp_neg,
                mul_comm (D : ℝ) (shrunkDensityExponent a b M)]
              ring
            _ ≤ N := by simpa only [mul_one] using h
        have hh := sourceRows_activity_bound (k := k) (M := M) (q := q) hdNat hD
          (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) Cfr lam (N*Real.exp (-c0*(D : ℝ))) N mu
          (uniformOrdinaryDensityActivityBase a b c0) q1 q2 hap hshrink hℓ (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hN0) hNx hμ hbase hB hbB
          hq1 hq2 hq1h hq21 hsmall (by simpa only [he] using hcoarse)
          (by simpa only [he] using hsingle)
          (by simpa only [he, mul_comm (D : ℝ) (shrunkDensityExponent a b M)] using hpair)
        simpa only [he, mul_comm (M : ℝ) (shrunkDensityExponent a b M)] using hh
      have hb := (h_sourceRows_shrunk_activity_bound C.densityLower C.densityUpper (lowerAliasQ C.smoothness d m theta Cω (higherBandSourceCact d C.densityLower C.densityUpper c0 lam) 1 (shrunkDensityExponent C.densityLower C.densityUpper) x) (lowerAliasQ C.smoothness d m theta Cω (higherBandSourceCact d C.densityLower C.densityUpper c0 lam) 2 (shrunkDensityExponent C.densityLower C.densityUpper) x) C.densityLower_pos (by change (M : ℝ)⁻¹ < (C.densityUpper-C.densityLower)/2 at hsh; linarith) htau (by dsimp [mu]; rw [lowerSaddleMu_eq_exp hxp]; exact (Real.exp_pos _).le) (by apply hh.trans; simpa only [one_mul] using hsingle) rfl rfl hq1 hq21 hDq)
      apply hb.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by unfold sourceSaddleActivityConstant; dsimp [c0, tau]; linarith) (sq_nonneg N)) (Real.exp_pos _).le
    filter_upwards [h_sourceSaddleTotalMass_eventually_bound] with x hx
    let m := highCompleteSourceSaddleCoefficient C
    let theta := highCompleteSourceSaddleTheta C
    let M := lowerSaddleM m x
    let D := lowerSaddleD d m x
    let k := lowerSaddleGrid d m theta Cω x
    let N := lowerSaddleN C.smoothness d m theta Cω
      (shrunkDensityExponent C.densityLower C.densityUpper) x
    let ell := lowerAliasCutoff C.smoothness d m theta Cω
      (densityIntervalExponent C.densityLower C.densityUpper+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x
    let mu := lowerSaddleMu d m theta Cω x
    have hmass : highRowTotalMass (completeSourceSaddleRows C q Cfr lam Cω x).rowMass =
        sourceSaddleTotalMass d k q C.smoothness C.densityLower C.densityUpper Cfr lam Cω x := by
      dsimp only [completeSourceSaddleRows,completeSourceRows,sourceSaddleTotalMass,
        m,theta,M,D,k,N,ell,mu,highCompleteSourceSaddleCoefficient,highCompleteSourceSaddleTheta]
      let F : ℝ×ℝ → ℝ := fun z =>
        highRowTotalMass (sourceRowData d k D M q z.1 z.2 Cfr lam ell N mu).rowMass
      let z1 : ℝ×ℝ := (C.densityLower+1/(M:ℝ),C.densityUpper-1/(M:ℝ))
      let z2 : ℝ×ℝ := (C.densityLower+(M:ℝ)⁻¹,C.densityUpper-(M:ℝ)⁻¹)
      have hz : z1=z2 := by dsimp only [z1,z2]; simp only [one_div]
      have h : F z1=F z2 := @congrArg (ℝ×ℝ) ℝ z1 z2 F hz
      exact h
    have h := div_le_div_of_nonneg_right (hmass.trans_le (hx k)) (highCenterMix_mem C).1.le
    change completeSourceSaddleActivity C q Cfr lam Cω x ≤ _ at h
    apply h.trans_eq
    dsimp only [completeSourceSaddleActivityConstant,lowerSaddleActivity,
      highCompleteSourceSaddleCoefficient,highCompleteSourceSaddleTheta]
    ring
  filter_upwards [hgeometry Cfr cf hmin hcf Cω,
    tendsto_natCast_atTop_atTop.eventually
      (eventually_completeSourceSaddle_parameters C hs hd hcf heta0 hcm Cω),
    tendsto_natCast_atTop_atTop.eventually
      h_completeSourceSaddleActivity_eventually_bound] with n hgeo hp hactivity
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let k := lowerSaddleGrid d m theta Cω n
  let M := completeSaddleM C n
  let D := completeSaddleD C n
  let N := completeSaddleN C Cω n
  let ell := completeSaddleEll C Cω n
  let mu := completeSaddleMu C Cω n
  let eta := cf*k^(-C.smoothness)
  dsimp only at hp hgeo
  obtain ⟨hk,hD,hM,hell,hellN,heta,heps,hB⟩ := hp
  have hk' : 4 ≤ k := hk
  have hD' : 3 ≤ D := hD
  have hM' : highCenterResolutionThreshold C ≤ M := hM
  letI : NeZero k := ⟨by omega⟩
  letI : LinearOrder (HighWindowLabels d k) :=
    LinearOrder.lift' (Fintype.equivFin (HighWindowLabels d k))
      (Fintype.equivFin (HighWindowLabels d k)).injective
  obtain ⟨E,hE,hEcap,hHI,hH0,hdom,hseries⟩ := hgeo inferInstance inferInstance
  have hq : 1 ≤ q := by dsimp only [q,lowerSaddleResponseOrder]; omega
  have G := completeSourceRows_guards C k D M q hD' hq hM' Cfr lam ell N mu hCfr hell hellN
  let Bl := highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass/highCenterMix C
  have hBl : 0 ≤ Bl := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hactivity' : Bl ≤ CB*lowerSaddleActivity C.smoothness d m theta Cω
      (shrunkDensityExponent C.densityLower C.densityUpper) n := hactivity
  change CompleteSaddleCostRiskBudget C cf CB C5 C6 C7 ch ctr cm Cω n
  dsimp only [CompleteSaddleCostRiskBudget]
  refine ⟨Bl,E,hB,hBl,hE,hactivity',hEcap,?_⟩
  intro U
  let delta := localScorePathLength (highPathConstant (3^d) Q.ρ eta0) Bl (Real.sqrt ((3^d : ℕ)*k^d*E))
  have heta0' : 0 ≤ eta := mul_nonneg hcf.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hvariance : eta^2*delta ≤ Q.ρ := highPath_variance_budget (3^d) Q.ρ_pos heta0 hBl
    (Real.sqrt_nonneg _) heta0' heta
  have hV (t : ℝ) (ht : t ∈ Icc 0 delta) : |(Q.v-eta^2*t)-Q.v| ≤ Q.ρ := by
    simp only [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg eta),abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hvariance
  have hetaEq : eta = completeSaddleEta C Cω cf n := completeSourceSaddle_eta_eq C Cω cf n
  have hout := hcost U k D M q inferInstance inferInstance hk' hD' hq hM' lam ell N mu hell hellN
    cf hcf.le hHolder heta cm hcm.le hcmU n E hE heps
    (fun _t _h _j r => completeSaddleGeometryEnvelope C Q Cfr cf Cω n r)
    (fun _t _ht _h _j r => hHI r)
    (fun _t _ht _h _j r u => hH0 r u)
    (fun t ht h j r x hx => by
      simpa only [← hetaEq] using hdom (Q.v-eta^2*t) (hV t ht) h j r x hx)
    (fun _t _ht _h => hseries)
  have htail : 2*Real.exp (-(cm/M)^2/
      (8*highHistoryMassParameter d k C.densityLower C.densityUpper)) =
      highCompleteSourceSaddleTail C Cω cm n :=
    (by rw [highHistoryMassParameter_lowerSaddle]; congr 1; congr 1; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  simpa only [htail] using hout
end NearlyMinimax
