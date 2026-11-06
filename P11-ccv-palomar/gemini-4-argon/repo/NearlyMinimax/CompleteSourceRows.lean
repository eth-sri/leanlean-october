module
public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.FinePairRowAnnihilation
public import NearlyMinimax.FinePairRowSource
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
open MvPolynomial
open scoped BigOperators
variable {κ : Type*} {d F : ℕ}
theorem finePairCoordinatePolynomial_monomial  (l : Fin d) :
    finePairCoordinatePolynomial l = monomial (Finsupp.single l 1) 8 := C_mul_X_eq_monomial
theorem finePairCoordinateCoefficients_l1_le  (l : Fin d) :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairCoordinatePolynomial l) β|) ≤ 8 := by
  apply (highFrameCoefficients_sum_abs_le _).trans
  rw [finePairCoordinatePolynomial_monomial]
  simp [frameCoefficientL1, MvPolynomial.support_monomial]
theorem finePairUnitCoefficients_l1_le (d F ) :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β|) ≤ 1 :=
  (highFrameCoefficients_sum_abs_le _).trans_eq frameCoefficientL1_one
theorem spatial_matrix_l1_outer  (u v : HighFrameIndex d F → ℝ) :
    spatialMatrixL1 (fun β β' => u β * v β') =
      (∑ β, |u β|) * (∑ β, |v β|) := by
  simp only [spatialMatrixL1, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
theorem finePairUnitMatrix_l1_le (d F : ℕ) :
    spatialMatrixL1 (finePairUnitMatrix d F) ≤ 1 := by
  unfold finePairUnitMatrix
  rw [spatial_matrix_l1_outer]
  simpa only [one_mul] using mul_le_mul (finePairUnitCoefficients_l1_le d F)
    (finePairUnitCoefficients_l1_le d F) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1)
def finePairMatrixEntryCost  [Fintype κ] (A : κ → κ → ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|
theorem fine_pair_entry_cost_outer  [Fintype κ] (u v : κ → ℝ) :
    finePairMatrixEntryCost (fun i j => u i * v j) = (∑ i, |u i|) * (∑ j, |v j|) := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
theorem fine_pair_entry_cost_sub_le  [Fintype κ] (A B : κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => A i j - B i j) ≤ finePairMatrixEntryCost A + finePairMatrixEntryCost B := by
  simp only [finePairMatrixEntryCost, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => abs_sub _ _))
theorem fine_pair_entry_cost_sum_le  [Fintype κ] [Fintype I]
    (A : I → κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => ∑ l, A l i j) ≤ ∑ l, finePairMatrixEntryCost (A l) := by
  unfold finePairMatrixEntryCost
  apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => Finset.abs_sum_le_sum_abs _ _))).trans_eq
  simp_rw [Finset.sum_comm (f := fun j l => |A l _ j|)]
  rw [Finset.sum_comm]
private theorem fine_pair_entry_cost_scalar  [Fintype κ] (t : ℝ) (A : κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => t * A i j) = |t| * finePairMatrixEntryCost A := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum]
theorem finite_quadratic_matrix_cost  [Fintype κ] (d )
    (c0 cs : κ → ℝ) (cl : Fin d → κ → ℝ)
    (h0 : (∑ β, |c0 β|) ≤ 1) (hs : (∑ β, |cs β|) ≤ 64 * d)
    (hl : ∀ l, (∑ β, |cl l β|) ≤ 8) :
    finePairMatrixEntryCost (fun β β' => (∑ l, 2 * cl l β * cl l β') -
      cs β * c0 β' - c0 β * cs β') ≤ 256 * d := by
  let B (β β' : κ) : ℝ := ∑ l, 2 * cl l β * cl l β'
  have houterS : finePairMatrixEntryCost (fun β β' => cs β * c0 β') ≤ 64 * d := by
    rw [fine_pair_entry_cost_outer]
    exact (mul_le_mul hs h0
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)).trans_eq (mul_one _)
  have houterS' : finePairMatrixEntryCost (fun β β' => c0 β * cs β') ≤ 64 * d := by
    rw [fine_pair_entry_cost_outer, mul_comm]
    exact (mul_le_mul hs h0
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)).trans_eq (mul_one _)
  have hB : finePairMatrixEntryCost B ≤ 128 * d := by
    apply (fine_pair_entry_cost_sum_le (fun l β β' => 2 * cl l β * cl l β')).trans
    calc
      _ ≤ ∑ _l : Fin d, ↑128 := by
        apply Finset.sum_le_sum
        intro l _
        have he : (fun β β' : κ => 2 * cl l β * cl l β') =
            (fun β β' => 2 * (cl l β * cl l β')) := by funext β β'; ring
        rw [he, fine_pair_entry_cost_scalar, fine_pair_entry_cost_outer]
        have hh := mul_le_mul (hl l) (hl l)
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 8)
        exact (mul_le_mul_of_nonneg_left hh (abs_nonneg (2 : ℝ))).trans_eq (by norm_num)
      _ = _ := by simp; ring
  change finePairMatrixEntryCost (fun β β' => B β β' - cs β * c0 β' - c0 β * cs β') ≤ _
  have hsub'  :=
    fine_pair_entry_cost_sub_le (fun β β' => B β β' - cs β * c0 β')
      (fun β β' => c0 β * cs β')
  have hh  :=
    (hsub'.trans (add_le_add (fine_pair_entry_cost_sub_le B (fun β β' => cs β * c0 β')) (le_refl _))).trans
      (add_le_add (add_le_add hB houterS) houterS')
  exact hh.trans_eq (by ring)
theorem spatial_matrix_l1_quadratic_three_le (d F )
    (c0 cs : HighFrameIndex d F → ℝ) (cl : Fin d → HighFrameIndex d F → ℝ)
    (h0 : (∑ β, |c0 β|) ≤ 1) (hs : (∑ β, |cs β|) ≤ 64 * d)
    (hl : ∀ l, (∑ β, |cl l β|) ≤ 8) :
    spatialMatrixL1 (fun β β' => (∑ l, 2 * cl l β * cl l β') -
      cs β * c0 β' - c0 β * cs β') ≤ 256 * d :=
  finite_quadratic_matrix_cost d c0 cs cl h0 hs hl
theorem finePairDistanceMatrix_l1_le (d F : ℕ) :
    spatialMatrixL1 (finePairDistanceMatrix d F) ≤ 256 * d :=
  have h_finePairSquareCoefficients_l1_le : (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairSquarePolynomial d) β|) ≤ 64 * d := by
    apply (highFrameCoefficients_sum_abs_le _).trans
    have h_finePairSquarePolynomial_monomial_sum : finePairSquarePolynomial d = ∑ l : Fin d,
        monomial (Finsupp.single l 1 + Finsupp.single l 1) ↑64 := by
      unfold finePairSquarePolynomial
      simp only [finePairCoordinatePolynomial_monomial, pow_two, monomial_mul]
      norm_num
    rw [h_finePairSquarePolynomial_monomial_sum]
    apply (frameCoefficientL1_sum_monomial_le _ _).trans_eq
    simp only [show |(64 : ℝ)| = 64 by norm_num, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  spatial_matrix_l1_quadratic_three_le d F _ _ _
    (finePairUnitCoefficients_l1_le d F) h_finePairSquareCoefficients_l1_le
    (fun l => finePairCoordinateCoefficients_l1_le l)
end
abbrev SingletonRowMark (d D q : ℕ) := Unit × HighPacketMarkIndex (HighFrameIndex d D) D 1 D q
def singletonRowMass (d D q : ℕ) (a b C : ℝ) : ℝ :=
  highPacketMarkMass (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
def singletonRowData (d k D q ) (a b C : ℝ) :
    HighUnionRowData d k D Unit (fun _ => SingletonRowMark d D q) where
  rowLaw := fun _ => highPacketAbsoluteLaw (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
  rowMass := fun _ => singletonRowMass d D q a b C
  rowActivation := fun _ => highPacketActivation (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
  rowIntercept := fun _ => highPacketIntercept a b D 1 D q
  rowSlope := fun _ _ e _ => highPacketSlope a b D 1 D q (fun _ _ => 1) e
  rowVector := fun _ e => (highResponseMarkAtom C q e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 q e.2.2).1
theorem singletonRowMass_positive (d D q ) (hq : 1 ≤ q)
    (a b ) (ha : 0 < a) (hab : a < b) (C ) (hC : 0 < C) :
    0 < singletonRowMass d D q a b C := by
  rw [singletonRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)]
  simp only [separatedMatrixCost, integral_dirac]
  rw [densityPacketWeight_variation a b ha hab D 1 D (by norm_num)]
  exact mul_pos (mul_pos (mul_pos
    (mul_pos (mul_pos (abs_pos.mpr (by simp only [densityPacketPrefactor, Nat.factorial_one, Nat.cast_one, one_div, inv_one, pow_one, one_mul]; exact div_ne_zero (ha.trans hab).ne' (densityMargin_zero_ne a b ha hab))) (Real.cosh_pos _)) (pow_pos (by exact_mod_cast (by unfold derivativeOrder; omega)) _)) (lt_of_lt_of_le zero_lt_one (response_absolute_cost_ge_one q hq)))
      (mul_pos (by norm_num) (pow_pos hC _))) (finePairUnitMatrix_l1_pos d D)
def highUnionRowRestrict {d k D : ℕ} {I : Type*} {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (R : HighUnionRowData d k D I E) (i : I) : HighUnionRowData d k D Unit (fun _ => E i) where
  rowLaw := fun _ => R.rowLaw i
  rowMass := fun _ => R.rowMass i
  rowActivation := fun _ => R.rowActivation i
  rowIntercept := fun _ => R.rowIntercept i
  rowSlope := fun j _ => R.rowSlope j i
  rowVector := fun _ => R.rowVector i
  rowTime := fun _ => R.rowTime i
abbrev SourceRowIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  FinePairRowTag ⊕ (Unit ⊕ HigherBandFamilyIndex d D M q a b C lam ℓ N μ)
def SourceRowMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowMark d D M q p
  | .inr (.inl _) => SingletonRowMark d D q
  | .inr (.inr i) => HigherBandFamilyMark d D M q a b C lam ℓ N μ i
instance sourceRowMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : MeasurableSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_measurable d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark] <;> infer_instance
instance sourceRowMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : StandardBorelSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_standardBorel d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark, sourceRowMark_measurable] <;> infer_instance
def sourceRowComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      HighUnionRowData d k D Unit (fun _ => SourceRowMark d D M q a b C lam ℓ N μ i)
  | .inl p => highUnionRowRestrict (finePairRowData d k D M q a b C ℓ N) p
  | .inr (.inl _) => singletonRowData d k D q a b C
  | .inr (.inr i) => higherBandFamilyComponent d k D M q a b C lam ℓ N μ i
def sourceRowData (d k D M q a b C lam ℓ N μ) :
    HighUnionRowData d k D (SourceRowIndex d D M q a b C lam ℓ N μ)
      (SourceRowMark d D M q a b C lam ℓ N μ) where
  rowLaw := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowLaw ()
  rowMass := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowMass ()
  rowActivation := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowActivation ()
  rowIntercept := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowIntercept ()
  rowSlope := fun j i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowSlope j ()
  rowVector := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowVector ()
  rowTime := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowTime ()
theorem highPacketSlope_joint_measurable_general {Z : Type*} [MeasurableSpace Z]
    (d m r D q : ℕ) (a b : ℝ) (B : Z → Covariate d → Fin r → ℝ)
    (hB : ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)) :
    Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      highPacketSlope a b m r D q (fun ζ l => B ζ ex.2 l) ex.1) := by
  have hc : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      densityMargin a b (densityPacketAtom a b m r D ex.1.2.1).1 / (↑r*b)) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      densityMargin a b (densityPacketAtom a b m r D h.1).1 / (↑r*b))).comp
        (measurable_snd.comp measurable_fst)
  have he (l : Fin r) : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) m r D q) × Covariate d =>
      (densityPacketAtom a b m r D ex.1.2.1).2 l) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      (densityPacketAtom a b m r D h.1).2 l)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (Finset.measurable_fun_sum _ (fun l _ => (he l).mul
    ((hB l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))
def higherBandSourceRow  (C : ModelConstants d) (k r m D q )
    (M Cfr lam L T : ℝ) (fine ) :
    HighUnionRowData d k D Unit (fun _ => HigherBandRowMark d r m D q fine) :=
  higherBandRowData d k r m D q (C.densityLower+1/M) (C.densityUpper-1/M) Cfr lam L T fine
theorem higherBandSourceRow_guards {d : ℕ} (C : ModelConstants d)
    (k r m D q ) (hr : 1 ≤ r) (M Cfr lam L T fine)
    (hM : highCenterResolutionThreshold C ≤ M) (hCfr : 1 ≤ Cfr) (hT : 1 ≤ T)
    (hpos : 0 < higherBandRowMass d r m D q (C.densityLower+1/M)
      (C.densityUpper-1/M) Cfr lam L T fine) :
    HighUnionSourceGuards C M Cfr (higherBandSourceRow C k r m D q M Cfr lam L T fine) := by
  let a := C.densityLower+1/M
  let b := C.densityUpper-1/M
  let σ := higherBandCarrierMeasure d r L T fine
  let A := higherBandCarrierAmplitude d r D lam fine
  let B := fun (j : HighWindowLabels d k) ζ (x : Covariate d) l =>
    higherBandCarrierFactor d r lam fine ζ l (highLocalCoordinates d k j x)
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  have hA := higherBandCarrierAmplitude_measurable d r D lam fine
  have hc := higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine
  have hg := highCenterResolution_guards C M hM
  have hM0 : 0 < M := by linarith [hg.1]
  have ha : 0 < a := by dsimp [a]; linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  have hab : a < b := by
    dsimp [a,b]
    linarith [hg.2,highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]
  have hB (j) (l : Fin r) : Measurable (fun ζx : HigherBandCarrier d r fine × Covariate d =>
      B j ζx.1 ζx.2 l) :=
    (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  have hBb (j) (ζ : HigherBandCarrier d r fine) (x : Covariate d) (l : Fin r) : |B j ζ x l| ≤ 1 :=
    higherBandCarrierFactor_bound d r lam fine ζ l _ (fun i =>
      (highLocalCoordinates_abs_le_one d k j x i).trans (by norm_num))
  have hBm (j) (x : Covariate d) (l : Fin r) : Measurable (fun ζ => B j ζ x l) :=
    (hB j l).comp (measurable_id.prodMk measurable_const)
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => (highPacketAbsoluteLaw_probability σ a b m r D q Cfr A hA hc hpos)
    mass_nonneg := fun _ => hpos.le
    total_positive := ?_
    activation_measurable := ?_
    activation_bound := fun _ => higherBandRowActivation_bound d r m D q a b Cfr lam L T fine
    activation_centered := fun _ => highPacketActivation_centered σ a b m r D q Cfr A hA hc hpos
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := fun _ => highPacketIntercept_measurable a b m r D q
    intercept_interval := ?_
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := ?_
    time_interval := ?_ }
  · simpa [highRowTotalMass,higherBandSourceRow,higherBandRowData] using hpos
  · intro i
    exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b m r D q Cfr A hA)
  · intro j i
    exact highPacketSlope_joint_measurable_general d m r D q a b (fun ζ x l => B j ζ x l) (hB j)
  · intro j x i
    exact highPacketSlope_integrable σ a b ha hab m r D q hr Cfr A hA hc hpos
      (fun ζ l => B j ζ x l) (hBm j x) (fun ζ l => hBb j ζ x l)
  · intro j x i
    exact highPacketAbsoluteLaw_slope_integral_zero σ a b ha hab m r D q hr Cfr A hA hc hpos
      (fun ζ l => B j ζ x l) (hBm j x) (fun ζ l => hBb j ζ x l)
  · intro i e
    exact (densityPacketAtom_mem a b hab.le m r D e.2.1).1
  · intro j i e x v hv
    have hh := localDensityReset_mem_interval a b ha hab r hr
      (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom_mem a b hab.le m r D e.2.1).1
      (densityPacketAtom a b m r D e.2.1).2 (densityPacketAtom_mem a b hab.le m r D e.2.1).2
      (fun _ => v) (fun _ l => B j e.1 x l) () hv (fun l => hBb j e.1 x l)
    convert hh using 1 <;>
      dsimp [higherBandSourceRow,higherBandRowData,highPacketSlope,highPacketIntercept,localDensityReset] <;> ring
  · intro i γ
    exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      (highResponseMarkAtom Cfr q h.2).2 γ)).comp measurable_snd
  · intro i
    exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
      (highResponseMarkAtom (ι := HighFrameIndex d D) 0 q h.2).1)).comp measurable_snd
  · intro i e
    exact covarianceAtom_mem_ball Cfr (by linarith) _ _ _ _
  · intro i e
    exact responseNode_mem_unit q _
theorem high_source_interval_numeric  (C : ModelConstants d) (M )
    (hM : highCenterResolutionThreshold C ≤ M) :
    0 < C.densityLower+1/M ∧ C.densityLower+1/M < C.densityUpper-1/M := by
  have hg := highCenterResolution_guards C M hM
  have hM0 : 0 < M := by linarith [hg.1]
  constructor
  · linarith [C.densityLower_pos,one_div_pos.mpr hM0]
  · linarith [hg.2,highCenterRadius_pos C,(highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]
def completeSourceRows {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (Cfr lam ℓ N μ : ℝ) :=
  sourceRowData d k D M q (C.densityLower+1/M)
    (C.densityUpper-1/M) Cfr lam ℓ N μ
theorem HighUnionSourceGuards.restrict   [Fintype I] 
    [∀ i, MeasurableSpace (E i)]  {M Cfr : ℝ}
    {R : HighUnionRowData d k F I E} (G : HighUnionSourceGuards C M Cfr R)
    (i ) (hpos : 0 < R.rowMass i) :
    HighUnionSourceGuards C M Cfr (highUnionRowRestrict R i) where
  resolution := G.resolution
  frame := G.frame
  row_probability := fun _ => G.row_probability i
  mass_nonneg := fun _ => G.mass_nonneg i
  total_positive := by simpa [highRowTotalMass,highUnionRowRestrict] using hpos
  activation_measurable := fun _ => G.activation_measurable i
  activation_bound := fun _ => G.activation_bound i
  activation_centered := fun _ => G.activation_centered i
  slope_measurable := fun j _ => G.slope_measurable j i
  slope_integrable := fun j x _ => G.slope_integrable j x i
  slope_centered := fun j x _ => G.slope_centered j x i
  intercept_measurable := fun _ => G.intercept_measurable i
  intercept_interval := fun _ => G.intercept_interval i
  row_reset_interval := fun j _ => G.row_reset_interval j i
  vector_measurable := fun _ => G.vector_measurable i
  time_measurable := fun _ => G.time_measurable i
  vector_ball := fun _ => G.vector_ball i
  time_interval := fun _ => G.time_interval i
theorem completeSourceRows_guards  (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N) :
    HighUnionSourceGuards C ↑M Cfr (completeSourceRows C k D M q Cfr lam ℓ N μ) := by
  let a := C.densityLower+1/↑M
  let b := C.densityUpper-1/M
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C ↑M hM
  have hCf : 0 < Cfr := by linarith
  have hcomp (i : SourceRowIndex d D M q a b Cfr lam ℓ N μ) :
      HighUnionSourceGuards C ↑M Cfr (sourceRowComponent d k D M q a b Cfr lam ℓ N μ i) := by
    cases i with
    | inl p =>
      exact (finePairSourceRows_guards C k D M q hD hq hM Cfr hCfr ℓ N hℓ hℓN).restrict p
        (finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf ℓ N hℓ hℓN p)
    | inr i =>
      have h_singletonRowSource_guards : HighUnionSourceGuards C M Cfr
          (singletonRowData d k D q (C.densityLower+1/M) (C.densityUpper-1/M) Cfr) := by
        let a := C.densityLower+1/M
        let b := C.densityUpper-1/M
        obtain ⟨ha,hab⟩ := high_source_interval_numeric C M hM
        have hCf : 0 < Cfr := by linarith
        have hpos := singletonRowMass_positive d D q hq a b ha hab Cfr hCf
        let A := fun _ : Unit => finePairUnitMatrix d D
        have hA : ∀ i j, Measurable (fun ζ => A ζ i j) := fun _ _ => measurable_const
        have hc : Integrable (separatedMatrixCost A) (Measure.dirac ()) := by
          simp [A]
        have h_singletonRow_probability  := highPacketAbsoluteLaw_probability (Measure.dirac ()) a b D 1 D q Cfr (fun _ => finePairUnitMatrix d D)
          (fun _ _ => measurable_const) (integrable_const _) (singletonRowMass_positive d D q hq a b ha hab Cfr hCf)
        refine {
          resolution := hM
          frame := hCfr
          row_probability := fun _ => h_singletonRow_probability
          mass_nonneg := fun _ => hpos.le
          total_positive := ?_
          activation_measurable := fun _ => absoluteActivation_measurable _ _
            (highPacketMarkWeight_measurable a b D 1 D q Cfr A hA)
          activation_bound := fun _ => highPacketActivation_bound (Measure.dirac ()) a b D 1 D q Cfr A
          activation_centered := fun _ => highPacketActivation_centered (Measure.dirac ()) a b D 1 D q Cfr A hA hc hpos
          slope_measurable := ?_
          slope_integrable := ?_
          slope_centered := ?_
          intercept_measurable := fun _ => highPacketIntercept_measurable a b D 1 D q
          intercept_interval := fun _ e => (densityPacketAtom_mem a b hab.le D 1 D e.2.1).1
          row_reset_interval := ?_
          vector_measurable := ?_
          time_measurable := ?_
          vector_ball := fun _ _ => covarianceAtom_mem_ball Cfr hCf _ _ _ _
          time_interval := fun _ _ => responseNode_mem_unit q _ }
        · simpa [highRowTotalMass,singletonRowData,a,b] using hpos
        · intro j i
          exact (highPacketSlope_measurable a b D 1 D q (fun _ => fun _ => 1)
            (fun _ => measurable_const)).comp measurable_fst
        · intro j x i
          exact highPacketSlope_integrable (Measure.dirac ()) a b ha hab D 1 D q (by norm_num) Cfr A hA hc hpos
            (fun _ => fun _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)
        · intro j x i
          exact highPacketAbsoluteLaw_slope_integral_zero (Measure.dirac ()) a b ha hab D 1 D q (by norm_num)
            Cfr A hA hc hpos (fun _ => fun _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)
        · intro j i e x v hv
          have hh := localDensityReset_mem_interval a b ha hab 1 (by norm_num)
            (densityPacketAtom a b D 1 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 1 D e.2.1).1
            (densityPacketAtom a b D 1 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 1 D e.2.1).2
            (fun _ => v) (fun _ _ => 1) () hv (by intro _; norm_num)
          convert hh using 1 <;> dsimp [singletonRowData,highPacketSlope,highPacketIntercept,localDensityReset] <;> ring
        · intro i γ
          exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 1 D q =>
            (highResponseMarkAtom Cfr q h.2).2 γ)).comp measurable_snd
        · intro i
          exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 1 D q =>
            (highResponseMarkAtom (ι := HighFrameIndex d D) 0 q h.2).1)).comp measurable_snd
      cases i with
      | inl _ => exact h_singletonRowSource_guards
      | inr i =>
        exact higherBandSourceRow_guards C k (higherBandFamilyTarget i.val)
          (higherBandFamilyGuardDegree M i.val) D q
          (by have := (higherBandFamily_target_bounds d D M q a b Cfr lam ℓ N μ i).1; omega)
          ↑M Cfr lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2 hM hCfr
          i.property.1 i.property.2.2.2
  have h_sourceRowTotalMass_positive : 0 < highRowTotalMass (sourceRowData d k D M q a b Cfr lam ℓ N μ).rowMass := by
    apply (singletonRowMass_positive d D q hq a b ha hab Cfr hCf).trans_le
    have h_sourceRowMass_nonneg (i : SourceRowIndex d D M q a b Cfr lam ℓ N μ) : 0 ≤ (sourceRowData d k D M q a b Cfr lam ℓ N μ).rowMass i := by
      cases i with
      | inl p => exact finePairRowMass_nonneg d D M q a b Cfr ℓ N p
      | inr i =>
        cases i with
        | inl _ => exact signedMarkMass_nonneg _ _
        | inr i => exact (higherBandFamily_mass_positive d k D M q a b Cfr lam ℓ N μ i).le
    exact Finset.single_le_sum (fun i _ => (h_sourceRowMass_nonneg i))
      (Finset.mem_univ (Sum.inr (Sum.inl ())))
  exact {
    resolution := hM
    frame := hCfr
    row_probability := fun i => (hcomp i).row_probability ()
    mass_nonneg := fun i => (hcomp i).mass_nonneg ()
    total_positive := h_sourceRowTotalMass_positive
    activation_measurable := fun i => (hcomp i).activation_measurable ()
    activation_bound := fun i => (hcomp i).activation_bound ()
    activation_centered := fun i => (hcomp i).activation_centered ()
    slope_measurable := fun j i => (hcomp i).slope_measurable j ()
    slope_integrable := fun j x i => (hcomp i).slope_integrable j x ()
    slope_centered := fun j x i => (hcomp i).slope_centered j x ()
    intercept_measurable := fun i => (hcomp i).intercept_measurable ()
    intercept_interval := fun i => (hcomp i).intercept_interval ()
    row_reset_interval := fun j i => (hcomp i).row_reset_interval j ()
    vector_measurable := fun i => (hcomp i).vector_measurable ()
    time_measurable := fun i => (hcomp i).time_measurable ()
    vector_ball := fun i => (hcomp i).vector_ball ()
    time_interval := fun i => (hcomp i).time_interval () }
end NearlyMinimax
