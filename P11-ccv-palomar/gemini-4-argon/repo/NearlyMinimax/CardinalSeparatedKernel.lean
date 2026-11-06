module
public import Mathlib
public import NearlyMinimax.CardinalSeparatedComposition
@[expose] public section
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
theorem measurable_sigma_mk_actual  
    [∀ i, MeasurableSpace (E i)] (i ) : Measurable (Sigma.mk i : E i → Sigma E) := by
  apply Measurable.of_le_map
  exact iInf_le _ i
theorem measurable_sigma_of_fibers  
    [∀ i, MeasurableSpace (E i)] {X : Type*} [MeasurableSpace X]
    (f : Sigma E → X) (hf : ∀ i, Measurable (fun e : E i => f ⟨i, e⟩)) : Measurable f := by
  apply Measurable.of_le_map
  change _ ≤ (⨅ i, (inferInstance : MeasurableSpace (E i)).map (Sigma.mk i)).map f
  rw [MeasurableSpace.map_iInf]
  apply le_iInf
  intro i
  rw [MeasurableSpace.map_comp]
  exact (hf i).le_map
theorem sigma_borelSpace_actual  [Countable ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] :
    BorelSpace (Sigma E) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hfiber (i : ι) : MeasurableSet (Sigma.mk i ⁻¹' s) :=
      hs.preimage (measurable_sigma_mk_actual i)
    have himage (i : ι) : MeasurableSet[borel (Sigma E)] (Sigma.mk i '' (Sigma.mk i ⁻¹' s)) := by
      letI : MeasurableSpace (Sigma E) := borel (Sigma E)
      letI : BorelSpace (Sigma E) := ⟨rfl⟩
      exact (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image).mpr (hfiber i)
    have he : s = ⋃ i : ι, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
      ext z
      constructor
      · intro hz
        exact mem_iUnion.mpr ⟨z.1, ⟨z.2, hz, Sigma.eta z⟩⟩
      · intro hz
        rcases mem_iUnion.mp hz with ⟨i, hi⟩
        rcases hi with ⟨e, he, rfl⟩
        exact he
    rw [he]
    exact MeasurableSet.iUnion himage
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro i
    exact (hs.preimage continuous_sigmaMk).measurableSet
theorem sigma_standardBorel_actual  [Countable ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] : StandardBorelSpace (Sigma E) := by
  letI : ∀ i, TopologicalSpace (E i) := fun i => (upgradeStandardBorel (E i)).toTopologicalSpace
  letI : ∀ i, BorelSpace (E i) := fun i => (upgradeStandardBorel (E i)).toBorelSpace
  letI : ∀ i, PolishSpace (E i) := fun i => (upgradeStandardBorel (E i)).toPolishSpace
  letI : BorelSpace (Sigma E) := sigma_borelSpace_actual
  infer_instance
variable {n d D : ℕ} {T : ℝ}
def spatialScalePermutation  (τ : Equiv.Perm (Fin n)) (i ) :
    SpatialScaleIndex i ≃ SpatialScaleIndex (τ i) where
  toFun j := ⟨τ j.val, fun h => j.property (τ.injective h)⟩
  invFun j := ⟨τ.symm j.val, fun h => j.property
    ((τ.apply_symm_apply j.val).symm.trans (congrArg τ h))⟩
  left_inv j := Subtype.ext (τ.symm_apply_apply j.val)
  right_inv j := Subtype.ext (τ.apply_symm_apply j.val)
def spatialScaleReindex  (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    SpatialScaleVector i ≃ᵐ SpatialScaleVector (τ i) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (spatialScalePermutation τ i)
@[simp] theorem spatialScaleReindex_apply  (τ )
    (i : Fin n) (t : SpatialScaleVector i) (j : SpatialScaleIndex i) :
    spatialScaleReindex τ i t (spatialScalePermutation τ i j) = t j := by
  simpa only [spatialScaleReindex] using
    MeasurableEquiv.piCongrLeft_apply_apply (spatialScalePermutation τ i)
      (β := fun _ => ℝ) t j
theorem spatial_centered_cardinal_matrix_perm  (τ : Equiv.Perm (Fin n))
    (U i lam t)
    (β β' : HighFrameIndex d D) :
    spatialCenteredCardinalMatrix i lam (U ∘ τ) t β β' =
      spatialCenteredCardinalMatrix (τ i) lam U (spatialScaleReindex τ i t) β β' := by
  have h_spatialScalePermutation_val (τ : Equiv.Perm (Fin n)) (i : Fin n) (j : SpatialScaleIndex i) : (spatialScalePermutation τ i j).val = τ j.val := rfl
  have h_spatial_cardinal_polynomial_perm : spatialCardinalPolynomial (U ∘ τ) i = spatialCardinalPolynomial U (τ i) := by
    rw [spatial_cardinal_polynomial_scale_product, spatial_cardinal_polynomial_scale_product]
    simpa only [Function.comp_def, h_spatialScalePermutation_val] using
      (spatialScalePermutation τ i).prod_comp
        (fun j => spatialCardinalAffine (U (τ i)) (U j.val))
  have h_spatial_cardinal_scale_perm : spatialCardinalScale lam (spatialScaleExtend i t) (U ∘ τ) i =
      spatialCardinalScale lam (spatialScaleExtend (τ i) (spatialScaleReindex τ i t)) U (τ i) := by
    rw [spatial_cardinal_scale_product, spatial_cardinal_scale_product]
    simpa only [Function.comp_def, h_spatialScalePermutation_val, spatialScaleReindex_apply] using
      (spatialScalePermutation τ i).prod_comp (fun j => spatialScaleReindex τ i t j * lam ^ 2 *
        Real.exp (-spatialScaleReindex τ i t j * lam * spatialSquaredDistance (U (τ i)) (U j.val)))
  simp only [spatialCenteredCardinalMatrix, h_spatial_cardinal_polynomial_perm,
    h_spatial_cardinal_scale_perm]
theorem spatial_centered_cardinal_integral_perm  (τ : Equiv.Perm (Fin n))
    (U : Fin n → Covariate d) (i : Fin n) (lam T : ℝ) (β β' : HighFrameIndex d D) :
    (∫ t, spatialCenteredCardinalMatrix i lam (U ∘ τ) t β β' ∂spatialScaleMeasure i T) =
      ∫ t, spatialCenteredCardinalMatrix (τ i) lam U t β β' ∂spatialScaleMeasure (τ i) T := by
  have h_spatial_scale_reindex_measurePreserving : MeasurePreserving (spatialScaleReindex τ i) (spatialScaleMeasure i T) (spatialScaleMeasure (τ i) T) := by
    have hp : MeasurePreserving (spatialScaleReindex τ i) volume volume :=
      measurePreserving_piCongrLeft (fun _ : SpatialScaleIndex (τ i) => (volume : Measure ℝ))
        (spatialScalePermutation τ i)
    have hr := hp.restrict_preimage (spatial_scale_domain_isClosed (τ i) T).measurableSet
    have hpre : (spatialScaleReindex τ i) ⁻¹' spatialScaleDomain (τ i) T = spatialScaleDomain i T := by
      ext t
      have h_spatial_scale_domain_reindex : spatialScaleReindex τ i t ∈ spatialScaleDomain (τ i) T ↔ t ∈ spatialScaleDomain i T := by
        have horthant : spatialScaleReindex τ i t ∈ Ici 0 ↔ t ∈ Ici 0 := by
          constructor
          · intro h j
            have hj := h (spatialScalePermutation τ i j)
            simpa only [Pi.zero_apply, spatialScaleReindex_apply] using hj
          · intro h j
            obtain ⟨j', rfl⟩ := (spatialScalePermutation τ i).surjective j
            simpa only [Pi.zero_apply, spatialScaleReindex_apply] using h j'
        have h_spatial_scale_log_sum_reindex : spatialScaleLogSum (τ i) (spatialScaleReindex τ i t) = spatialScaleLogSum i t := by
          have hs := (spatialScalePermutation τ i).sum_comp
            (fun j => Real.log (1 + max 0 (spatialScaleReindex τ i t j)))
          simpa only [spatialScaleLogSum, spatialScaleReindex_apply] using hs.symm
        simp only [spatialScaleDomain, mem_inter_iff, mem_setOf_eq,
          h_spatial_scale_log_sum_reindex, horthant]
      exact h_spatial_scale_domain_reindex
    rw [hpre] at hr
    exact hr
  rw [← h_spatial_scale_reindex_measurePreserving.integral_comp']
  exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
    spatial_centered_cardinal_matrix_perm τ U i lam t β β')
theorem integrated_cardinal_matrix_perm  (τ : Equiv.Perm (Fin n))
    (lam T : ℝ) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (U ∘ τ) β β' = integratedCardinalMatrix lam T U β β' := by
  simp only [integratedCardinalMatrix, spatial_centered_cardinal_integral_perm]
  exact Equiv.sum_comp τ (fun i => ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T)
abbrev CardinalSeparatedMark (d n : ℕ) := Σ i : Fin n, CenteredCardinalMark d n i
def cardinalSeparatedMeasure (d n ) (T : ℝ) : Measure (CardinalSeparatedMark d n) :=
  ∑ i : Fin n, Measure.map (Sigma.mk i) (centeredCardinalMeasure i d T)
def cardinalSeparatedAmplitude  (lam : ℝ)
    (z : CardinalSeparatedMark d n) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  centeredCardinalAmplitude z.1 lam z.2
def cardinalSeparatedFactor  (lam : ℝ) (z : CardinalSeparatedMark d n)
    (l : Fin n) (x : Covariate d) : ℝ :=
  centeredCardinalFactor z.1 lam z.2 l x
theorem cardinal_separated_mark_standardBorel (d n ) : StandardBorelSpace (CardinalSeparatedMark d n) :=
  sigma_standardBorel_actual
theorem cardinal_separated_measure_finite (d n : ℕ)  (hT : 1 ≤ T) :
    IsFiniteMeasure (cardinalSeparatedMeasure d n T) := by
  letI : ∀ i : Fin n, IsFiniteMeasure (centeredCardinalMeasure i d T) :=
    fun i => centered_cardinal_measure_finite i d hT
  unfold cardinalSeparatedMeasure
  infer_instance
theorem cardinal_separated_amplitude_measurable  (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable (fun z : CardinalSeparatedMark d n => cardinalSeparatedAmplitude lam z β β') :=
  measurable_sigma_of_fibers _ (fun i => centered_cardinal_amplitude_measurable i lam β β')
theorem cardinal_separated_factor_measurable  (lam : ℝ) (l : Fin n) (x : Covariate d) :
    Measurable (fun z : CardinalSeparatedMark d n => cardinalSeparatedFactor lam z l x) :=
  measurable_sigma_of_fibers _ (fun i => centered_cardinal_factor_measurable i lam l x)
theorem cardinal_separated_factor_abs_le_one  (lam : ℝ) (z : CardinalSeparatedMark d n)
    (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) :
    |cardinalSeparatedFactor lam z l x| ≤ 1 :=
  centered_cardinal_factor_abs_le_one z.1 lam z.2 l x hx
theorem cardinal_separated_integrable_of_fibers  (T )
    (f : CardinalSeparatedMark d n → ℝ) (hf : Measurable f)
    (hi : ∀ i : Fin n, Integrable (fun z => f ⟨i, z⟩) (centeredCardinalMeasure i d T)) :
    Integrable f (cardinalSeparatedMeasure d n T) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply (integrable_map_measure hf.aestronglyMeasurable (measurable_sigma_mk_actual i).aemeasurable).mpr
  exact hi i
theorem cardinal_separated_integral_eq_sum  (T )
    (f : CardinalSeparatedMark d n → ℝ) (hf : Measurable f)
    (hi : ∀ i : Fin n, Integrable (fun z => f ⟨i, z⟩) (centeredCardinalMeasure i d T)) :
    (∫ z, f z ∂cardinalSeparatedMeasure d n T) =
      ∑ i : Fin n, ∫ z, f ⟨i, z⟩ ∂centeredCardinalMeasure i d T := by
  unfold cardinalSeparatedMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_map_measure hf.aestronglyMeasurable (measurable_sigma_mk_actual i).aemeasurable).mpr (hi i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (measurable_sigma_mk_actual i).aemeasurable hf.aestronglyMeasurable
theorem cardinal_separated_cost_measurable  (lam ) :
    Measurable (separatedMatrixCost (cardinalSeparatedAmplitude (d := d) (n := n) (D := D) lam)) :=
  Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
    (fun β' _ => (cardinal_separated_amplitude_measurable lam β β').abs))
theorem cardinal_separated_cost_integrable  (lam )  (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam)) (cardinalSeparatedMeasure d n T) :=
  cardinal_separated_integrable_of_fibers T _ (cardinal_separated_cost_measurable lam)
    (fun i => centered_cardinal_cost_integrable i lam hT)
theorem cardinal_separated_cost_integral_le  (hn : 2 ≤ n) (lam )
     (hT : 1 ≤ T) :
    (∫ z, separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam) z ∂cardinalSeparatedMeasure d n T) ≤
      ↑n * (1024 * |lam| * ↑d ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  rw [cardinal_separated_integral_eq_sum T _ (cardinal_separated_cost_measurable lam)
    (fun i => centered_cardinal_cost_integrable i lam hT)]
  change (∑ i : Fin n, ∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z
    ∂centeredCardinalMeasure i d T) ≤ _
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => centered_cardinal_cost_integral_le (d := d) (D := D) hn i lam hT)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using h
theorem cardinal_separated_product_entry_integrable  (lam : ℝ)
     (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => (∏ l, cardinalSeparatedFactor lam z l (U l)) * cardinalSeparatedAmplitude lam z β β')
      (cardinalSeparatedMeasure d n T) := by
  have hm : Measurable (fun z : CardinalSeparatedMark d n =>
      (∏ l, cardinalSeparatedFactor lam z l (U l)) * cardinalSeparatedAmplitude lam z β β') :=
    (Finset.measurable_fun_prod _ (fun l _ => cardinal_separated_factor_measurable lam l (U l))).mul
      (cardinal_separated_amplitude_measurable lam β β')
  exact cardinal_separated_integrable_of_fibers T _ hm
    (fun i => centered_cardinal_product_entry_integrable i lam hT U hU β β')
def cardinalSeparatedSymmetricFactor  (lam : ℝ)
    (z : CardinalSeparatedMark d n) (U : Fin n → Covariate d) : ℝ :=
  (∑ τ : Equiv.Perm (Fin n), ∏ l, cardinalSeparatedFactor lam z l (U (τ l))) / n.factorial
theorem cardinal_separated_symmetric_entry_integrable  (lam )
     (hT : 1 ≤ T) (U ) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β')
      (cardinalSeparatedMeasure d n T) := by
  have hi := (integrable_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n))) (fun (τ : Equiv.Perm (Fin n)) _ =>
    cardinal_separated_product_entry_integrable lam hT (U ∘ τ) (fun l r => hU (τ l) r) β β')).div_const ↑n.factorial
  simpa only [cardinalSeparatedSymmetricFactor, Function.comp_apply, Finset.sum_mul, div_mul_eq_mul_div] using hi
theorem integrated_cardinal_symmetric_separated_exact  (lam ) (hlam : 0 ≤ lam)
     (hT : 1 ≤ T) (U ) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T := by
  have he (z : CardinalSeparatedMark d n) :
      cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β' =
        (∑ τ : Equiv.Perm (Fin n),
          (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β') / ↑n.factorial := by
    simp only [cardinalSeparatedSymmetricFactor, Finset.sum_mul, div_mul_eq_mul_div]
  simp_rw [he]
  have hsum := integral_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n))) (fun (τ : Equiv.Perm (Fin n)) _ =>
    cardinal_separated_product_entry_integrable lam hT (U ∘ τ) (fun l r => hU (τ l) r) β β')
  change (∫ z, ∑ τ : Equiv.Perm (Fin n),
    (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
    ∂cardinalSeparatedMeasure d n T) = ∑ τ : Equiv.Perm (Fin n),
      ∫ z, (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T at hsum
  rw [integral_div, hsum]
  have hs (τ : Equiv.Perm (Fin n)) :
      (∫ z, (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T) = integratedCardinalMatrix lam T U β β' := by
    have h_integrated_cardinal_separated_exact : integratedCardinalMatrix lam T (U ∘ τ) β β' =
      ∫ z, (∏ l, cardinalSeparatedFactor lam z l ((U ∘ τ) l)) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T := by
      have hU : ∀ l r, |(U ∘ τ) l r| ≤ 2 := fun l r => hU (τ l) r
      have hm : Measurable (fun z : CardinalSeparatedMark d n =>
          (∏ l, cardinalSeparatedFactor lam z l ((U ∘ τ) l)) * cardinalSeparatedAmplitude lam z β β') :=
        (Finset.measurable_fun_prod _ (fun l _ => cardinal_separated_factor_measurable lam l ((U ∘ τ) l))).mul
          (cardinal_separated_amplitude_measurable lam β β')
      rw [cardinal_separated_integral_eq_sum T _ hm
        (fun i => centered_cardinal_product_entry_integrable i lam hT (U ∘ τ) hU β β')]
      unfold integratedCardinalMatrix
      apply Finset.sum_congr rfl
      intro i _
      have h_centered_cardinal_integrated_separated_exact (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2) : (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T) =
          ∫ z, (∏ l, centeredCardinalFactor i lam z l (U l)) * centeredCardinalAmplitude i lam z β β'
            ∂centeredCardinalMeasure i d T := by
        letI := spatial_scale_measure_finite i T hT
        letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
        symm
        rw [centeredCardinalMeasure, integral_prod _ (centered_cardinal_product_entry_integrable i lam hT U hU β β')]
        apply integral_congr_ae
        have h_centered_cardinal_factor_product (z : CenteredCardinalMark d n i) (U : Fin n → Covariate d) : (∏ l, centeredCardinalFactor i lam z l (U l)) =
            gaussianTensorObservable lam z.1 (fun _ : SpatialScaleIndex i => U i) (fun j => U j.val) z.2 := by
          rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
            (fun l => centeredCardinalFactor i lam z l (U l)) (Finset.mem_univ i)]
          have he : centeredCardinalFactor i lam z i (U i) =
              ∏ j : SpatialScaleIndex i, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) (U i) := by
            simp [centeredCardinalFactor]
          rw [he, Finset.prod_subtype (p := fun l : Fin n => l ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
            (fun l => by simp) (fun l : Fin n => centeredCardinalFactor i lam z l (U l))]
          have hr : (∏ j : SpatialScaleIndex i, centeredCardinalFactor i lam z j.val (U j.val)) =
              ∏ j : SpatialScaleIndex i, gaussianPrimitiveRight lam (z.1 j) (z.2 j) (U j.val) := by
            apply Finset.prod_congr rfl
            intro j _
            simp only [centeredCardinalFactor, dite_eq_left j.property]
          rw [hr, ← Finset.prod_mul_distrib]
          rfl
        filter_upwards [ae_restrict_mem (spatial_scale_domain_isClosed i T).measurableSet] with t ht
        simp_rw [h_centered_cardinal_factor_product]
        exact centered_cardinal_symmetric_tensor_exact i lam hlam t ht.1 U β β'
      exact (h_centered_cardinal_integrated_separated_exact (U ∘ τ) hU)
    simpa only [Function.comp_apply] using
      h_integrated_cardinal_separated_exact.symm.trans
        (integrated_cardinal_matrix_perm τ lam T U β β')
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  field_simp
end NearlyMinimax
