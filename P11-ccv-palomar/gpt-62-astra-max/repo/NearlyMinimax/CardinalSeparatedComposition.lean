module

public import NearlyMinimax.CardinalScaleVolume
public import NearlyMinimax.GaussianTensorCost
public import NearlyMinimax.FiniteTensorPolynomialMoments

@[expose] public section

/-! Actual tensor Gaussian and compact-scale separated representation of the
integrated spatial cardinal covariance. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section
variable {κ : Type*} {d n D : ℕ} (i : Fin n) (lam : ℝ) (U : DesignSample d n)

/-- Tensorization of the actual primitive Gaussian coefficient moments. -/
theorem gaussian_tensor_cardinal_moments [Fintype κ] {d : ℕ}
    {lam : ℝ} (hlam : 0 ≤ lam) (t : κ → ℝ) (ht : ∀ j, 0 ≤ t j)
    (x y : κ → Covariate d) (β β' : Fin d →₀ ℕ) :
    Integrable (fun e => gaussianTensorObservable lam t x y e *
      gaussianTensorAmplitude lam e β β') (gaussianTensorMeasure κ d) ∧
      (∫ e, gaussianTensorObservable lam t x y e * gaussianTensorAmplitude lam e β β'
        ∂gaussianTensorMeasure κ d) =
        (∏ j, t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (x j) (y j)))) *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β' := by
  let w := fun j e =>
    gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
      gaussianPrimitiveScalar d lam e
  let P := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.1 e.2.2.1.1
  let P' := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.2 e.2.2.1.2
  let p := fun j => spatialCardinalAffine (x j) (y j)
  let a := fun j => t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (x j) (y j)))
  have hpair (j : κ) (b b' : Fin d →₀ ℕ) :
      polynomialPairMoment (w j) (P j) (P' j) b b' =
        fun e => gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
          gaussianPrimitiveAmplitude lam e b b' := by
    funext e
    dsimp [w, P, P', polynomialPairMoment, gaussianPrimitiveAmplitude, gaussianPrimitiveScalar]
    ring
  have hi (j : κ) (b b' : Fin d →₀ ℕ) :
      Integrable (polynomialPairMoment (w j) (P j) (P' j) b b') (gaussianPrimitiveMeasure d) := by
    rw [hpair]
    apply gaussianPrimitive_observable_integrable
  have he (j : κ) (b b' : Fin d →₀ ℕ) :
      (∫ e, polynomialPairMoment (w j) (P j) (P' j) b b' e ∂gaussianPrimitiveMeasure d) =
        a j * (p j).coeff b * (p j).coeff b' := by
    rw [hpair]
    exact (gaussianPrimitive_separated_exact hlam (ht j) (x j) (y j) b b').symm
  have h := tensorPolynomialPairMoment_fintype_integral hi he β β'
  have hfun : tensorPolynomialPairMoment_fintype w P P' β β' =
      fun e => gaussianTensorObservable lam t x y e *
        gaussianTensorAmplitude lam e β β' := by
    funext e
    unfold tensorPolynomialPairMoment_fintype gaussianTensorObservable gaussianTensorAmplitude
      gaussianTensorScalar gaussianTensorLeftPolynomial gaussianTensorRightPolynomial gaussianPolynomialProduct
    dsimp
    rw [Finset.prod_mul_distrib]
    ring
  rw [hfun] at h
  exact h

/-- Genuine scale-and-Gaussian mark space for a fixed cardinal center. -/
abbrev CenteredCardinalMark (d : ℕ) {n : ℕ} (i : Fin n) :=
  SpatialScaleVector i × GaussianTensorMark (SpatialScaleIndex i) d

def centeredCardinalMeasure (d : ℕ) (T : ℝ) :
    Measure (CenteredCardinalMark d i) :=
  (spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d)

def centeredCardinalAmplitude
    (z : CenteredCardinalMark d i) : HighFrameIndex d D → HighFrameVector d D :=
  gaussianTensorSymmetricAmplitude lam z.2

end

section
variable {d n : ℕ} {i : Fin n} (lam : ℝ) (z : CenteredCardinalMark d i) (l : Fin n)

/-- Each observation receives one bounded spatial factor. The distinguished
observation receives the product of the left factors. -/
def centeredCardinalFactor (x : Covariate d) : ℝ :=
  if h : l ≠ i then gaussianPrimitiveRight lam (z.1 ⟨l, h⟩) (z.2 ⟨l, h⟩) x
    else ∏ j, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) x

theorem centered_cardinal_factor_abs_le_one {x : Covariate d} (hx : ∀ r, |x r| ≤ 2) :
    |centeredCardinalFactor lam z l x| ≤ 1 := by
  unfold centeredCardinalFactor
  split_ifs
  · exact gaussianPrimitiveRight_bound lam _ _ hx
  · rw [Finset.abs_prod]
    calc
      _ ≤ _ :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => gaussianTrig_abs_le_one ..)
      _ = _ := by simp

end

section
variable {d n D : ℕ} (hn : 2 ≤ n) (i : Fin n) (lam : ℝ) {T : ℝ} (hT : 1 ≤ T)

theorem centered_cardinal_factor_measurable
    (l : Fin n) (x : Covariate d) :
    Measurable (fun z : CenteredCardinalMark d i => centeredCardinalFactor lam z l x) := by
  unfold centeredCardinalFactor
  split_ifs with h
  · have hm : Measurable (fun z : CenteredCardinalMark d i => (z.1 ⟨l, h⟩, z.2 ⟨l, h⟩)) :=
      (((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_fst).prodMk
        ((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_snd))
    have hh := (gaussianPrimitiveRight_scale_measurable lam x).comp hm
    fun_prop
  · apply Finset.measurable_fun_prod
    intro j _
    have hm : Measurable (fun z : CenteredCardinalMark d i => (z.1 j, z.2 j)) :=
      (((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
    have hh := (gaussianPrimitiveLeft_scale_measurable lam x).comp hm
    fun_prop

theorem centered_cardinal_amplitude_measurable
    (β β' : HighFrameIndex d D) :
    Measurable (fun z => centeredCardinalAmplitude i lam z β β') :=
  (gaussianTensorSymmetricAmplitude_measurable lam β β').comp measurable_snd

theorem centered_cardinal_measure_finite (d : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  unfold centeredCardinalMeasure
  infer_instance

include hT in
theorem centered_cardinal_cost_integrable :
    Integrable (separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam))
      (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  have h := (integrable_const 1 (μ := spatialScaleMeasure i T)).mul_prod
    (gaussianTensorSymmetricAmplitude_cost_integrable (κ := SpatialScaleIndex i) (d := d) (D := D) lam)
  change Integrable (fun z : CenteredCardinalMark d i =>
    separatedMatrixCost (gaussianTensorSymmetricAmplitude lam) z.2)
      ((spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d))
  simpa using h

theorem centered_cardinal_cost_integral_eq (T : ℝ) :
    (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) =
      volume.real (spatialScaleDomain i T) *
        (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam) e ∂gaussianTensorMeasure (SpatialScaleIndex i) d) := by
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  letI : SFinite (spatialScaleMeasure i T) := by unfold spatialScaleMeasure; infer_instance
  have h := integral_prod_mul (μ := spatialScaleMeasure i T)
    (ν := gaussianTensorMeasure (SpatialScaleIndex i) d) (fun _ => 1)
    (separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam))
  simp at h
  simpa only [centeredCardinalMeasure, centeredCardinalAmplitude, separatedMatrixCost,
    spatialScaleMeasure, Measure.real, Measure.restrict_apply_univ] using h

include hn hT in
/-- Actual representation cost, obtained from the actual Gaussian tensor
moment cost and actual logarithmic scale-domain volume. -/
theorem centered_cardinal_cost_integral_le :
    (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) ≤
      (1024 * |lam| * d ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  rw [centered_cardinal_cost_integral_eq]
  have hcost := gaussianTensorSymmetricAmplitude_integrated_cost
    (κ := SpatialScaleIndex i) (d := d) (D := D) lam
  rw [spatial_scale_index_card] at hcost
  have hvol := spatial_scale_domain_volume_le_uniform hn i hT
  have hlog := Real.log_nonneg hT
  have hnn : 0 ≤ ∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam) e ∂gaussianTensorMeasure (SpatialScaleIndex i) d :=
    integral_nonneg (fun e => Finset.sum_nonneg (fun β _ => by positivity))
  have h := mul_le_mul hvol hcost hnn (by positivity)
  convert h using 1
  rw [show (1024 * |lam| * d ^ 2) = 2 * (512 * |lam| * d ^ 2) by ring, mul_pow]
  ring

theorem centered_cardinal_factor_product
    (z : CenteredCardinalMark d i) (U : DesignSample d n) :
    (∏ l, centeredCardinalFactor lam z l (U l)) =
      gaussianTensorObservable lam z.1 (fun _ => U i) (fun j => U j.val) z.2 := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun l => centeredCardinalFactor lam z l (U l)) (Finset.mem_univ i)]
  have he : centeredCardinalFactor lam z i (U i) =
      ∏ j, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) (U i) := by
    simp [centeredCardinalFactor]
  rw [he]
  rw [Finset.prod_subtype (p := fun l => l ≠ i) (Finset.univ.erase i)
    (fun l => by simp) (fun l => centeredCardinalFactor lam z l (U l))]
  have hr : (∏ j : SpatialScaleIndex i, centeredCardinalFactor lam z j.val (U j.val)) =
      ∏ j, gaussianPrimitiveRight lam (z.1 j) (z.2 j) (U j.val) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [centeredCardinalFactor, dite_eq_left j.property]
  rw [hr, ← Finset.prod_mul_distrib]
  rfl

end

section
variable {d n D : ℕ} {i : Fin n} {lam : ℝ} (hlam : 0 ≤ lam) {t : SpatialScaleVector i} (ht : t ∈ Ici 0)
    (U : DesignSample d n) (β β' : HighFrameIndex d D)
include hlam ht

theorem centered_cardinal_raw_tensor_integrable :
    Integrable (fun e =>
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β') (gaussianTensorMeasure (SpatialScaleIndex i) d) :=
  (gaussian_tensor_cardinal_moments hlam t (fun j => ht j)
    (fun _ => U i) (fun j => U j.val) _ _).1

theorem centered_cardinal_raw_tensor_exact :
    (∫ e,
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) =
      spatialCenteredCardinalMatrix lam U t β β' := by
  have h := (gaussian_tensor_cardinal_moments hlam t (fun j => ht j)
    (fun _ => U i) (fun j => U j.val) (polynomialBoxExponent β.val) (polynomialBoxExponent β'.val)).2
  simpa only [gaussianTensorFrameAmplitude, gaussianTensorAmplitude, spatialCenteredCardinalMatrix, highFrameCoefficients,
    spatial_cardinal_scale_product, spatial_cardinal_polynomial_scale_product] using h

theorem centered_cardinal_symmetric_tensor_exact :
    (∫ e,
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorSymmetricAmplitude lam e β β' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) =
      spatialCenteredCardinalMatrix lam U t β β' := by
  have he : (fun e =>
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorSymmetricAmplitude lam e β β') =
      fun e => (gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β' +
        gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β' β) / 2 := by
    funext e
    unfold gaussianTensorSymmetricAmplitude realMatrixSymmetrize
    ring
  rw [he, integral_div, integral_add
    (centered_cardinal_raw_tensor_integrable hlam ht U β β')
    (centered_cardinal_raw_tensor_integrable hlam ht U β' β),
    centered_cardinal_raw_tensor_exact hlam ht U β β',
    centered_cardinal_raw_tensor_exact hlam ht U β' β]
  unfold spatialCenteredCardinalMatrix
  ring

end

variable {d n D : ℕ} (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T)
include hT

theorem centered_cardinal_product_entry_integrable {U : DesignSample d n} (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => (∏ l, centeredCardinalFactor lam z l (U l)) *
      centeredCardinalAmplitude i lam z β β') (centeredCardinalMeasure i d T) := by
  have hm : Measurable (fun z => ∏ l, centeredCardinalFactor lam z l (U l)) :=
    Finset.measurable_fun_prod _ (fun l _ => centered_cardinal_factor_measurable i lam l (U l))
  have hb : ∀ z : CenteredCardinalMark d i, |∏ l, centeredCardinalFactor lam z l (U l)| ≤ 1 := by
    intro z
    rw [Finset.abs_prod]
    calc
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun l _ => centered_cardinal_factor_abs_le_one lam z l (hU l))
      _ = _ := by simp
  have h := (separatedMatrix_entry_integrable (centered_cardinal_amplitude_measurable i lam)
      (centered_cardinal_cost_integrable i lam hT) β β').mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by exact hb z))
  exact h.congr (Filter.Eventually.of_forall (fun z => mul_comm _ _))

include hlam in
/-- Exact positive separated representation of each centered, scale-integrated
term of the genuine cardinal covariance. -/
theorem centered_cardinal_integrated_separated_exact (U : DesignSample d n)
    (hU : ∀ l r, |U l r| ≤ 2) (β β' : HighFrameIndex d D) :
    (∫ t, spatialCenteredCardinalMatrix lam U t β β' ∂spatialScaleMeasure i T) =
      ∫ z, (∏ l, centeredCardinalFactor lam z l (U l)) * centeredCardinalAmplitude i lam z β β'
        ∂centeredCardinalMeasure i d T := by
  letI := spatial_scale_measure_finite i hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  symm
  rw [centeredCardinalMeasure, integral_prod _ (centered_cardinal_product_entry_integrable i lam hT hU β β')]
  apply integral_congr_ae
  have hae : ∀ᵐ t ∂spatialScaleMeasure i T, t ∈ spatialScaleDomain i T :=
    ae_restrict_mem (spatial_scale_domain_isClosed i T).measurableSet
  filter_upwards [hae] with t ht
  simp_rw [centered_cardinal_factor_product]
  exact centered_cardinal_symmetric_tensor_exact hlam ht.1 U β β'

end NearlyMinimax
