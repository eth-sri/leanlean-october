module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.BoundaryFourier
public import RequestProject.SobolevMultiplier
public import RequestProject.LpBoundedMultiplier
public import RequestProject.NeumannH1SmoothMultiplier
public import RequestProject.ConormalNormalization
public import RequestProject.DiskHalfTrace
public import RequestProject.PlanarNotation

/-!
# Fourier coefficients of actual boundary multiplication

The coefficient function has averaged circle Fourier coefficients. The input
and output use the genuine orthonormal boundary Fourier map for measure dθ.
Thus multiplication is convolution with the averaged coefficients, with no
additional square-root-of-2π factor in the convolution kernel.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter

section

variable (a : SmoothH1Coefficient) (A : C(ParamCircle, ℂ))
    (hA : ∀ θ : ℝ, A (θ : ParamCircle) = a (unitCirclePt θ))
    (hc : IsWL1 halfOrder (fourierCoeff A)) (u : NeumannH1 unitDisk) (g : BoundaryL2)

include A in
/-- Multiplication by an actual continuous periodic circle function. -/
def boundaryContinuousMultiplier :
    BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (fun θ : ℝ => A (θ : ParamCircle))
    (A.continuous.comp (AddCircle.continuous_mk' _)).aestronglyMeasurable
    (Eventually.of_forall (fun θ => A.norm_coe_le_norm (θ : ParamCircle)))

theorem boundaryContinuousMultiplier_ae :
    (boundaryContinuousMultiplier A g : ℝ → ℂ)
      =ᵐ[angleMeasure]
        fun θ => A (θ : ParamCircle) * g θ :=
  lpBoundedMultiplier_ae _
    (A.continuous.comp (AddCircle.continuous_mk' _)).aestronglyMeasurable
    _ g

theorem boundaryCircleLift_continuousMultiplier_ae :
    (boundaryCircleLift (boundaryContinuousMultiplier A g) : ParamCircle → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun q => A q * boundaryCircleLift g q := by
  filter_upwards [boundaryCircleLift_coe _,
    boundary_liftIoc_congr_ae (boundaryContinuousMultiplier_ae A g),
    boundaryCircleLift_coe g] with q hm hl hg
  rw [hm, hl, hg]
  change A ((AddCircle.equivIoc anglePeriod 0 q : ℝ) : ParamCircle) *
    AddCircle.liftIoc anglePeriod 0 (g : ℝ → ℂ) q =
      _
  simp

theorem boundaryFourier_eq_sqrt_mul_circleLift (n : ℤ) :
    boundaryFourier g n = fourierScale *
      fourierCoeff (boundaryCircleLift g) n := by
  rw [boundaryFourier_apply,
    fourierCoeff_congr_ae (boundaryCircleLift_coe g), fourierCoeff_liftIoc_eq]
  simp

/-- Exact convolution for arbitrary actual boundary L² input. -/
theorem boundaryFourier_continuousMultiplier
    (hA : Summable (fourierCoeff A)) (g : BoundaryL2) (n : ℤ) :
    boundaryFourier (boundaryContinuousMultiplier A g) n =
      seqConv (fourierCoeff A) (boundaryFourier g) n := by
  
  have hprod : fourierCoeff (boundaryCircleLift (boundaryContinuousMultiplier A g)) =
      seqConv (fourierCoeff A) (fourierCoeff (boundaryCircleLift g)) := by
    rw [fourierCoeff_congr_ae (boundaryCircleLift_continuousMultiplier_ae A g)]
    exact fourierCoeff_mul_eq_seqConv A hA ((Lp.memLp (boundaryCircleLift g)).integrable (by norm_num))
  rw [boundaryFourier_eq_sqrt_mul_circleLift, hprod]
  unfold seqConv
  rw [← tsum_mul_left]
  simp [boundaryFourier_eq_sqrt_mul_circleLift] <;> ring

/-- Removing the actual half-trace weight gives the ordinary orthonormal
Fourier coefficients. Their square-root-of-2π normalization is retained. -/
theorem fromL2_half_diskHalfTrace :
    fromL2 halfOrder (diskHalfTrace u) = boundaryFourier (diskH1Trace u) := by
  funext n
  rw [fromL2, diskHalfTrace_apply]
  have hw : sobWeight n ^ (-halfOrder) * Real.sqrt (sobWeight n) = 1 := by
    rw [Real.sqrt_eq_rpow, mul_comm, sobWeight_rpow_mul_neg]
  change ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
    ((Real.sqrt (sobWeight n) : ℂ) * boundaryFourier (diskH1Trace u) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, hw]
  simp

include hA in
theorem diskH1Trace_smoothMultiplier :
    diskH1Trace (neumannH1SmoothMultiplier unitDisk a u) =
      boundaryContinuousMultiplier A (diskH1Trace u) := by
  change h1BoundaryTrace isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
    (neumannH1SmoothMultiplier unitDisk a u) = _
  rw [h1BoundaryTrace_neumannH1SmoothMultiplier unitDisk_bounded]
  change h1SmoothBoundaryMultiplier unitCircle_isBoundaryParam a (diskH1Trace u) =
    _
  apply Lp.ext
  filter_upwards [h1SmoothBoundaryMultiplier_ae unitCircle_isBoundaryParam a (diskH1Trace u),
    boundaryContinuousMultiplier_ae A (diskH1Trace u)] with θ hs hc
  simp [*]

theorem multiplier_toCLM_apply {s t C : ℝ}
    {Φ : (ℤ → ℂ) → (ℤ → ℂ)} (H : SeqOpBound s t C Φ) (b : L2Z) (n : ℤ) :
    H.toCLM b n = ((sobWeight n ^ t : ℝ) : ℂ) * Φ (fromL2 s b) n := rfl

include hA in
/-- The actual smooth multiplier and its normalized Fourier operator agree
on the genuine disk H¹ half trace, for every input. -/
theorem diskHalfTrace_smoothMultiplier :
    diskHalfTrace (neumannH1SmoothMultiplier unitDisk a u) =
      (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM (diskHalfTrace u) := by
  have hsum : Summable (fourierCoeff A) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (by norm_num) _ hc
    intro n
    exact le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_rpow (one_le_sobWeight n) (by positivity))
  ext n
  have hL : diskHalfTrace
      (neumannH1SmoothMultiplier unitDisk a u) n =
      (Real.sqrt (sobWeight n)) *
        seqConv (fourierCoeff A) (boundaryFourier (diskH1Trace u)) n := by
    rw [diskHalfTrace_apply, diskH1Trace_smoothMultiplier a A hA,
      boundaryFourier_continuousMultiplier A hsum]
    rfl
  have hR  :=
    multiplier_toCLM_apply  
       
      (seqOpBound_seqConv  
        (by norm_num : (0 : ℝ) ≤ 1 / 2) hc) (diskHalfTrace u) n
  rw [hL, hR, fromL2_half_diskHalfTrace, Real.sqrt_eq_rpow]

end

end PolyaNeumann

end
