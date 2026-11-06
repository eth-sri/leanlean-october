module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.BoundaryFourier
public import RequestProject.SobolevMultiplier
public import RequestProject.LpBoundedMultiplier
public import RequestProject.NeumannH1SmoothMultiplier
public import RequestProject.ConormalNormalization
public import RequestProject.DiskHalfTrace

/-!
# Fourier coefficients of actual boundary multiplication

The coefficient function has averaged circle Fourier coefficients. The input
and output use the genuine orthonormal boundary Fourier map for measure dθ.
Thus multiplication is convolution with the averaged coefficients, with no
additional square-root-of-2π factor in the convolution kernel.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter



/-- Multiplication by an actual continuous periodic circle function. -/
def boundaryContinuousMultiplier (A : C(AddCircle circlePeriod, ℂ)) :
    ComplexEnd BoundaryL2 :=
  lpBoundedMultiplier (fun θ : ℝ => A (θ : AddCircle circlePeriod))
    (A.continuous.comp (AddCircle.continuous_mk' _)).aestronglyMeasurable
    (Eventually.of_forall (fun θ => A.norm_coe_le_norm (θ : AddCircle circlePeriod)))

section
variable (A : C(AddCircle circlePeriod, ℂ))

include A in
theorem boundaryContinuousMultiplier_ae
    g :
    (boundaryContinuousMultiplier A g : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
        fun θ => A (θ : AddCircle circlePeriod) * g θ :=
  lpBoundedMultiplier_ae (fun θ : ℝ => A (θ : AddCircle circlePeriod))
    (A.continuous.comp (AddCircle.continuous_mk' _)).aestronglyMeasurable
    (Eventually.of_forall (fun θ => A.norm_coe_le_norm (θ : AddCircle circlePeriod))) g

include A in
theorem boundaryCircleLift_continuousMultiplier_ae g :
    (boundaryCircleLift (boundaryContinuousMultiplier A g) : AddCircle circlePeriod → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun q => A q * boundaryCircleLift g q := by
  filter_upwards [boundaryCircleLift_coe (boundaryContinuousMultiplier A g),
    boundary_liftIoc_congr_ae (boundaryContinuousMultiplier_ae A g),
    boundaryCircleLift_coe g] with q hm hl hg
  rw [hm, hl, hg]
  change A ((AddCircle.equivIoc circlePeriod 0 q)) *
    AddCircle.liftIoc circlePeriod 0 g q =
      A q * AddCircle.liftIoc circlePeriod 0 g q
  simp_all

theorem boundaryFourier_eq_sqrt_mul_circleLift g n :
    boundaryFourier g n = (Real.sqrt circlePeriod : ℂ) *
      fourierCoeff (boundaryCircleLift g) n := by
  rw [boundaryFourier_apply,
    fourierCoeff_congr_ae (boundaryCircleLift_coe g), fourierCoeff_liftIoc_eq]
  simp  

include A in
/-- Exact convolution for arbitrary actual boundary L² input. -/
theorem boundaryFourier_continuousMultiplier
    (hA : Summable (fourierCoeff A)) g n :
    boundaryFourier (boundaryContinuousMultiplier A g) n =
      seqConv (fourierCoeff A) (boundaryFourier g) n := by
  have hg  :=
    (Lp.memLp (boundaryCircleLift g)).integrable (by norm_num)
  have hprod : fourierCoeff (boundaryCircleLift (boundaryContinuousMultiplier A g)) =
      seqConv (fourierCoeff A) (fourierCoeff (boundaryCircleLift g)) := by
    rw [fourierCoeff_congr_ae (boundaryCircleLift_continuousMultiplier_ae A g)]
    exact?
  rw [boundaryFourier_eq_sqrt_mul_circleLift, hprod]
  unfold seqConv
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [boundaryFourier_eq_sqrt_mul_circleLift]
  ring

end


/-- Removing the actual half-trace weight gives the ordinary orthonormal
Fourier coefficients. Their square-root-of-2π normalization is retained. -/
theorem fromL2_half_diskHalfTrace u :
    fromL2 (1 / 2 : ℝ) (diskHalfTrace u) = boundaryFourier (diskH1Trace u) := by
  funext n
  have hw : sobWeight n ^ (-(1 / 2 : ℝ)) * Real.sqrt (sobWeight n) = 1 := by
    rw [Real.sqrt_eq_rpow, mul_comm, sobWeight_rpow_mul_neg]
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) *
    ((Real.sqrt (sobWeight n)) * boundaryFourier (diskH1Trace u) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, hw]
  simp

section
variable (a : SmoothH1Coefficient) (A : C(AddCircle circlePeriod, ℂ)) (hA : ∀ θ : ℝ, A (θ : AddCircle circlePeriod) = a (unitCircleMap θ))

include a A hA in
theorem diskH1Trace_smoothMultiplier
    u :
    diskH1Trace (neumannH1SmoothMultiplier unitDisk a u) =
      boundaryContinuousMultiplier A (diskH1Trace u) := by
  change h1BoundaryTrace isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
    (neumannH1SmoothMultiplier (Metric.ball 0 1) a u) = _
  rw [h1BoundaryTrace_neumannH1SmoothMultiplier unitDisk_bounded]
  simp_all [boundaryContinuousMultiplier] <;> tauto

theorem common_multiplier_toCLM_apply 
     (H : SeqOpBound s t C Φ) b n :
    H.toCLM b n = ((sobWeight n ^ t : ℝ) : ℂ) * Φ (fromL2 s b) n := rfl

include a A hA in
/-- The actual smooth multiplier and its normalized Fourier operator agree
on the genuine disk H¹ half trace, for every input. -/
theorem diskHalfTrace_smoothMultiplier
    (hc : IsWL1 (1 / 2 : ℝ) (fourierCoeff A))
    u :
    diskHalfTrace (neumannH1SmoothMultiplier unitDisk a u) =
      (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM (diskHalfTrace u) := by
  have hsum : Summable (fourierCoeff A) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hc
    intro n
    exact le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_rpow (one_le_sobWeight n) (by norm_num))
  apply lp.ext
  funext n
  have hL : diskHalfTrace
      (neumannH1SmoothMultiplier unitDisk a u) n =
      (Real.sqrt (sobWeight n) : ℂ) *
        seqConv (fourierCoeff A) (boundaryFourier (diskH1Trace u)) n := by
    rw [diskHalfTrace_apply, diskH1Trace_smoothMultiplier a A hA,
      boundaryFourier_continuousMultiplier A hsum]
    simp  [sobWeight]
  have hR  :=
    common_multiplier_toCLM_apply (s := (1 / 2)) (t := (1 / 2))
      (C := wl1Norm (1 / 2) (fourierCoeff A)) (Φ := seqConv (fourierCoeff A))
      (seqOpBound_seqConv (s := (1 / 2)) (c := fourierCoeff A)
        (by norm_num) hc) (diskHalfTrace u) n
  rw [hL, hR, fromL2_half_diskHalfTrace, Real.sqrt_eq_rpow]

end


end PolyaNeumann

end
