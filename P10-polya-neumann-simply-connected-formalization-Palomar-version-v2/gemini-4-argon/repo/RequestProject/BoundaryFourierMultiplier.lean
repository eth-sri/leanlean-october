module

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

local instance boundaryMultiplierTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Multiplication by an actual continuous periodic circle function. -/
def boundaryContinuousMultiplier (A : C(AddCircle (2 * Real.pi), ℂ)) :
    BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi)))
    (A.continuous.comp (AddCircle.continuous_mk' _)).aestronglyMeasurable
    (Eventually.of_forall (fun θ => A.norm_coe_le_norm (θ : AddCircle (2 * Real.pi))))

theorem boundaryContinuousMultiplier_ae A
    g :
    (boundaryContinuousMultiplier A g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun θ => A (θ : AddCircle (2 * Real.pi)) * g θ :=
  lpBoundedMultiplier_ae (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi)))
    (A.continuous.comp (AddCircle.continuous_mk' _)).aestronglyMeasurable
    (Eventually.of_forall (fun θ => A.norm_coe_le_norm (θ : AddCircle (2 * Real.pi)))) g

theorem boundaryFourier_eq_sqrt_mul_circleLift g n :
    boundaryFourier g n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeff (boundaryCircleLift g) n := by
  rw [boundaryFourier_apply,
    fourierCoeff_congr_ae (boundaryCircleLift_coe g), fourierCoeff_liftIoc_eq]
  simp

/-- Exact convolution for arbitrary actual boundary L² input. -/
theorem boundaryFourier_continuousMultiplier (A : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable (fourierCoeff A)) g n :
    boundaryFourier (boundaryContinuousMultiplier A g) n =
      seqConv (fourierCoeff A) (boundaryFourier g) n := by
  rw [boundaryFourier_eq_sqrt_mul_circleLift, show fourierCoeff (boundaryCircleLift (boundaryContinuousMultiplier A g)) = seqConv (fourierCoeff A) (fourierCoeff (boundaryCircleLift g)) by
    rw [fourierCoeff_congr_ae (show boundaryCircleLift (boundaryContinuousMultiplier A g) =ᵐ[AddCircle.haarAddCircle] fun q => A q * boundaryCircleLift g q by
      filter_upwards [boundaryCircleLift_coe (boundaryContinuousMultiplier A g),
        boundary_liftIoc_congr_ae (boundaryContinuousMultiplier_ae A g),
        boundaryCircleLift_coe g] with q hm hl hg
      rw [hm, hl, hg]
      change A (AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) *
        AddCircle.liftIoc (2 * Real.pi) 0 g q = _
      have hrep : (AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) = q :=
        (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
      rw [hrep])]
    exact fourierCoeff_mul_eq_seqConv A hA ((Lp.memLp (boundaryCircleLift g)).integrable (by norm_num : (1 : ENNReal) ≤ 2))]
  unfold seqConv
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [boundaryFourier_eq_sqrt_mul_circleLift]
  ring

/-- Removing the actual half-trace weight gives the ordinary orthonormal
Fourier coefficients. Their square-root-of-2π normalization is retained. -/
theorem fromL2_half_diskHalfTrace u :
    fromL2 (1 / 2) (diskHalfTrace u) = boundaryFourier (diskH1Trace u) := by
  funext n
  rw [fromL2, diskHalfTrace_apply]
  change (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
    ((Real.sqrt (sobWeight n)) * boundaryFourier (diskH1Trace u) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, show sobWeight n ^ (-(1 / 2 : ℝ)) * Real.sqrt (sobWeight n) = 1 by
    rw [Real.sqrt_eq_rpow, mul_comm, sobWeight_rpow_mul_neg]]
  simp

theorem diskH1Trace_smoothMultiplier a
    A
    (hA : ∀ θ : ℝ, A θ = a (circleMap 0 1 θ))
    u :
    diskH1Trace (neumannH1SmoothMultiplier (Metric.ball 0 1) a u) =
      boundaryContinuousMultiplier A (diskH1Trace u) := by
  change h1BoundaryTrace unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
    (neumannH1SmoothMultiplier (Metric.ball 0 1) a u) = _
  rw [h1BoundaryTrace_neumannH1SmoothMultiplier]
  change h1SmoothBoundaryMultiplier unitCircle_isBoundaryParam a (diskH1Trace u) = _
  apply Lp.ext
  filter_upwards [h1SmoothBoundaryMultiplier_ae unitCircle_isBoundaryParam a (diskH1Trace u),
    boundaryContinuousMultiplier_ae A (diskH1Trace u)] with θ hs hc
  rw [hs, hc, hA θ]

private theorem multiplier_toCLM_apply {s t C : ℝ}
     (H : SeqOpBound s t C Φ) b n :
    H.toCLM b n = ((sobWeight n ^ t : ℝ) : ℂ) * Φ (fromL2 s b) n := rfl

/-- The actual smooth multiplier and its normalized Fourier operator agree
on the genuine disk H¹ half trace, for every input. -/
theorem diskHalfTrace_smoothMultiplier (a : SmoothH1Coefficient)
    (A : C(AddCircle (2 * Real.pi), ℂ))
    (hA : ∀ θ : ℝ, A (θ : AddCircle (2 * Real.pi)) = a (circleMap 0 1 θ))
    (hc : IsWL1 (1 / 2) (fourierCoeff A))
    (u : NeumannH1 (Metric.ball 0 1)) :
    diskHalfTrace (neumannH1SmoothMultiplier (Metric.ball (0 : ℂ) 1) a u) =
      (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM (diskHalfTrace u) := by
  apply lp.ext
  funext n
  rw [show diskHalfTrace (neumannH1SmoothMultiplier (Metric.ball 0 1) a u) n = Real.sqrt (sobWeight n) * seqConv (fourierCoeff A) (boundaryFourier (diskH1Trace u)) n by
    rw [diskHalfTrace_apply, diskH1Trace_smoothMultiplier a A hA,
      boundaryFourier_continuousMultiplier A (by
        apply Summable.of_norm
        apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hc
        intro n
        exact le_mul_of_one_le_left (norm_nonneg _)
          (Real.one_le_rpow (one_le_sobWeight n) (by norm_num : (0 : ℝ) ≤ 1 / 2)))]
    simp [sobWeight], multiplier_toCLM_apply (s := (1 / 2)) (t := (1 / 2)) (C := wl1Norm (1 / 2) (fourierCoeff A)) (Φ := seqConv (fourierCoeff A)) (seqOpBound_seqConv (s := (1 / 2)) (c := fourierCoeff A) (by norm_num : (0 : ℝ) ≤ 1 / 2) hc) (diskHalfTrace u) n, fromL2_half_diskHalfTrace, Real.sqrt_eq_rpow]

end PolyaNeumann

end
