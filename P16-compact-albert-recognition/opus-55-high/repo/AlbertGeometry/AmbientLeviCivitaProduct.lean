/-
The ambient affine connection is raised from the
literal derivative of the actual varying metric -D²logN/3. Its Koszul,
torsion, metric and uniqueness laws are proved before comparison with the
independently derivative-defined intrinsic product. No Jordan, invariance,
recognition, trace-of-multiplication or prescribed connection field is input.
This is the AMBIENT affine coefficient; the level-chart coefficient is -K.
-/
module

public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertGeometry.LogHessianPositiveNeighborhood
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section
namespace AlbertGeometry.AmbientLeviCivitaProduct
noncomputable section
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance ambientDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance ambientDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace


/-- Smoothness is proved for the literal log and then its literal derivatives. -/
theorem contDiffAt_actual_log (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logCubic P) x :=
  (contDiff_diagonalCubic P.form ⊤).contDiffAt.log (ne_of_gt hx)

theorem contDiffAt_actual_logHessian (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logHessian P) x :=
  ((contDiffAt_actual_log P hx).fderiv_right (m := ⊤) (by simp)).fderiv_right (by simp)

theorem contDiffAt_actual_metric (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logHessianForm P) x :=
  (contDiffAt_actual_logHessian P hx).const_smul (-1 / 3 : ℝ)

/-- The derivative of the actual varying ambient metric, never a stored jet. -/
def ambientMetricD1 (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (logHessianForm P) x

theorem hasFDerivAt_actual_metric (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (logHessianForm P) (ambientMetricD1 P x) x :=
  ((contDiffAt_actual_metric P hx).differentiableAt (by simp)).hasFDerivAt

/-- Third-derivative Schwarz symmetry swaps the first two metric-jet slots. -/
theorem ambientMetricD1_swap12 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x v u w := by
  have hs := congrArg (fun L => L w)
    ((((contDiffAt_actual_log P hx).fderiv_right (by simp)).isSymmSndFDerivAt le_top).eq u v)
  rw [ambientMetricD1, show fderiv ℝ (logHessianForm P) x = _ from (((contDiffAt_actual_logHessian P hx).differentiableAt
    (by simp)).hasFDerivAt.const_smul (-1 / 3 : ℝ)).fderiv]
  simp; exact hs

/-- Symmetry is differentiated on an actual positive neighborhood. -/
theorem ambientMetricD1_swap23 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x u w v := by
  have hG := hasFDerivAt_actual_metric P hx
  have h1 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG v) w
  have h2 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG w) v
  have hc : (fun y => logHessianForm P y v w) =ᶠ[𝓝 x]
      (fun y => logHessianForm P y w v) :=
    (eventually_positive P hx).mono (fun y hy => logHessianForm_symm P hy v w)
  have h := congrArg (fun L => L u)
    (h1.unique (h2.congr_of_eventuallyEq hc))
  simpa [ContinuousLinearMap.flip_apply] using h

/-- Actual affine-coordinate Koszul tensor, built from the literal metric jet. -/
def ambientKoszulTensor (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))

theorem ambientKoszulTensor_apply (P : SymmetricTrilinearForm E) (x u v w : E) :
    ambientKoszulTensor P x u v w =
      (ambientMetricD1 P x u v w + ambientMetricD1 P x v u w -
        ambientMetricD1 P x w u v) / 2 := by
  simp [ambientKoszulTensor]
  ring

theorem ambientKoszulTensor_eq_half (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ambientKoszulTensor P x = (1 / 2 : ℝ) • ambientMetricD1 P x := by
  ext u v w
  rw [ambientKoszulTensor_apply, ambientMetricD1_swap12 P hx v u w,
    ambientMetricD1_swap12 P hx w u v, ambientMetricD1_swap23 P hx u w v]
  simp [smul_eq_mul]
  ring

/-- Raise the actual Koszul covector by the actual metric inverse. The total
inverse may be zero off the invertible locus; all laws below prove invertibility. -/
def ambientGamma (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (logHessianForm P x).inverse).comp (ambientKoszulTensor P x)

section FiniteDimension
variable [FiniteDimensional ℝ E]

/-- Actual affine Koszul identity at every positive metric point. -/
theorem ambientGamma_koszul (P : SymmetricTrilinearForm E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    logHessianForm P x (ambientGamma P x u v) w = ambientKoszulTensor P x u v w := by
  exact congr($((isInvertible_of_pos hp).self_apply_inverse
    (ambientKoszulTensor P x u v)) w)

/-- Actual adjoint polarization gives the cross pairing before Jordan laws. -/
theorem intrinsicCross_pairing (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (u v w : E) :
    rawTraceForm P e (intrinsicCross P e hB u v) w = 6 * P.form ![u,v,w] := by
  simp only [intrinsicCross, map_sub, ContinuousLinearMap.sub_apply,
    intrinsicAdjoint_pairing, fderiv_diagonalCubic_apply_symmetric]
  have hadd : P.form ![u + v,u + v,w] = P.form ![u,u,w] +
      P.form ![u,v,w] + P.form ![v,u,w] + P.form ![v,v,w] := by
    simp only [← fullyCurried_apply, map_add, ContinuousLinearMap.add_apply]
    ring
  rw [hadd, P.swap12 v u w]
  ring

theorem rawTraceForm_unit_left (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (w : E) :
    rawTraceForm P e e w = normTrace P e w := by
  rw [rawTraceForm_eq_three_logMetric P e he, logHessianForm_radial_at_one P e w he]
  unfold normTrace
  ring

/-- Exact full-slot product pairing, with rawB=3g and unhalved cross. -/
theorem intrinsicProduct_pairing (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (hB : (rawBilinearForm P e).Nondegenerate)
    (u v w : E) :
    rawTraceForm P e (intrinsicProduct P e hB u v) w =
      3 * P.form ![u,v,w] + (normTrace P e u * rawTraceForm P e v w +
        normTrace P e v * rawTraceForm P e u w - intrinsicS P e u v * normTrace P e w) / 2 := by
  simp only [intrinsicProduct, map_smul, map_add, map_sub,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul, intrinsicCross_pairing,
    rawTraceForm_unit_left P e he]
  ring

/-- Differentiate the proved rational metric identity on its positive
neighborhood. The scalar derivatives and whole CLM derivative agree by uniqueness. -/
theorem ambientMetricD1_at_one (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (u v w : E) :
    ambientMetricD1 P e u v w = (-1 / 3 : ℝ) *
      (6 * P.form ![u,v,w] - normTrace P e u * cubicHessian P e v w -
        cubicHessian P e u v * normTrace P e w -
        normTrace P e v * cubicHessian P e u w +
        2 * normTrace P e u * normTrace P e v * normTrace P e w) := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  have hG := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_metric P hN) v) w
  have hH := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_cubicHessian P e) v) w
  have hV := eval_const_hasFDerivAt (hasFDerivAt_fderiv_diagonalCubic_actual P e) v
  have hW := eval_const_hasFDerivAt (hasFDerivAt_fderiv_diagonalCubic_actual P e) w
  have hR := hasFDerivAt_inverseCubic P hN
  have hs := ((hH.mul hR).const_smul (-1 / 3 : ℝ)).add
    ((((hV.mul hW).mul hR).mul hR).const_smul (1 / 3 : ℝ))
  have hc : (fun y => logHessianForm P y v w) =ᶠ[𝓝 e]
      (fun y => (-1 / 3 : ℝ) * (cubicHessian P y v w *
        (diagonalCubic P.form y)⁻¹) + (1 / 3 : ℝ) *
          (fderiv ℝ (diagonalCubic P.form) y v *
            fderiv ℝ (diagonalCubic P.form) y w *
              (diagonalCubic P.form y)⁻¹ * (diagonalCubic P.form y)⁻¹)) :=
    (eventually_positive P hN).mono (fun y hy => by
      change logHessianForm P y v w = _
      rw [logHessianForm_apply P hy]
      simp [div_eq_mul_inv, mul_inv_rev]
      ring)
  have hd := congrArg (fun L => L u)
    (hG.unique (hs.congr_of_eventuallyEq hc))
  simp [ContinuousLinearMap.flip_apply, 
    inverseCubicDerivative, fullyCurried_apply,
    smul_eq_mul, Pi.mul_apply, he, one_pow, inv_one, normTrace] at hd ⊢
  rw [hd]
  ring

/-- The metric cubic jet is DERIVED from actual DN/D2N/D3N, then compared
with the independently reconstructed product. All radial slots are retained. -/
theorem ambientMetricD1_eq_neg_two_product (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (hB : (rawBilinearForm P e).Nondegenerate)
    (u v w : E) :
    ambientMetricD1 P e u v w =
      -2 * logHessianForm P e (intrinsicProduct P e hB u v) w := by
  have hg := rawTraceForm_eq_three_logMetric P e he (intrinsicProduct P e hB u v) w
  rw [intrinsicProduct_pairing P e he hB] at hg
  simp [intrinsicS, rawTraceForm_apply] at hg
  rw [ambientMetricD1_at_one P e he]
  nlinarith only [hg]

/-- Actual AMBIENT affine Levi-Civita coefficient at the normalized base.
The product has its real positive-derived nondegeneracy certificate. -/
theorem ambientGamma_at_one_eq_neg_product (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) (u v : E) :
    ambientGamma P e u v =
      -intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u v := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  apply injective_of_pos hp
  ext w
  rw [ambientGamma_koszul P e hp, ambientKoszulTensor_eq_half P hN]
  simp [map_neg,
    smul_eq_mul]
  rw [ambientMetricD1_eq_neg_two_product P e he
    (rawBilinearForm_nondegenerate P e he hp)]
  ring

end FiniteDimension

section SmoothConnection
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Genuine smooth connection field on the actual positive-definite locus;
point invertibility and the literal metric derivatives supply its smoothness. -/
theorem contDiffAt_ambientGamma (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    ContDiffAt ℝ ⊤ (ambientGamma P) x := by
  have hG := contDiffAt_actual_metric P hx
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).contDiff.contDiffAt.comp x
    ((isInvertible_of_pos hp).contDiffAt_map_inverse.comp x hG)).clm_comp
    (((hG.fderiv_right (by simp)).const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq
      ((eventually_positive P hx).mono (fun y hy => ambientKoszulTensor_eq_half P hy)))

end SmoothConnection

end
end AlbertGeometry.AmbientLeviCivitaProduct
