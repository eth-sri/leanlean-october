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
public import AlbertGeometry.CubicHessian
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Dual.Lemmas
@[expose] public section
namespace AlbertGeometry.AmbientLeviCivitaProduct
noncomputable section
open Glennie.SubmissionR04Intrinsic
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open scoped ContDiff Topology
open Filter
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- Specialize instance search to real operators, including nested operators.
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
@[implicit_reducible] scoped instance (priority := 1100) realOperatorNorm : NormedAddCommGroup (X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[implicit_reducible] scoped instance (priority := 1100) realOperatorSpace : NormedSpace ℝ (X →L[ℝ] Y) :=
  ContinuousLinearMap.toNormedSpace
end

theorem _root_.HasFDerivAt.clm_apply_const
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {f' : X →L[ℝ] Y →L[ℝ] Z} {x : X}
    (hf : HasFDerivAt f f' x) (u : Y) :
    HasFDerivAt (fun y => f y u) (f'.flip u) x := (ContinuousLinearMap.apply ℝ Z u).hasFDerivAt.comp x hf

/-- Smoothness is proved for the literal log and then its literal derivatives. -/
theorem contDiffAt_actual_log (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) : ContDiffAt ℝ ⊤ (logCubic P) x :=
  (contDiff_diagonalCubic P ⊤).contDiffAt.log (ne_of_gt hx)

theorem contDiffAt_actual_logHessian (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) : ContDiffAt ℝ ⊤ (logHessian P) x :=
  ((contDiffAt_actual_log P hx).fderiv_right (m := ⊤) (by simp)).fderiv_right (by simp)

theorem contDiffAt_actual_metric (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) : ContDiffAt ℝ ⊤ (metric P) x :=
  (contDiffAt_actual_logHessian P hx).const_smul (-1 / 3 : ℝ)

theorem hasFDerivAt_actual_metric (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) :
    HasFDerivAt (metric P) (ambientMetricD1 P x) x :=
  ((contDiffAt_actual_metric P hx).differentiableAt (by simp)).hasFDerivAt

/-- Third-derivative Schwarz symmetry swaps the first two metric-jet slots. -/
theorem ambientMetricD1_swap12 (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x v u w := by
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (logCubic P)) x :=
    (contDiffAt_actual_log P hx).fderiv_right (by simp)
  have hl := (((contDiffAt_actual_logHessian P hx).differentiableAt
    (by simp)).hasFDerivAt.const_smul (-1 / 3 : ℝ)).fderiv
  change ambientMetricD1 P x = (-1 / 3 : ℝ) • fderiv ℝ (logHessian P) x at hl
  rw [hl]
  exact congrArg (fun L : E →L[ℝ] ℝ => (-1 / 3 : ℝ) • L w)
    ((hd.isSymmSndFDerivAt le_top).eq u v)

/-- Symmetry is differentiated on an actual positive neighborhood. -/
theorem ambientMetricD1_swap23 (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x u w v := by
  let hG := hasFDerivAt_actual_metric P hx
  have h1 := (hG.clm_apply_const v).clm_apply_const w
  have h2 := (hG.clm_apply_const w).clm_apply_const v
  have hc : (fun y => metric P y v w) =ᶠ[𝓝 x]
      (fun y => metric P y w v) :=
    (eventually_positive P hx).mono (fun y hy => logHessianForm_symm P hy v w)
  exact DFunLike.congr_fun (h1.unique (h2.congr_of_eventuallyEq hc)) u

theorem ambientKoszulTensor_apply (P : BasedCubic E) (x u v w : E) :
    ambientKoszulTensor P x u v w =
      (ambientMetricD1 P x u v w + ambientMetricD1 P x v u w -
        ambientMetricD1 P x w u v) / 2 := by
  change (1/2 : ℝ) * (ambientMetricD1 P x u v w + ambientMetricD1 P x v u w -
    ambientMetricD1 P x w u v) = _
  ring

theorem ambientKoszulTensor_eq_half (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) :
    ambientKoszulTensor P x = (1 / 2 : ℝ) • ambientMetricD1 P x := by
  ext u v w
  rw [ambientKoszulTensor_apply, ambientMetricD1_swap12 P hx v u w,
    ambientMetricD1_swap12 P hx w u v, ambientMetricD1_swap23 P hx u w v]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem ambientGamma_apply (P : BasedCubic E) (x u v : E) :
    ambientConnection P x u v = (metric P x).inverse
      (ambientKoszulTensor P x u v) := by
  simp only [ambientConnection, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

section FiniteDimension
variable [FiniteDimensional ℝ E]

theorem actual_metric_dual_isInvertible (P : BasedCubic E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P x u u) :
    (metric P x).IsInvertible :=
  dual_isInvertible _ fun u hu => by by_contra h; exact (hp u h).ne' hu

/-- Actual affine Koszul identity at every positive metric point. -/
theorem ambientGamma_koszul (P : BasedCubic E) (x : E)
    (hi : (metric P x).IsInvertible) (u v w : E) :
    metric P x (ambientConnection P x u v) w = ambientKoszulTensor P x u v w := by
  rw [ambientGamma_apply, hi.self_apply_inverse]

/-- Actual adjoint polarization gives the cross pairing before Jordan laws. -/
theorem intrinsicCross_pairing (P : BasedCubic E) (e : E)
    (hB : (rawPair P e).IsInvertible) (u v w : E) :
    rawPair P e (intrinsicCross P e u v) w = 6 * P.form ![u,v,w] := by
  simp only [intrinsicCross, map_sub, sub_apply, intrinsicAdjoint_pairing P e hB,
    fderiv_diagonalCubic_apply_symmetric, ← fullyCurried_apply, map_add, add_apply]
  simp only [fullyCurried_apply, P.swap12 v u w]
  ring

theorem rawTraceForm_unit_left (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (w : E) : rawPair P e e w = traceAt P e w := by
  simp only [rawTraceForm_apply, traceAt, fderiv_diagonalCubic_at_one P e he,
    cubicHessian_apply, fderiv_diagonalCubic_apply_symmetric]
  ring

/-- Exact full-slot product pairing, with rawB=3g and unhalved cross. -/
theorem intrinsicProduct_pairing (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (hB : (rawPair P e).IsInvertible)
    (u v w : E) :
    rawPair P e (product P e u v) w =
      3 * P.form ![u,v,w] + (traceAt P e u * rawPair P e v w +
        traceAt P e v * rawPair P e u w - intrinsicS P e u v * traceAt P e w) / 2 := by
  change rawPair P e ((1 / 2 : ℝ) • (intrinsicCross P e u v + traceAt P e u • v +
    traceAt P e v • u - intrinsicS P e u v • e)) w = _
  simp only [map_smul, map_add, map_sub,
    smul_apply, add_apply,
    sub_apply, smul_eq_mul, intrinsicCross_pairing P e hB,
    rawTraceForm_unit_left P e he]
  ring

/-- The derivative of the rational log-metric formula is the independently
reconstructed product paired against the normalized metric. -/
theorem ambientMetricD1_eq_neg_two_product (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (hB : (rawPair P e).IsInvertible) (u v w : E) :
    ambientMetricD1 P e u v w = -2 * metric P e (product P e u v) w := by
  have hpos : 0 < cubic P e := he ▸ one_pos
  let hN := hasFDerivAt_diagonalCubic P e
  let hD := hasFDerivAt_fderiv_diagonalCubic_actual P e
  have hG := ((hasFDerivAt_actual_metric P hpos).clm_apply_const v).clm_apply_const w
  have hH := ((hasFDerivAt_cubicHessian P e).clm_apply_const v).clm_apply_const w
  have hR := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt e hN
  have hP := (hD.clm_apply_const v).mul (hD.clm_apply_const w)
  have hs := ((hH.mul hR).sub ((hP.mul hR).mul hR)).const_smul (-1 / 3 : ℝ)
  have hd := DFunLike.congr_fun (hG.unique (hs.congr_of_eventuallyEq
    ((eventually_positive P hpos).mono fun y hy => by
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply, smul_eq_mul]
      rw [logHessianForm_apply P hy]
      simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
      ring))) u
  norm_num [hN, hD, he, fullyCurried_apply, traceAt, smul_eq_mul] at hd
  have hg := rawTraceForm_eq_three_logMetric P e he (product P e u v) w
  rw [intrinsicProduct_pairing P e he hB] at hg
  simp only [intrinsicS, rawTraceForm_apply, traceAt] at hg
  linear_combination hd - (2/3 : ℝ) * hg

/-- Actual AMBIENT affine Levi-Civita coefficient at the normalized base.
The product has its real positive-derived nondegeneracy certificate. -/
theorem ambientGamma_at_one_eq_neg_product (P : BasedCubic E) (e : E)
    (he : cubic P e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P e u u) (u v : E) :
    ambientConnection P e u v =
      -product P e u v := by
  have hN : 0 < cubic P e := by rw [he]; norm_num
  apply (actual_metric_dual_isInvertible P e hp).injective
  ext w
  rw [ambientGamma_koszul P e (actual_metric_dual_isInvertible P e hp), ambientKoszulTensor_eq_half P hN]
  simp only [smul_apply, map_neg,
    neg_apply, smul_eq_mul]
  rw [ambientMetricD1_eq_neg_two_product P e he
    (rawTraceForm_isInvertible P e he hp)]
  ring

end FiniteDimension

section SmoothConnection
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Genuine smooth connection field on the actual positive-definite locus;
point invertibility and the literal metric derivatives supply its smoothness. -/
theorem contDiffAt_ambientGamma (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x)
    (hp : ∀ u : E, u ≠ 0 → 0 < metric P x u u) :
    ContDiffAt ℝ ⊤ (ambientConnection P) x := by
  have hG := contDiffAt_actual_metric P hx
  have hi : ContDiffAt ℝ ⊤ (fun y => (metric P y).inverse) x :=
    (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (n := ⊤)
      (actual_metric_dual_isInvertible P x hp)).fun_comp x hG
  have hDG : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x := hG.fderiv_right (by simp)
  have hK : ContDiffAt ℝ ⊤ (ambientKoszulTensor P) x :=
    (hDG.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq
      ((eventually_positive P hx).mono (fun y hy => ambientKoszulTensor_eq_half P hy))
  have hleft := (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).contDiff.contDiffAt.fun_comp x hi
  exact hleft.clm_comp hK

end SmoothConnection

end
end AlbertGeometry.AmbientLeviCivitaProduct
