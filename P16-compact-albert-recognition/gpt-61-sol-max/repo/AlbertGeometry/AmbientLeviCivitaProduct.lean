/-
The ambient affine connection is raised from the
literal derivative of the actual varying metric -D²logN/3. Its Koszul,
torsion, metric and uniqueness laws are proved before comparison with the
independently derivative-defined intrinsic product. No Jordan, invariance,
recognition, trace-of-multiplication or prescribed connection field is input.
This is the AMBIENT affine coefficient; the level-chart coefficient is -K.
-/
module
public import AlbertGeometry.LinearSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Aesop

public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertGeometry.LogHessianPositiveNeighborhood
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section
namespace AlbertGeometry.AmbientLeviCivitaProduct
noncomputable section
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open scoped ContDiff Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)

-- Exactly the canonical operator norms; no new norm on native Albert or V.
real_operator_norms ambientDualNorm ambientDualSpace E ℝ

real_operator_norms ambientBilinearNorm ambientBilinearSpace E (E →L[ℝ] ℝ)

real_operator_norms ambientTrilinearNorm ambientTrilinearSpace E (E →L[ℝ] E →L[ℝ] ℝ)

real_operator_norms ambientEndNorm ambientEndSpace E E

real_operator_norms ambientVectorBilinearNorm ambientVectorBilinearSpace E (E →L[ℝ] E)

real_operator_norms ambientInverseNorm ambientInverseSpace (E →L[ℝ] ℝ) E

variable  {x : E}
    (hx : 0 < diagonalCubic P.form x)

include P x hx in
/-- Smoothness is proved for the literal log and then its literal derivatives. -/
theorem contDiffAt_actual_log  : ContDiffAt ℝ ⊤ (logCubic P) x :=
  (contDiff_diagonalCubic P.form ⊤).contDiffAt.log (ne_of_gt hx)

include P x hx in
theorem contDiffAt_actual_logHessian  : ContDiffAt ℝ ⊤ (logHessian P) x := by
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (logCubic P)) x :=
    (contDiffAt_actual_log P hx).fderiv_right (by simp)
  exact hd.fderiv_right (by simp)

include P x hx in
theorem contDiffAt_actual_metric  : ContDiffAt ℝ ⊤ (logHessianForm P) x :=
  (contDiffAt_actual_logHessian P hx).const_smul (-1 / 3 : ℝ)

/-- The derivative of the actual varying ambient metric, never a stored jet. -/
def ambientMetricD1  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (logHessianForm P) x

include P x hx in
theorem hasFDerivAt_actual_metric  :
    HasFDerivAt (logHessianForm P) (ambientMetricD1 P x) x :=
  ((contDiffAt_actual_metric P hx).differentiableAt (by simp)).hasFDerivAt

include P x hx in
/-- Third-derivative Schwarz symmetry swaps the first two metric-jet slots. -/
theorem ambientMetricD1_swap12  (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x v u w := by
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (logCubic P)) x :=
    (contDiffAt_actual_log P hx).fderiv_right (by simp)
  have hh := ((contDiffAt_actual_logHessian P hx).differentiableAt
    (by simp)).hasFDerivAt.const_smul (-1 / 3 : ℝ)
  have hs := congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((hd.isSymmSndFDerivAt le_top).eq u v)
  change fderiv ℝ (logHessianForm P) x u v w =
    fderiv ℝ (logHessianForm P) x v u w
  have hmetric : fderiv ℝ (logHessianForm P) x =
      (-1 / 3 : ℝ) • fderiv ℝ (logHessian P) x := hh.fderiv
  rw [hmetric]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact congrArg (fun r : ℝ => (-1 / 3 : ℝ) * r) hs

include P x hx in
/-- Symmetry is differentiated on an actual positive neighborhood. -/
theorem ambientMetricD1_swap23  (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x u w v := by
  have hG := hasFDerivAt_actual_metric P hx
  have h1 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG v) w
  have h2 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG w) v
  have hc : (fun y => logHessianForm P y v w) =ᶠ[𝓝 x]
      (fun y => logHessianForm P y w v) :=
    (eventually_positive P hx).mono (fun y hy => logHessianForm_symm P hy v w)
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (h1.unique (h2.congr_of_eventuallyEq hc))
  exact h

/-- Actual affine-coordinate Koszul tensor, built from the literal metric jet. -/
def ambientKoszulTensor  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))

include P x hx in
theorem ambientKoszulTensor_eq_half  :
    ambientKoszulTensor P x = (1 / 2 : ℝ) • ambientMetricD1 P x := by
  ext u v w
  change (1 / 2 : ℝ) * (ambientMetricD1 P x u v w + ambientMetricD1 P x v u w -
    ambientMetricD1 P x w u v) = (1 / 2 : ℝ) * ambientMetricD1 P x u v w
  rw [ambientMetricD1_swap12 P hx v u w,
    ambientMetricD1_swap12 P hx w u v, ambientMetricD1_swap23 P hx u w v]
  ring

/-- Raise the actual Koszul covector by the actual metric inverse. The total
inverse may be zero off the invertible locus; all laws below prove invertibility. -/
def ambientGamma  (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (logHessianForm P x).inverse).comp (ambientKoszulTensor P x)

section FiniteDimension
variable [FiniteDimensional ℝ E]

theorem actual_metric_dual_injective  (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    Function.Injective (logHessianForm P x) := (positiveDualEquiv (logHessianForm P x) hp).injective

theorem actual_metric_dual_isInvertible  (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    (logHessianForm P x).IsInvertible :=
  ⟨positiveDualEquiv (logHessianForm P x) hp, rfl⟩

/-- Actual affine Koszul identity at every positive metric point. -/
theorem ambientGamma_koszul (x : E)
    (hi : (logHessianForm P x).IsInvertible) (u v w : E) :
    logHessianForm P x (ambientGamma P x u v) w = ambientKoszulTensor P x u v w := by
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    (hi.self_apply_inverse (ambientKoszulTensor P x u v))

/-- Exact full-slot product pairing, with rawB=3g and unhalved cross. -/
theorem intrinsicProduct_pairing
    (he : diagonalCubic P.form e = 1) (hB : (rawBilinearForm P e).Nondegenerate)
    (u v w : E) :
    rawTraceForm P e (intrinsicProduct P e hB u v) w =
      3 * P.form ![u,v,w] + (normTrace P e u * rawTraceForm P e v w +
        normTrace P e v * rawTraceForm P e u w - intrinsicS P e u v * normTrace P e w) / 2 := by
  have hr : rawTraceForm P e e w = normTrace P e w := by
    rw [rawTraceForm_eq_three_logMetric P e he, logHessianForm_radial_at_one P e w he]
    unfold normTrace
    ring
  simp only [clm_eval, intrinsicProduct, intrinsicCross, intrinsicAdjoint_pairing,
    fderiv_diagonalCubic_apply_symmetric, hr]
  simp only [← fullyCurried_apply, map_add, ContinuousLinearMap.add_apply]
  simp only [fullyCurried_apply, P.swap12 v u w]
  ring

/-- The metric cubic jet is DERIVED from actual DN/D2N/D3N, then compared
with the independently reconstructed product. All radial slots are retained. -/
theorem ambientMetricD1_eq_neg_two_product
    (he : diagonalCubic P.form e = 1) (hB : (rawBilinearForm P e).Nondegenerate)
    (u v w : E) :
    ambientMetricD1 P e u v w =
      -2 * logHessianForm P e (intrinsicProduct P e hB u v) w := by
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
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring)
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hG.unique (hs.congr_of_eventuallyEq hc))
  simp only [clm_eval, inverseCubicDerivative, fullyCurried_apply, Pi.mul_apply, he, one_pow, inv_one] at hd ⊢

  have hg := rawTraceForm_eq_three_logMetric P e he (intrinsicProduct P e hB u v) w
  rw [intrinsicProduct_pairing P e he hB] at hg
  simp only [intrinsicS, rawTraceForm_apply, normTrace] at hg
  rw [hd]
  nlinarith only [hg]

/-- Actual AMBIENT affine Levi-Civita coefficient at the normalized base.
The product has its real positive-derived nondegeneracy certificate. -/
theorem ambientGamma_at_one_eq_neg_product
    (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) (u v : E) :
    ambientGamma P e u v =
      -intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u v := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  apply actual_metric_dual_injective P e hp
  ext w
  rw [ambientGamma_koszul P e (actual_metric_dual_isInvertible P e hp), ambientKoszulTensor_eq_half P hN]
  simp only [ContinuousLinearMap.smul_apply, map_neg,
    ContinuousLinearMap.neg_apply, smul_eq_mul]
  rw [ambientMetricD1_eq_neg_two_product P e he
    (rawBilinearForm_nondegenerate P e he hp)]
  ring

end FiniteDimension

section SmoothConnection
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Genuine smooth connection field on the actual positive-definite locus;
point invertibility and the literal metric derivatives supply its smoothness. -/
theorem contDiffAt_ambientGamma  {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    ContDiffAt ℝ ⊤ (ambientGamma P) x := by
  have hG := contDiffAt_actual_metric P hx
  have hi : ContDiffAt ℝ ⊤ (fun y => (logHessianForm P y).inverse) x :=
    (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse

      (actual_metric_dual_isInvertible P x hp)).fun_comp x hG
  have hDG : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x := hG.fderiv_right (by simp)
  have hK : ContDiffAt ℝ ⊤ (ambientKoszulTensor P) x :=
    (hDG.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq
      ((eventually_positive P hx).mono (fun y hy => ambientKoszulTensor_eq_half P hy))
  have hleft : ContDiffAt ℝ ⊤
      (fun y => ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
        (logHessianForm P y).inverse) x :=
    (ContinuousLinearMap.contDiff

      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)).contDiffAt.fun_comp x hi
  exact hleft.clm_comp hK

end SmoothConnection


end
end AlbertGeometry.AmbientLeviCivitaProduct
