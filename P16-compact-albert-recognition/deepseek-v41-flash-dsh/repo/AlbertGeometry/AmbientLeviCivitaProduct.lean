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
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open scoped ContDiff Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Exactly the canonical operator norms; no new norm on native Albert or V.
local instance ambientDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientTrilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientTrilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance ambientEndNorm : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance ambientEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance ambientVectorBilinearNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance ambientVectorBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance ambientInverseNorm : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
local instance ambientInverseSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)

private theorem eval_const_hasFDerivAt
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {f' : X →L[ℝ] Y →L[ℝ] Z} {x : X}
    (hf : HasFDerivAt f f' x) (u : Y) :
    HasFDerivAt (fun y => f y u) (f'.flip u) x := by
  have h := hf.clm_apply (hasFDerivAt_const u x)
  apply h.congr_fderiv
  ext w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add]
variable (P : SymmetricTrilinearForm E)
include P in

/-- Smoothness is proved for the literal log and then its literal derivatives. -/
theorem contDiffAt_actual_log  {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logCubic P) x :=
  (contDiff_diagonalCubic P.form ⊤).contDiffAt.log (ne_of_gt hx)
include P in

theorem contDiffAt_actual_logHessian  {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logHessian P) x := by
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (logCubic P)) x :=
    (contDiffAt_actual_log P hx).fderiv_right (by simp)
  exact hd.fderiv_right (by simp)
include P in

theorem contDiffAt_actual_metric  {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logHessianForm P) x :=
  (contDiffAt_actual_logHessian P hx).const_smul (-1 / 3 : ℝ)
include P in

/-- The derivative of the actual varying ambient metric, never a stored jet. -/
def ambientMetricD1  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (logHessianForm P) x
include P in

theorem hasFDerivAt_actual_metric  {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (logHessianForm P) (ambientMetricD1 P x) x :=
  ((contDiffAt_actual_metric P hx).differentiableAt (by simp)).hasFDerivAt
include P in

/-- Third-derivative Schwarz symmetry swaps the first two metric-jet slots. -/
theorem ambientMetricD1_swap12  {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w : E) :
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
include P in

/-- Symmetry is differentiated on an actual positive neighborhood. -/
theorem ambientMetricD1_swap23  {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w : E) :
    ambientMetricD1 P x u v w = ambientMetricD1 P x u w v := by
  have hG := hasFDerivAt_actual_metric P hx
  have h1 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG v) w
  have h2 := eval_const_hasFDerivAt (eval_const_hasFDerivAt hG w) v
  have hc : (fun y => logHessianForm P y v w) =ᶠ[𝓝 x]
      (fun y => logHessianForm P y w v) :=
    (eventually_positive P hx).mono (fun y hy => logHessianForm_symm P hy v w)
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (h1.unique (h2.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply] using h
include P in

/-- Actual affine-coordinate Koszul tensor, built from the literal metric jet. -/
def ambientKoszulTensor  (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (ambientMetricD1 P x + (ambientMetricD1 P x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
      (ambientMetricD1 P x).flip))
include P in

theorem ambientKoszulTensor_apply  (x u v w : E) :
    ambientKoszulTensor P x u v w =
      (ambientMetricD1 P x u v w + ambientMetricD1 P x v u w -
        ambientMetricD1 P x w u v) / 2 := by
  have hflip :
      ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
        (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
        (ambientMetricD1 P x).flip) u v w = ambientMetricD1 P x w u v := rfl
  simp only [ambientKoszulTensor, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  rw [hflip]
  simp only [ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring
include P in

theorem ambientKoszulTensor_eq_half  {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ambientKoszulTensor P x = (1 / 2 : ℝ) • ambientMetricD1 P x := by
  ext u v w
  rw [ambientKoszulTensor_apply, ambientMetricD1_swap12 P hx v u w,
    ambientMetricD1_swap12 P hx w u v, ambientMetricD1_swap23 P hx u w v]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
include P in

/-- Raise the actual Koszul covector by the actual metric inverse. The total
inverse may be zero off the invertible locus; all laws below prove invertibility. -/
def ambientGamma  (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (logHessianForm P x).inverse).comp (ambientKoszulTensor P x)
include P in

theorem ambientGamma_apply  (x u v : E) :
    ambientGamma P x u v = (logHessianForm P x).inverse
      (ambientKoszulTensor P x u v) := by
  simp only [ambientGamma, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

section FiniteDimension
variable [FiniteDimensional ℝ E]
include P in

theorem actual_metric_dual_injective  (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    Function.Injective (logHessianForm P x) := by
  intro u v huv
  have hzero : logHessianForm P x (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hzero' : logHessianForm P x (u - v) (u - v) = 0 := by rw [hzero]; rfl
  have hz : u - v = 0 := by
    by_contra hne
    have h := hp (u - v) hne
    rw [hzero'] at h
    exact (lt_irrefl 0) h
  exact sub_eq_zero.mp hz
include P in

theorem actual_metric_dual_isInvertible  (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    (logHessianForm P x).IsInvertible := by
  let d : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  letI : FiniteDimensional ℝ (E →L[ℝ] ℝ) := d.finiteDimensional
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans d.finrank_eq
  let A : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
    (LinearEquiv.ofInjectiveOfFinrankEq (logHessianForm P x).toLinearMap
      (actual_metric_dual_injective P x hp) hdim).toContinuousLinearEquiv
  exact ⟨A, rfl⟩
include P in

/-- Actual affine Koszul identity at every positive metric point. -/
theorem ambientGamma_koszul  (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    logHessianForm P x (ambientGamma P x u v) w = ambientKoszulTensor P x u v w := by
  rw [ambientGamma_apply]
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    ((actual_metric_dual_isInvertible P x hp).self_apply_inverse
      (ambientKoszulTensor P x u v))
include P in

/-- Actual adjoint polarization gives the cross pairing before Jordan laws. -/
theorem intrinsicCross_pairing  (e : E)
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
include P in

theorem rawTraceForm_unit_left  (e : E)
    (he : diagonalCubic P.form e = 1) (w : E) :
    rawTraceForm P e e w = normTrace P e w := by
  rw [rawTraceForm_eq_three_logMetric P e he, logHessianForm_radial_at_one P e w he]
  unfold normTrace
  ring
include P in

/-- Exact full-slot product pairing, with rawB=3g and unhalved cross. -/
theorem intrinsicProduct_pairing  (e : E)
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
include P in

/-- Differentiate the proved rational metric identity on its positive
neighborhood. The scalar derivatives and whole CLM derivative agree by uniqueness. -/
theorem ambientMetricD1_at_one  (e : E)
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
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring)
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hG.unique (hs.congr_of_eventuallyEq hc))
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inverseCubicDerivative, fullyCurried_apply,
    smul_eq_mul, Pi.mul_apply, he, one_pow, inv_one, normTrace] at hd ⊢
  rw [hd]
  ring
include P in

/-- The metric cubic jet is DERIVED from actual DN/D2N/D3N, then compared
with the independently reconstructed product. All radial slots are retained. -/
theorem ambientMetricD1_eq_neg_two_product  (e : E)
    (he : diagonalCubic P.form e = 1) (hB : (rawBilinearForm P e).Nondegenerate)
    (u v w : E) :
    ambientMetricD1 P e u v w =
      -2 * logHessianForm P e (intrinsicProduct P e hB u v) w := by
  have hg := rawTraceForm_eq_three_logMetric P e he (intrinsicProduct P e hB u v) w
  rw [intrinsicProduct_pairing P e he hB] at hg
  simp only [intrinsicS, rawTraceForm_apply] at hg
  rw [ambientMetricD1_at_one P e he]
  nlinarith only [hg]
include P in

/-- Actual AMBIENT affine Levi-Civita coefficient at the normalized base.
The product has its real positive-derived nondegeneracy certificate. -/
theorem ambientGamma_at_one_eq_neg_product  (e : E)
    (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) (u v : E) :
    ambientGamma P e u v =
      -intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u v := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  apply actual_metric_dual_injective P e hp
  ext w
  rw [ambientGamma_koszul P e hp, ambientKoszulTensor_eq_half P hN]
  simp only [ContinuousLinearMap.smul_apply, map_neg,
    ContinuousLinearMap.neg_apply, smul_eq_mul]
  rw [ambientMetricD1_eq_neg_two_product P e he
    (rawBilinearForm_nondegenerate P e he hp)]
  ring

end FiniteDimension

section SmoothConnection
variable [CompleteSpace E] [FiniteDimensional ℝ E]
include P in

/-- Genuine smooth connection field on the actual positive-definite locus;
point invertibility and the literal metric derivatives supply its smoothness. -/
theorem contDiffAt_ambientGamma  {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    ContDiffAt ℝ ⊤ (ambientGamma P) x := by
  have hG := contDiffAt_actual_metric P hx
  have hi : ContDiffAt ℝ ⊤ (fun y => (logHessianForm P y).inverse) x :=
    (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (n := ⊤)
      (actual_metric_dual_isInvertible P x hp)).fun_comp x hG
  have hDG : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x := hG.fderiv_right (by simp)
  have hK : ContDiffAt ℝ ⊤ (ambientKoszulTensor P) x :=
    (hDG.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq
      ((eventually_positive P hx).mono (fun y hy => ambientKoszulTensor_eq_half P hy))
  have hleft : ContDiffAt ℝ ⊤
      (fun y => ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
        (logHessianForm P y).inverse) x :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := (E →L[ℝ] ℝ) →L[ℝ] E)
      (F := (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) (n := ⊤)
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)).contDiffAt.fun_comp x hi
  exact hleft.clm_comp hK

end SmoothConnection

section BasedTransport
variable [FiniteDimensional ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
variable {P : SymmetricTrilinearForm E} {e : E}
  {Q : SymmetricTrilinearForm G} {f : G}

end BasedTransport
end
end AlbertGeometry.AmbientLeviCivitaProduct
