module

public import AlbertGeometry.BasedNormAdjointTransport
public import AlbertRecognition.CubicFiber
public import Glennie.BasicLaws
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section
namespace AlbertGeometry.NativeNormAlgebra
noncomputable section
open Glennie

/-- Literal Newton cubic expression using the actual native binary product and
raw trace pairing. No octonion or matrix associativity is invoked. -/
def nativeNewtonNorm (x : Albert) : ℝ :=
  (Glennie.trace x ^ 3 - 3 * Glennie.trace x * Glennie.inner x x +
    2 * Glennie.inner x (jordan x x)) / 6

/-- Literal quadratic algebraic expression; its derivative interpretation is
not part of this module. -/
def nativeAdjoint (x : Albert) : Albert :=
  jordan x x - Glennie.trace x • x +
    ((Glennie.trace x ^ 2 - Glennie.inner x x) / 2) • (1 : Albert)

/-- Unhalved polarization of the literal quadratic expression. -/
def nativeCross (x y : Albert) : Albert :=
  nativeAdjoint (x + y) - nativeAdjoint x - nativeAdjoint y

/-- The norm/unit reconstruction formula, using raw B(x,y)=inner(x,y). -/
def nativeRecoveredProduct (x y : Albert) : Albert :=
  (1 / 2 : ℝ) • (nativeCross x y + Glennie.trace y • x +
    Glennie.trace x • y -
    (Glennie.trace x * Glennie.trace y - Glennie.inner x y) • (1 : Albert))

/-- The exact finite polynomial on any native affine line. -/
theorem nativeNewtonNorm_line (x y : Albert) (t : ℝ) :
    nativeNewtonNorm (x + t • y) = nativeNewtonNorm x +
      t * Glennie.inner (nativeAdjoint x) y +
      t ^ 2 * Glennie.inner (nativeAdjoint y) x + t ^ 3 * nativeNewtonNorm y := by
  simp only [nativeNewtonNorm, nativeAdjoint, trace_add, trace_smul,
    jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
    inner_add_left, inner_add_right, inner_sub_left,
    inner_smul_left, inner_smul_right, inner_unit_left]
  simp only [jordan_comm y x, inner_comm y x,
    inner_comm y (jordan x x), inner_comm x (jordan y y),
    inner_jordan_associative x x y, inner_jordan_associative y y x]
  ring

/-- Actual unhalved polarization, derived solely from native bilinearity. -/
theorem nativeCross_eq (x y : Albert) :
    nativeCross x y = (2 : ℝ) • jordan x y - Glennie.trace y • x -
      Glennie.trace x • y +
      (Glennie.trace x * Glennie.trace y - Glennie.inner x y) • (1 : Albert) := by
  simp only [nativeCross, nativeAdjoint, trace_add, jordan_add_left,
    jordan_add_right, inner_add_left, inner_add_right,
    jordan_comm y x, inner_comm y x]
  module

/-- The reconstructed binary product is literally the compact native Jordan product. -/
theorem nativeRecoveredProduct_eq (x y : Albert) :
    nativeRecoveredProduct x y = jordan x y := by
  simp only [nativeRecoveredProduct, nativeCross_eq]
  module

end
end AlbertGeometry.NativeNormAlgebra

namespace AlbertGeometry.AmbientLeviCivitaProduct
noncomputable section
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open scoped ContDiff Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

theorem eval_const_hasFDerivAt
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

/-- Smoothness is proved for the literal log and then its literal derivatives. -/
theorem contDiffAt_actual_log (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logCubic P) x :=
  (contDiff_diagonalCubic P.form ⊤).contDiffAt.log (ne_of_gt hx)

theorem contDiffAt_actual_logHessian (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) : ContDiffAt ℝ ⊤ (logHessian P) x := by
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (logCubic P)) x :=
    (contDiffAt_actual_log P hx).fderiv_right (by simp)
  exact hd.fderiv_right (by simp)

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
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (h1.unique (h2.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply] using h

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
  have hflip :
      ((((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
        (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ).comp
        (ambientMetricD1 P x).flip) u v w = ambientMetricD1 P x w u v := rfl
  simp only [ambientKoszulTensor, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  rw [hflip]
  simp only [ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

theorem ambientKoszulTensor_eq_half (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ambientKoszulTensor P x = (1 / 2 : ℝ) • ambientMetricD1 P x := by
  ext u v w
  rw [ambientKoszulTensor_apply, ambientMetricD1_swap12 P hx v u w,
    ambientMetricD1_swap12 P hx w u v, ambientMetricD1_swap23 P hx u w v]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Raise the actual Koszul covector by the actual metric inverse. -/
def ambientGamma (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
    (logHessianForm P x).inverse).comp (ambientKoszulTensor P x)

theorem ambientGamma_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    ambientGamma P x u v = (logHessianForm P x).inverse
      (ambientKoszulTensor P x u v) := by
  simp only [ambientGamma, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]

theorem ambientGamma_koszul_of_isInvertible (P : SymmetricTrilinearForm E) {x : E}
    (hinv : (logHessianForm P x).IsInvertible) (u v w : E) :
    logHessianForm P x (ambientGamma P x u v) w = ambientKoszulTensor P x u v w := by
  rw [ambientGamma_apply]
  exact congrArg (fun L : E →L[ℝ] ℝ => L w)
    (hinv.self_apply_inverse (ambientKoszulTensor P x u v))

section FiniteDimension
variable [FiniteDimensional ℝ E]

theorem actual_metric_dual_injective (P : SymmetricTrilinearForm E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    Function.Injective (logHessianForm P x) := by
  intro u v huv
  have hzero : logHessianForm P x (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hzero' : logHessianForm P x (u - v) (u - v) = 0 := by rw [hzero]; rfl
  have hz : u - v = 0 := by
    by_contra hne
    exact (lt_irrefl 0) (hzero' ▸ hp (u - v) hne)
  exact sub_eq_zero.mp hz

theorem actual_metric_dual_isInvertible (P : SymmetricTrilinearForm E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    (logHessianForm P x).IsInvertible := by
  let d : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  letI : FiniteDimensional ℝ (E →L[ℝ] ℝ) := d.finiteDimensional
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans d.finrank_eq
  exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq (logHessianForm P x).toLinearMap
    (actual_metric_dual_injective P x hp) hdim).toContinuousLinearEquiv, rfl⟩

/-- Actual affine Koszul identity at every positive metric point. -/
theorem ambientGamma_koszul (P : SymmetricTrilinearForm E) (x : E)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    logHessianForm P x (ambientGamma P x u v) w = ambientKoszulTensor P x u v w :=
  ambientGamma_koszul_of_isInvertible P (actual_metric_dual_isInvertible P x hp) u v w

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
  unfold normTrace; ring

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

/-- Differentiate the proved rational metric identity on its positive neighborhood. -/
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
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring)
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hG.unique (hs.congr_of_eventuallyEq hc))
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inverseCubicDerivative, fullyCurried_apply,
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
  simp only [intrinsicS, rawTraceForm_apply] at hg
  rw [ambientMetricD1_at_one P e he]
  nlinarith only [hg]

/-- Actual AMBIENT affine Levi-Civita coefficient at the normalized base. -/
theorem ambientGamma_at_one_eq_neg_product (P : SymmetricTrilinearForm E) (e : E)
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

/-- Genuine smooth connection field on the actual positive-definite locus. -/
theorem contDiffAt_ambientGamma (P : SymmetricTrilinearForm E) {x : E}
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

/-- Literal second derivative of the actual varying ambient metric. -/
def ambientMetricD2 (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (ambientMetricD1 P) x

theorem hasFDerivAt_actual_metricD1 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (ambientMetricD1 P) (ambientMetricD2 P x) x := by
  have hD1 : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x :=
    (contDiffAt_actual_metric P hx).fderiv_right (by simp)
  exact (hD1.differentiableAt (by simp)).hasFDerivAt

/-- Fourth-derivative cancellation is an actual Schwarz theorem for g. -/
theorem ambientMetricD2_swap12 (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v w z : E) :
    ambientMetricD2 P x u v w z = ambientMetricD2 P x v u w z :=
  congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L w z)
    (((contDiffAt_actual_metric P hx).isSymmSndFDerivAt le_top).eq u v)

/-- The genuine derivative of the smooth actual connection coefficient. -/
def ambientGammaD1 (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fderiv ℝ (ambientGamma P) x

theorem hasFDerivAt_actual_ambientGamma (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) :
    HasFDerivAt (ambientGamma P) (ambientGammaD1 P x) x :=
  ((contDiffAt_ambientGamma P hx hp).differentiableAt (by simp)).hasFDerivAt

/-- The actual connection on a field in a constant affine direction. -/
def ambientCovariantDerivative (P : SymmetricTrilinearForm E) (u : E)
    (Y : E → E) (x : E) : E := fderiv ℝ Y x u + ambientGamma P x u (Y x)

theorem ambientCovariantDerivative_const (P : SymmetricTrilinearForm E) (u w x : E) :
    ambientCovariantDerivative P u (fun _ : E => w) x = ambientGamma P x u w := by
  simp only [ambientCovariantDerivative, fderiv_const_apply,
    ContinuousLinearMap.zero_apply, zero_add]

/-- Actual covariant-derivative commutator on constant affine fields. -/
def ambientCurvature (P : SymmetricTrilinearForm E) (x u v w : E) : E :=
  ambientCovariantDerivative P u (ambientCovariantDerivative P v (fun _ : E => w)) x -
    ambientCovariantDerivative P v (ambientCovariantDerivative P u (fun _ : E => w)) x

/-- The actual constant-field curvature has its actual D-Gamma expression. -/
theorem ambientCurvature_apply (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    ambientCurvature P x u v w =
      ambientGammaD1 P x u v w - ambientGammaD1 P x v u w +
        ambientGamma P x u (ambientGamma P x v w) -
          ambientGamma P x v (ambientGamma P x u w) := by
  have hΓ := hasFDerivAt_actual_ambientGamma P hx hp
  have hv := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ v) w
  have hu := eval_const_hasFDerivAt (eval_const_hasFDerivAt hΓ u) w
  have fv : ambientCovariantDerivative P v (fun _ : E => w) =
      (fun y => ambientGamma P y v w) :=
    funext (fun y => ambientCovariantDerivative_const P v w y)
  have fu : ambientCovariantDerivative P u (fun _ : E => w) =
      (fun y => ambientGamma P y u w) :=
    funext (fun y => ambientCovariantDerivative_const P u w y)
  rw [ambientCurvature, fv, fu]
  simp only [ambientCovariantDerivative, hv.fderiv, hu.fderiv,
    ContinuousLinearMap.flip_apply]
  abel

/-- The Hessian metric has Dg=2g(Gamma(.,.),.) at every positive metric point. -/
theorem ambientMetricD1_eq_two_Gamma (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    ambientMetricD1 P x u v w =
      2 * logHessianForm P x (ambientGamma P x u v) w := by
  have h := ambientGamma_koszul P x hp u v w
  rw [ambientKoszulTensor_eq_half P hx] at h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  linarith

/-- Differentiate actual Koszul pairing on a proved invertible positive neighborhood. -/
theorem ambientGammaD1_pairing (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w z : E) :
    logHessianForm P x (ambientGammaD1 P x u v w) z =
      (1 / 2 : ℝ) * ambientMetricD2 P x u v w z -
        ambientMetricD1 P x u (ambientGamma P x v w) z := by
  have hG := hasFDerivAt_actual_metric P hx
  have hΓ := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_ambientGamma P hx hp) v) w
  have hpair := eval_const_hasFDerivAt (hG.clm_apply hΓ) z
  have hjet := eval_const_hasFDerivAt (eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_actual_metricD1 P hx) v) w) z
  have hinv : ∀ᶠ y in 𝓝 x, (logHessianForm P y).IsInvertible :=
    hG.continuousAt.eventually (actual_metric_dual_isInvertible P x hp).eventually_nhds
  have hc : (fun y => logHessianForm P y (ambientGamma P y v w) z) =ᶠ[𝓝 x]
      (fun y => (1 / 2 : ℝ) * ambientMetricD1 P y v w z) :=
    ((eventually_positive P hx).and hinv).mono fun y ⟨hy, hi⟩ => by
      change logHessianForm P y (ambientGamma P y v w) z =
        (1 / 2 : ℝ) * ambientMetricD1 P y v w z
      rw [ambientGamma_koszul_of_isInvertible P hi, ambientKoszulTensor_eq_half P hy]
      rfl
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L u)
    (hpair.unique ((hjet.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq hc))
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hd
  linarith

/-- Actual Hessian curvature is the negative connection commutator at every
positive metric point. -/
theorem ambientCurvature_eq_neg_Gamma_commutator (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P x u u) (u v w : E) :
    ambientCurvature P x u v w =
      -(ambientGamma P x u (ambientGamma P x v w) -
        ambientGamma P x v (ambientGamma P x u w)) := by
  apply actual_metric_dual_injective P x hp
  ext z
  rw [ambientCurvature_apply P hx hp]
  simp only [map_sub, map_add, map_neg, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
  rw [ambientGammaD1_pairing P hx hp u v w z,
    ambientGammaD1_pairing P hx hp v u w z,
    ambientMetricD2_swap12 P hx u v w z,
    ambientMetricD1_eq_two_Gamma P hx hp u (ambientGamma P x v w) z,
    ambientMetricD1_eq_two_Gamma P hx hp v (ambientGamma P x u w) z]
  ring

/-- Original arbitrary-cubic full ambient tensor endpoint, before Jordan. -/
theorem ambientCurvature_at_one_eq_neg_product_commutator
    (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
    (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) (u v w : E) :
    ambientCurvature P e u v w =
      -(intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u
          (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v w) -
        intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) v
          (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) u w)) := by
  have hx : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  rw [ambientCurvature_eq_neg_Gamma_commutator P hx hp,
    ambientGamma_at_one_eq_neg_product P e he hp v w, map_neg,
    ambientGamma_at_one_eq_neg_product P e he hp, neg_neg,
    ambientGamma_at_one_eq_neg_product P e he hp u w, map_neg,
    ambientGamma_at_one_eq_neg_product P e he hp, neg_neg]

end SmoothConnection
end
end AlbertGeometry.AmbientLeviCivitaProduct

namespace AlbertGeometry.RecognitionFromCurvature
noncomputable section
open Module Glennie AlbertRecognition
open AlbertGeometry.Cubic
open AlbertGeometry.NativeNormAlgebra
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.AmbientLeviCivitaProduct

set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)

def tangentSpace : Submodule ℝ E := (fderiv ℝ (diagonalCubic P.form) e).ker

def tangentProjectionRaw : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (1 / 3 : ℝ) •
    (ContinuousLinearMap.toSpanSingleton ℝ e).comp (fderiv ℝ (diagonalCubic P.form) e)

@[simp] theorem tangentProjectionRaw_apply (x : E) :
    tangentProjectionRaw P e x = x - (fderiv ℝ (diagonalCubic P.form) e x / 3) • e := by
  simp only [tangentProjectionRaw, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_smul, div_eq_mul_inv]
  congr 2; ring

theorem tangentProjectionRaw_mem (he : diagonalCubic P.form e = 1) (x : E) :
    tangentProjectionRaw P e x ∈ tangentSpace P e := by
  change fderiv ℝ (diagonalCubic P.form) e (tangentProjectionRaw P e x) = 0
  rw [tangentProjectionRaw_apply, map_sub, map_smul, fderiv_diagonalCubic_at_one P.form e he]
  simp only [smul_eq_mul]; ring

def tangentProjection (he : diagonalCubic P.form e = 1) : E →L[ℝ] tangentSpace P e :=
  (tangentProjectionRaw P e).codRestrict (tangentSpace P e) (tangentProjectionRaw_mem P e he)

@[simp] theorem tangentProjection_coe (he : diagonalCubic P.form e = 1) (x : E) :
    (tangentProjection P e he x : E) = x - (fderiv ℝ (diagonalCubic P.form) e x / 3) • e :=
  tangentProjectionRaw_apply P e x

@[simp] theorem tangentProjection_basepoint (he : diagonalCubic P.form e = 1) :
    tangentProjection P e he e = 0 := by
  apply Subtype.ext
  simp only [tangentProjection_coe, fderiv_diagonalCubic_at_one P.form e he,
    div_self (by norm_num : (3 : ℝ) ≠ 0), one_smul, sub_self, ZeroMemClass.coe_zero]

def normalSplitInverse (p : ℝ × tangentSpace P e) : E := (p.1 / 3) • e + p.2

theorem normalSplit_left_inverse (he : diagonalCubic P.form e = 1) (x : E) :
    normalSplitInverse P e (fderiv ℝ (diagonalCubic P.form) e x, tangentProjection P e he x) = x := by
  simp only [normalSplitInverse, tangentProjection_coe]; module

theorem normalSplit_right_inverse (he : diagonalCubic P.form e = 1) (p : ℝ × tangentSpace P e) :
    (fderiv ℝ (diagonalCubic P.form) e (normalSplitInverse P e p),
      tangentProjection P e he (normalSplitInverse P e p)) = p := by
  have hv : fderiv ℝ (diagonalCubic P.form) e (p.2 : E) = 0 := p.2.property
  have hn : fderiv ℝ (diagonalCubic P.form) e (normalSplitInverse P e p) = p.1 := by
    simp only [normalSplitInverse, map_add, map_smul,
      fderiv_diagonalCubic_at_one P.form e he, hv, smul_eq_mul]
    ring
  apply Prod.ext hn
  apply Subtype.ext
  rw [tangentProjection_coe, hn]
  simp only [normalSplitInverse]; module

local instance tangentDualNorm : NormedAddCommGroup (tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := tangentSpace P e) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentDualSpace : NormedSpace ℝ (tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := tangentSpace P e) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentBilinearSpace : NormedSpace ℝ (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := tangentSpace P e) (F := tangentSpace P e →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance tangentEndSpace : NormedSpace ℝ (tangentSpace P e →L[ℝ] tangentSpace P e) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := tangentSpace P e) (F := tangentSpace P e) (σ₁₂ := RingHom.id ℝ)

def baseChartMetric : tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  (logHessianForm P e).bilinearComp (tangentSpace P e).subtypeL (tangentSpace P e).subtypeL

def tangentCubicForm : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => tangentSpace P e) ℝ :=
  P.form.compContinuousLinearMap (fun _ : Fin 3 => (tangentSpace P e).subtypeL)

def tangentCubicCurried :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  (((continuousMultilinearCurryFin1 ℝ (tangentSpace P e)
    (tangentSpace P e →L[ℝ] ℝ)).toContinuousLinearEquiv).toContinuousLinearMap).comp
      ((tangentCubicForm P e).curryRight.curryLeft)

@[simp] theorem tangentCubicCurried_apply (u v w : tangentSpace P e) :
    tangentCubicCurried P e u v w = P.form ![(u : E), (v : E), (w : E)] := by
  change continuousMultilinearCurryFin1 ℝ (tangentSpace P e) (tangentSpace P e →L[ℝ] ℝ)
    ((tangentCubicForm P e).curryRight.curryLeft u) v w = P.form ![(u : E), (v : E), (w : E)]
  rw [continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.curryRight_apply]
  simp only [tangentCubicForm, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1; ext i; fin_cases i <;> simp

def raisedTangentCubic :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e :=
  ((ContinuousLinearMap.compL ℝ (tangentSpace P e) (tangentSpace P e →L[ℝ] ℝ) (tangentSpace P e))
    (baseChartMetric P e).inverse).comp (tangentCubicCurried P e)

def sourceCurvature (u v w : tangentSpace P e) : tangentSpace P e :=
  -(baseChartMetric P e v w) • u + (baseChartMetric P e u w) • v -
    raisedTangentCubic P e u (raisedTangentCubic P e v w) +
    raisedTangentCubic P e v (raisedTangentCubic P e u w)

theorem diagonalCubic_eq_three (x : E) : diagonalCubic P.form x = P.form ![x, x, x] := by
  unfold diagonalCubic; congr 1; ext i; fin_cases i <;> rfl

theorem cubic_unit_unit_tangent (u : tangentSpace P e) : P.form ![e, e, (u : E)] = 0 := by
  have h : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
  rw [fderiv_diagonalCubic_apply_symmetric] at h; linarith

theorem cubic_unit_tangent_tangent (he : diagonalCubic P.form e = 1) (u v : tangentSpace P e) :
    P.form ![e, (u : E), (v : E)] = -(1 / 2 : ℝ) * baseChartMetric P e u v := by
  have hpos1 : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  have hu : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
  have hv : fderiv ℝ (diagonalCubic P.form) e (v : E) = 0 := v.property
  have h := logHessianForm_apply P hpos1 (u : E) (v : E)
  rw [he, hu, hv, cubicHessian_apply] at h
  change _ = -(1 / 2 : ℝ) * logHessianForm P e (u : E) (v : E)
  linarith

theorem cubic_unit_tangent_expansion (he : diagonalCubic P.form e = 1) (t : ℝ) (u : tangentSpace P e) :
    diagonalCubic P.form (t • e + (u : E)) =
      t^3 - (3 / 2 : ℝ) * t * baseChartMetric P e u u + P.form ![(u : E), (u : E), (u : E)] := by
  have h0 : P.form ![e, e, e] = 1 := by rw [← diagonalCubic_eq_three P e, he]
  have h1 := cubic_unit_unit_tangent P e u
  have h2 : P.form ![e, (u : E), e] = 0 := by rw [P.swap23]; exact h1
  have h3 : P.form ![(u : E), e, e] = 0 := by rw [P.swap12]; exact h2
  have h4 := cubic_unit_tangent_tangent P e he u u
  have h5 : P.form ![(u : E), e, (u : E)] = -(1 / 2 : ℝ) * baseChartMetric P e u u := by
    rw [P.swap12]; exact h4
  have h6 : P.form ![(u : E), (u : E), e] = -(1 / 2 : ℝ) * baseChartMetric P e u u := by
    rw [P.swap23]; exact h5
  rw [diagonalCubic_eq_three, ← fullyCurried_apply]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply, h0, h1, h2, h3, h4, h5, h6]
  ring

theorem cubic_three_neg (u : E) : P.form ![-u, -u, -u] = -P.form ![u, u, u] := by
  rw [← fullyCurried_apply]
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg, fullyCurried_apply]

def frameAmbientMap (F : V ≃ₗ[ℝ] tangentSpace P e) : V →ₗ[ℝ] E :=
  (tangentSpace P e).subtype.comp F.toLinearMap

def framePullbackFunctional (F : V ≃ₗ[ℝ] tangentSpace P e) : (E →L[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun T := T.toLinearMap.comp (frameAmbientMap P e F)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def framePullbackBilinear (F : V ≃ₗ[ℝ] tangentSpace P e) :
    (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun T := (framePullbackFunctional P e F).comp (T.toLinearMap.comp (frameAmbientMap P e F))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def frameTrilinearForm (F : V ≃ₗ[ℝ] tangentSpace P e) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  (framePullbackBilinear P e F).comp ((fullyCurried P).toLinearMap.comp (frameAmbientMap P e F))

def frameCubic (F : V ≃ₗ[ℝ] tangentSpace P e) : SymmetricCubic where
  form := frameTrilinearForm P e F
  swap12 x y z := by
    change fullyCurried P (F x : E) (F y : E) (F z : E) =
      fullyCurried P (F y : E) (F x : E) (F z : E)
    rw [fullyCurried_apply, fullyCurried_apply]
    exact P.swap12 _ _ _
  swap23 x y z := by
    change fullyCurried P (F x : E) (F y : E) (F z : E) =
      fullyCurried P (F x : E) (F z : E) (F y : E)
    rw [fullyCurried_apply, fullyCurried_apply]
    exact P.swap23 _ _ _

@[simp] theorem frameCubic_apply (F : V ≃ₗ[ℝ] tangentSpace P e) (x y z : V) :
    (frameCubic P e F).form x y z = P.form ![(F x : E), (F y : E), (F z : E)] :=
  fullyCurried_apply P (F x : E) (F y : E) (F z : E)

variable [FiniteDimensional ℝ E]

theorem baseChartMetric_injective (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    Function.Injective (baseChartMetric P e) := by
  intro u v huv
  have h0 : baseChartMetric P e (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h0' : baseChartMetric P e (u - v) (u - v) = 0 := by rw [h0]; rfl
  have hz : (u - v : E) = 0 := by
    by_contra hne
    exact (lt_irrefl 0) (h0' ▸ hpos (u - v : E) hne)
  exact sub_eq_zero.mp (Subtype.ext hz)

theorem baseChartMetric_isInvertible (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    (baseChartMetric P e).IsInvertible := by
  let W := tangentSpace P e
  let d : Module.Dual ℝ W ≃ₗ[ℝ] (W →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  letI : FiniteDimensional ℝ (W →L[ℝ] ℝ) := d.finiteDimensional
  have hdim : Module.finrank ℝ W = Module.finrank ℝ (W →L[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := W)).symm.trans d.finrank_eq
  exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq (baseChartMetric P e).toLinearMap
    (baseChartMetric_injective P e hpos) hdim).toContinuousLinearEquiv, rfl⟩

theorem raisedTangentCubic_pairing (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
    (u v w : tangentSpace P e) :
    baseChartMetric P e (raisedTangentCubic P e u v) w = P.form ![(u : E), (v : E), (w : E)] := by
  have h := congrArg (fun L : tangentSpace P e →L[ℝ] ℝ => L w)
    ((baseChartMetric_isInvertible P e hpos).self_apply_inverse (tangentCubicCurried P e u v))
  exact h.trans (tangentCubicCurried_apply P e u v w)

theorem raisedTangentCubic_frame (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
    (F : V ≃ₗ[ℝ] tangentSpace P e)
    (hmetric : ∀ x y : V, baseChartMetric P e (F x) (F y) = gA x y) (x y : V) :
    raisedTangentCubic P e (F x) (F y) = F (KB (frameCubic P e F) x y) := by
  apply baseChartMetric_injective P e hpos
  ext w
  obtain ⟨w, rfl⟩ := F.surjective w
  change baseChartMetric P e (raisedTangentCubic P e (F x) (F y)) (F w) =
    baseChartMetric P e (F (KB (frameCubic P e F) x y)) (F w)
  rw [raisedTangentCubic_pairing P e hpos, hmetric, KB_pairing, frameCubic_apply]

theorem frameCubic_sign_of_curvature (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
    (F : V ≃ₗ[ℝ] tangentSpace P e)
    (hmetric : ∀ x y : V, baseChartMetric P e (F x) (F y) = gA x y)
    (hcurv : ∀ x y z : V, sourceCurvature P e (F x) (F y) (F z) = F (-(AlbertRecognition.D x y z))) :
    frameCubic P e F = referenceCubic ∨ frameCubic P e F = scalarCubic (-1) referenceCubic := by
  apply (q_fiber_reference (frameCubic P e F)).mp
  funext x y; apply LinearMap.ext; intro z
  have hc := hcurv x y z
  dsimp only [sourceCurvature] at hc
  rw [hmetric y z, hmetric x z,
    raisedTangentCubic_frame P e hpos F hmetric y z,
    raisedTangentCubic_frame P e hpos F hmetric x (KB (frameCubic P e F) y z),
    raisedTangentCubic_frame P e hpos F hmetric x z,
    raisedTangentCubic_frame P e hpos F hmetric y (KB (frameCubic P e F) x z)] at hc
  have hlhs : -(gA y z) • F x + gA x z • F y -
      F (KB (frameCubic P e F) x (KB (frameCubic P e F) y z)) +
      F (KB (frameCubic P e F) y (KB (frameCubic P e F) x z)) =
      F (-(gA y z • x - gA x z • y + q (frameCubic P e F) x y z)) := by
    simp only [q, operatorComm_apply, map_neg, map_add, map_sub, map_smul, neg_smul]; abel
  rw [hlhs] at hc
  have hinj := F.injective hc
  dsimp only [AlbertRecognition.D, AlbertRecognition.wedge, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk] at hinj
  exact add_left_cancel (neg_inj.mp hinj)

private def cubicLine (a b c d t : ℝ) : ℝ := a + t * b + t^2 * c + t^3 * d

private theorem hasDerivAt_cubicLine_zero (a b c d : ℝ) :
    HasDerivAt (cubicLine a b c d) b 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) a).add ((hasDerivAt_id (0 : ℝ)).mul_const b)).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c)).add ((hasDerivAt_pow 3 (0 : ℝ)).mul_const d)
  exact h.congr_deriv (by ring)

theorem exists_native_norm_unit_actual_geometry [CompleteSpace E]
    (he : diagonalCubic P.form e = 1)
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
    (F : V ≃ₗ[ℝ] tangentSpace P e)
    (hmetric : ∀ x y : V, baseChartMetric P e (F x) (F y) = gA x y)
    (hcurv : ∀ x y z : V, sourceCurvature P e (F x) (F y) (F z) = F (-(AlbertRecognition.D x y z))) :
    ∃ A : E ≃ₗ[ℝ] Glennie.Albert,
      A e = (1 : Glennie.Albert) ∧
      (∀ x : E, nativeNewtonNorm (A x) = diagonalCubic P.form x) ∧
      (∀ x y : E,
        logHessianForm P e x y = Glennie.trace (jordan (A x) (A y)) / 3) ∧
      (∀ x y : E,
        A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hpos) x y) =
          jordan (A x) (A y)) ∧
      (∀ x y : E, A (ambientGamma P e x y) = -jordan (A x) (A y)) ∧
      (∀ u v w : E,
        A (ambientCurvature P e u v w) =
          -(jordan (A u) (jordan (A v) (A w)) -
            jordan (A v) (jordan (A u) (A w)))) := by
  have hF0 : ∃ F0 : V ≃ₗ[ℝ] tangentSpace P e,
      (∀ x y : V, baseChartMetric P e (F0 x) (F0 y) = gA x y) ∧
      (∀ x : V, P.form ![(F0 x : E), (F0 x : E), (F0 x : E)] = referenceCubic.form x x x) := by
    rcases frameCubic_sign_of_curvature P e hpos F hmetric hcurv with hp | hn
    · exact ⟨F, hmetric, fun x => by
        simpa only [frameCubic_apply] using congrArg (fun B : SymmetricCubic => B.form x x x) hp⟩
    · refine ⟨(LinearEquiv.neg ℝ).trans F, fun x y => ?_, fun x => ?_⟩
      · simp only [LinearEquiv.trans_apply, LinearEquiv.neg_apply, map_neg,
          ContinuousLinearMap.neg_apply, neg_neg, hmetric]
      · simp only [LinearEquiv.trans_apply, LinearEquiv.neg_apply, map_neg, Submodule.coe_neg]
        rw [cubic_three_neg]
        have hx := congrArg (fun B : SymmetricCubic => B.form x x x) hn
        simp only [frameCubic_apply, scalarCubic_form] at hx
        linarith
  obtain ⟨F0, hm0, hc0⟩ := hF0
  have hproj_split (a : Albert) :
      (Glennie.trace a / 3) • (1 : Albert) + (project a : Albert) = a := by
    rw [project_coe, Glennie.traceless]; module
  have htr_split (t : ℝ) (v : V) :
      Glennie.trace ((t / 3) • (1 : Albert) + (v : Albert)) = t := by
    rw [trace_add, trace_smul, trace_unit, trace_V]; ring
  have hpr_split (t : ℝ) (v : V) :
      project ((t / 3) • (1 : Albert) + (v : Albert)) = v := by
    apply Subtype.ext
    rw [project_coe, Glennie.traceless, htr_split]
    module
  let A : E ≃ₗ[ℝ] Albert := {
    toFun := fun x => (fderiv ℝ (diagonalCubic P.form) e x / 3) • (1 : Albert) +
      (F0.symm (tangentProjection P e he x) : Albert)
    invFun := fun a => normalSplitInverse P e (Glennie.trace a, F0 (project a))
    left_inv := fun x => by
      dsimp only
      rw [htr_split, hpr_split, F0.apply_symm_apply]
      exact normalSplit_left_inverse P e he x
    right_inv := fun a => by
      dsimp only
      have hs := normalSplit_right_inverse P e he (Glennie.trace a, F0 (project a))
      have hs1 := congrArg Prod.fst hs
      have hs2 := congrArg Prod.snd hs
      dsimp only at hs1 hs2
      rw [hs1, hs2, F0.symm_apply_apply]
      exact hproj_split a
    map_add' := fun x y => by
      simp only [map_add, add_div, add_smul, Submodule.coe_add]; abel
    map_smul' := fun r x => by
      simp only [map_smul, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul,
        smul_add, smul_smul, div_eq_mul_inv, mul_assoc] }
  have hA_apply (x : E) : A x = (fderiv ℝ (diagonalCubic P.form) e x / 3) • (1 : Albert) +
      (F0.symm (tangentProjection P e he x) : Albert) := rfl
  have hunit : A e = 1 := by
    rw [hA_apply, fderiv_diagonalCubic_at_one P.form e he, tangentProjection_basepoint,
      map_zero, ZeroMemClass.coe_zero, div_self (by norm_num : (3 : ℝ) ≠ 0), one_smul, add_zero]
  have htr (x : E) : Glennie.trace (A x) = fderiv ℝ (diagonalCubic P.form) e x := by
    rw [hA_apply]; exact htr_split _ _
  have hm (x y : E) : logHessianForm P e x y = Glennie.inner (A x) (A y) / 3 := by
    let tx := fderiv ℝ (diagonalCubic P.form) e x / 3
    let ux := tangentProjection P e he x
    let ty := fderiv ℝ (diagonalCubic P.form) e y / 3
    let uy := tangentProjection P e he y
    have hx_eq : x = tx • e + (ux : E) := (normalSplit_left_inverse P e he x).symm
    have hy_eq : y = ty • e + (uy : E) := (normalSplit_left_inverse P e he y).symm
    have hee : logHessianForm P e e e = 1 := by
      rw [logHessianForm_radial_at_one P e e he, fderiv_diagonalCubic_at_one P.form e he]; norm_num
    have heu (u : tangentSpace P e) : logHessianForm P e e (u : E) = 0 := by
      rw [logHessianForm_radial_at_one P e (u : E) he]
      have hu : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
      rw [hu]; ring
    have hue (u : tangentSpace P e) : logHessianForm P e (u : E) e = 0 := by
      rw [logHessianForm_symm P (by rw [he]; norm_num), heu]
    have huu : logHessianForm P e (ux : E) (uy : E) =
        Glennie.inner (F0.symm ux : Albert) (F0.symm uy : Albert) / 3 := by
      change baseChartMetric P e ux uy = gA (F0.symm ux) (F0.symm uy)
      rw [← hm0 (F0.symm ux) (F0.symm uy), F0.apply_symm_apply, F0.apply_symm_apply]
    have hin1 (v : V) : Glennie.inner (1 : Albert) (v : Albert) = 0 := by
      rw [inner_unit_left, trace_V]
    have hin2 (v : V) : Glennie.inner (v : Albert) (1 : Albert) = 0 := by
      rw [inner_unit_right, trace_V]
    conv_lhs => rw [hx_eq, hy_eq]
    simp only [hA_apply, map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hee, heu, hue, huu,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_unit_left, trace_unit, hin1, hin2]
    ring
  have hnorm (x : E) : nativeNewtonNorm (A x) = diagonalCubic P.form x := by
    let t := fderiv ℝ (diagonalCubic P.form) e x / 3
    let u := tangentProjection P e he x
    let v := F0.symm u
    have hx_eq : x = t • e + (u : E) := (normalSplit_left_inverse P e he x).symm
    have hvu : F0 v = u := F0.apply_symm_apply u
    have hmetric_u : baseChartMetric P e u u = Glennie.inner (v : Albert) (v : Albert) / 3 := by
      rw [← hvu, hm0 v v]; rfl
    have hcubic_u : P.form ![(u : E), (u : E), (u : E)] =
        Glennie.inner (v : Albert) (jordan (v : Albert) (v : Albert)) / 3 := by
      rw [← hvu, hc0 v]
      change CA v v v = _
      rw [CA_eq_native, inner_comm]
    have hv_tr : Glennie.trace (v : Albert) = 0 := trace_V v
    have hin1 : Glennie.inner (1 : Albert) (v : Albert) = 0 := by rw [inner_unit_left, hv_tr]
    have hin2 : Glennie.inner (v : Albert) (1 : Albert) = 0 := by rw [inner_unit_right, hv_tr]
    have hvv : Glennie.trace (jordan (v : Albert) (v : Albert)) =
        Glennie.inner (v : Albert) (v : Albert) := rfl
    conv_rhs => rw [hx_eq, cubic_unit_tangent_expansion P e he t u, hmetric_u, hcubic_u]
    change nativeNewtonNorm (t • (1 : Albert) + (v : Albert)) = _
    simp only [nativeNewtonNorm, trace_add, trace_smul, trace_unit, hv_tr,
      jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
      jordan_unit_left, jordan_unit_right, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, inner_unit_left, inner_unit_right,
      hin1, hin2, hvv]
    ring
  have hfderiv (x y : E) :
      fderiv ℝ (diagonalCubic P.form) x y = Glennie.inner (nativeAdjoint (A x)) (A y) := by
    have ha : HasDerivAt (fun s : ℝ => x + s • y) y 0 :=
      (((hasDerivAt_id (0 : ℝ)).smul_const y).const_add x).congr_deriv (by simp)
    have hN : HasFDerivAt (diagonalCubic P.form) (fderiv ℝ (diagonalCubic P.form) x) x :=
      (hasFDerivAt_diagonalCubic P.form x).congr_fderiv (fderiv_diagonalCubic P.form x).symm
    have h1 : HasDerivAt (fun s : ℝ => diagonalCubic P.form (x + s • y))
        (fderiv ℝ (diagonalCubic P.form) x y) 0 := by
      simpa only [Function.comp_def] using
        (hN.comp_hasDerivAt_of_eq 0 ha (by simp))
    have hline (s : ℝ) : diagonalCubic P.form (x + s • y) =
        cubicLine (nativeNewtonNorm (A x)) (Glennie.inner (nativeAdjoint (A x)) (A y))
          (Glennie.inner (nativeAdjoint (A y)) (A x)) (nativeNewtonNorm (A y)) s := by
      rw [← hnorm (x + s • y), map_add, map_smul]
      exact nativeNewtonNorm_line (A x) (A y) s
    have h2 := (hasDerivAt_cubicLine_zero (nativeNewtonNorm (A x))
      (Glennie.inner (nativeAdjoint (A x)) (A y))
      (Glennie.inner (nativeAdjoint (A y)) (A x))
      (nativeNewtonNorm (A y))).congr_of_eventuallyEq (Filter.Eventually.of_forall hline)
    exact h1.unique h2
  let hB := rawBilinearForm_nondegenerate P e he hpos
  have hraw (x y : E) : rawTraceForm P e x y = Glennie.inner (A x) (A y) := by
    rw [rawTraceForm_eq_three_logMetric P e he, hm]; ring
  have hadj (x : E) : A (intrinsicAdjoint P e hB x) = nativeAdjoint (A x) := by
    have h := intrinsicAdjoint_unique P e hB x (A.symm (nativeAdjoint (A x))) (fun y => by
      rw [hraw, A.apply_symm_apply, hfderiv])
    exact (congrArg A h.symm).trans (A.apply_symm_apply _)
  have hprod (x y : E) : A (intrinsicProduct P e hB x y) = jordan (A x) (A y) := by
    have htr_eq (z : E) : normTrace P e z = Glennie.trace (A z) := (htr z).symm
    simp only [intrinsicProduct, intrinsicCross, intrinsicS, map_smul, map_add, map_sub,
      hadj, htr_eq, hraw, hunit]
    rw [← nativeRecoveredProduct_eq (A x) (A y)]
    dsimp [nativeRecoveredProduct, nativeCross]
    module
  refine ⟨A, hunit, hnorm, hm, hprod, fun x y => ?_, fun u v w => ?_⟩
  · rw [ambientGamma_at_one_eq_neg_product P e he hpos, map_neg, hprod]
  · rw [ambientCurvature_at_one_eq_neg_product_commutator P e he hpos]
    simp only [map_neg, map_sub, hprod]

end
end AlbertGeometry.RecognitionFromCurvature
