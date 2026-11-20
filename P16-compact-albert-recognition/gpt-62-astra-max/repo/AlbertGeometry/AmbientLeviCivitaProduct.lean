module
public import AlbertGeometry.CubicHessian
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! The actual log-Hessian metric, its Koszul covector, and the product
obtained by polarizing the actual raised differential. -/
@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
attribute [local instance] taskAmbientDualNorm taskAmbientDualSpace taskAmbientBilinearNorm taskAmbientBilinearSpace taskAmbientTrilinearNorm taskAmbientTrilinearSpace taskAmbientEndNorm taskAmbientEndSpace taskAmbientVectorBilinearNorm taskAmbientVectorBilinearSpace taskAmbientInverseNorm taskAmbientInverseSpace
open Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : BasedCubic E)

theorem koszul {x : E} (hx : 0 < cubic P x) : ambientKoszulTensor P x = (1/2 : ℝ) • ambientMetricD1 P x := by
  ext u v w
  change 1/2 * (ambientMetricD1 P x u v w + ambientMetricD1 P x v u w - ambientMetricD1 P x w u v) = _
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,metric_jet P hx,tri_apply,P.swap12,P.swap23]; ring

variable [FiniteDimensional ℝ E]
theorem invertible_of_positive (B : E →L[ℝ] E →L[ℝ] ℝ) (hp : ∀ u ≠ 0, 0 < B u u) : B.IsInvertible := by
  let d : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  have hi : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro u hu; by_contra hn; simpa [hu] using hp u hn
  exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq B.toLinearMap hi
    ((Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans d.finrank_eq)).toContinuousLinearEquiv,rfl⟩

variable {e : E} (he : cubic P e = 1) (hp : ∀ u ≠ 0, 0 < metric P e u u)
include he hp in
theorem product_pair (u v w : E) : rawPair P e (product P e u v) w = 3 * tri P u v w +
    (traceAt P e u * rawPair P e v w + traceAt P e v * rawPair P e u w -
      (traceAt P e u * traceAt P e v - rawPair P e u v) * traceAt P e w)/2 := by
  have hi := invertible_of_positive (rawPair P e) (fun u hu => by rw [raw_metric P he]; positivity [hp u hu])
  have adj (a b : E) : rawPair P e (adjoint P e a) b = 3 * tri P a a b := by
    change rawPair P e ((rawPair P e).inverse (traceAt P a)) b = _
    rw [hi.self_apply_inverse,trace_eq]; rfl
  have unit : rawPair P e e w = traceAt P e w := by
    rw [rawPair_apply,trace_unit P e he,trace_eq]; simp; ring
  simp only [product,map_smul,map_add,map_sub,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul,adj,unit,tri_apply,P.swap12 v u w]; ring

theorem connection_pair {x : E} (hx : 0 < cubic P x) (hi : (metric P x).IsInvertible) (u v w : E) :
    metric P x (ambientConnection P x u v) w = (1/2 : ℝ) * ambientMetricD1 P x u v w := by
  change metric P x ((metric P x).inverse (ambientKoszulTensor P x u v)) w = _
  rw [hi.self_apply_inverse,koszul P hx]; rfl

include he hp in
theorem connection_product (u v : E) : ambientConnection P e u v = -product P e u v := by
  have hi := invertible_of_positive _ hp
  apply hi.injective; ext w
  rw [connection_pair P (by simp [he]) hi,map_neg,ContinuousLinearMap.neg_apply]
  have h := raw_metric P he (product P e u v) w
  rw [product_pair P he hp,rawPair_apply,rawPair_apply,rawPair_apply] at h
  rw [metric_jet P (by simp [he]),he]; simp only [inv_one,one_pow]; linarith

variable [CompleteSpace E]
theorem smooth_connection {x : E} (hx : 0 < cubic P x) (hi : (metric P x).IsInvertible) :
    ContDiffAt ℝ ⊤ (ambientConnection P) x := by
  have hG := metric_smooth P hx
  have hI := (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ⊤) hi).fun_comp x hG
  have hD : ContDiffAt ℝ ⊤ (ambientMetricD1 P) x := hG.fderiv_right (by simp)
  have hK := (hD.const_smul (1/2 : ℝ)).congr_of_eventuallyEq ((pos_near P hx).mono fun y h => koszul P h)
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).contDiff.contDiffAt.fun_comp x hI).clm_comp hK
end
end Glennie.SubmissionR04Intrinsic
