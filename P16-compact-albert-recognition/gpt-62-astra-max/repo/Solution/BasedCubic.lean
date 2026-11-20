module
public import Glennie.ObservationData
public import AlbertGeometry.RecognitionFromCurvature
public import AlbertGeometry.AmbientCurvatureProduct

@[expose] public section
namespace Glennie.SubmissionR04Intrinsic
noncomputable section
set_option autoImplicit false
open Glennie
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open AlbertRecognition AlbertGeometry
open RecognitionFromCurvature

variable [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : BasedCubic E) (e : E) (he : cubic P e = 1)
  (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) (F : V ≃ₗ[ℝ] tangent P e)
  (hm : ∀ x y : V, metric P e (F x : E) (F y : E) = gA x y)

private theorem curried_apply (u v w : tangent P e) :
    tangentCubicCurried P e u v w = P.form ![(u : E),v,w] := by
  change continuousMultilinearCurryFin1 ℝ (tangent P e) ((tangent P e) →L[ℝ] ℝ) (((tangentCubicForm P e).curryRight.curryLeft) u) v w = _
  rw [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.curryRight_apply]
  apply congrArg P.form
  ext i; fin_cases i <;> rfl

include hp hm he in
theorem polarized_of_match
    (hc : ∀ x y z : V, independentCurvature P e (F x) (F y) (F z) = F (nativeCurvature x y z)) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧ ∀ x y z, 6 * P.form ![x,y,z] = newton3 (A x) (A y) (A z) := by
  apply lift_signed_frame P e he F hm
  let k (x y : V) := F.symm (independentRaisedCubic P e (F x) (F y))
  let K : V →ₗ[ℝ] V →ₗ[ℝ] V := LinearMap.mk₂ ℝ k (by intros; simp [k]) (by intros; simp [k])
    (by intros; simp [k]) (by intros; simp [k])
  have pair (x y z : V) : gA (K x y) z = P.form ![(F x:E),F y,F z] := by
    have hI : (tangentMetricDual P e).IsInvertible := invertible_of_positive _ fun u hu => hp u (by simpa using hu)
    rw [←hm]; change tangentMetricDual P e (F (k x y)) (F z) = _
    rw [show F (k x y) = _ from F.apply_symm_apply _]
    change tangentMetricDual P e ((tangentMetricDual P e).inverse _) (F z) = _
    rw [hI.self_apply_inverse]; exact curried_apply P e _ _ _
  let B : SymmetricCubic := ⟨K,fun x y => gA_ext fun z => by rw [pair,pair,P.swap12], fun x y z => by rw [pair,pair,P.swap23]⟩
  have form (x y z : V) : B.form x y z = _ := pair x y z
  suffices eq : q B = q referenceCubic by simpa only [form] using cubic_sign B eq
  funext x y; apply LinearMap.ext; intro z
  apply F.injective
  have eqv (a b c : V) : nativeCurvature a b c =
      (-(gA b c) • a + gA a c • b - KA a (KA b c) + KA b (KA a c) : V) := by
    have k (v w : V) : nativeK v w = KA v w := by rw [KA_apply]; rfl
    simp only [nativeCurvature,k]; rfl
  have h := hc x y z
  rw [eqv] at h
  simp only [independentCurvature, map_add, map_sub, map_smul,
    show ∀ a b : V, tangentMetricDual P e (F a) (F b) = gA a b from hm,
    show ∀ a b : V, independentRaisedCubic P e (F a) (F b) = F (B.K a b) from fun a b => (F.apply_symm_apply _).symm] at h
  change F (B.K x (B.K y z) - B.K y (B.K x z)) = F (KA x (KA y z) - KA y (KA x z)); rw [map_sub,map_sub]
  linear_combination (norm := module) -h

end
end Glennie.SubmissionR04Intrinsic

