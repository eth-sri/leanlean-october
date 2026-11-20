module
public import AlbertGeometry.CubicHessian
public import AlbertRecognition.CubicFiber

/-! Reassemble the polarized cubic, not just its diagonal, across the normal
line and the derivative kernel. In this splitting its four blocks have zero,
one, two, or three tangent arguments. Only the last block has a sign choice. -/
@[expose] public section
namespace AlbertGeometry.RecognitionFromCurvature
noncomputable section
open Glennie AlbertRecognition SubmissionR04Intrinsic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : BasedCubic E) (e : E) (he : cubic P e = 1)

private theorem tan_trace (u : tangent P e) : traceAt P e u = 0 := u.2
private theorem cubic_unit_unit_tangent (u : tangent P e) : P.form ![e,e,(u:E)] = 0 := by
  have h := tan_trace P e u; simpa [trace_eq] using h
include he in
private theorem cubic_unit_tangent_tangent (u v : tangent P e) : P.form ![e,(u:E),v] = -(1/2 : ℝ) * metric P e u v := by
  rw [metric_formula P (by simp [he]),he,tan_trace]; simp

private def joinUnit {X : Type*} [AddCommGroup X] [Module ℝ X] (l : X →ₗ[ℝ] ℝ)
    (a : X) (h : l a = 3) : (ℝ × l.ker) ≃ₗ[ℝ] X where
  toFun p := p.1 • a + p.2
  map_add' _ _ := by simp [add_smul]; abel
  map_smul' _ _ := by simp [smul_add, smul_smul]
  invFun x := (l x / 3, ⟨x - (l x / 3) • a, by change l _ = 0; simp [h]⟩)
  right_inv x := by change (l x / 3) • a + (x - _) = x; abel
  left_inv := by
    rintro ⟨t,u⟩; have hu : l (u : X) = 0 := u.2
    have ht : l (t • a + u) / 3 = t := by simp [h,hu]
    simp only [ht]; congr 2; abel

def newton3 (x y z : Albert) : ℝ :=
  trace x * trace y * trace z - trace x * inner y z - trace y * inner x z - trace z * inner x y +
  2 * inner (jordan x y) z

private theorem signedTangent (F : V ≃ₗ[ℝ] tangent P e)
    (hm : ∀ x y : V, metric P e (F x) (F y) = gA x y)
    (hs : (∀ x y z : V, P.form ![(F x:E),F y,F z] = CA x y z) ∨
      (∀ x y z : V, P.form ![(F x:E),F y,F z] = -CA x y z)) :
    ∃ D : tangent P e ≃ₗ[ℝ] V,
      (∀ u v : tangent P e, metric P e u v = gA (D u) (D v)) ∧
      ∀ u v w : tangent P e, P.form ![(u : E),v,w] = CA (D u) (D v) (D w) := by
  rcases hs with h | h
  · refine ⟨F.symm,?_,?_⟩
    · intro u v; simpa using hm (F.symm u) (F.symm v)
    · intro u v w; have eq := h (F.symm u) (F.symm v) (F.symm w)
      simpa using eq
  · refine ⟨F.symm.trans (LinearEquiv.neg ℝ),?_,?_⟩
    · intro u v; simpa [gA,Glennie.inner_neg_left,Glennie.inner_neg_right] using hm (F.symm u) (F.symm v)
    · intro u v w; have eq := h (F.symm u) (F.symm v) (F.symm w)
      simpa [neg_div,CA_eq_native,jordan_neg_left,jordan_neg_right,Glennie.inner_neg_right] using eq

include he in
theorem lift_signed_frame (F : V ≃ₗ[ℝ] tangent P e)
    (hm : ∀ x y : V, metric P e (F x) (F y) = gA x y)
    (hs : (∀ x y z : V, P.form ![(F x:E),F y,F z] = CA x y z) ∨
      (∀ x y z : V, P.form ![(F x:E),F y,F z] = -CA x y z)) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧
      ∀ x y z, 6 * P.form ![x,y,z] = newton3 (A x) (A y) (A z) := by
  obtain ⟨D,hm,hc⟩ := signedTangent P e F hm hs
  let jE := joinUnit (traceAt P e).toLinearMap e (SubmissionR04Intrinsic.trace_unit P e he)
  let jA := joinUnit Glennie.traceLinear 1 Glennie.trace_unit
  let A := jE.symm.trans (((LinearEquiv.refl ℝ ℝ).prodCongr D).trans jA)
  have ap (t : ℝ) (u : tangent P e) : A (t • e + u) = t • (1 : Albert) + (D u : Albert) := by
    exact congrArg (((LinearEquiv.refl ℝ ℝ).prodCongr D).trans jA) (jE.symm_apply_apply (t,u))
  have rep (x : E) : ∃ (t : ℝ) (u : tangent P e), t • e + u = x :=
    ⟨_,_, jE.apply_symm_apply x⟩
  refine ⟨A,by simpa using ap 1 0,?_⟩; intro x y z
  obtain ⟨t,u,rfl⟩ := rep x; obtain ⟨s,v,rfl⟩ := rep y; obtain ⟨r,w,rfl⟩ := rep z
  have h0 : P.form ![e,e,e] = 1 := by simpa [cubic_diag] using he
  rw [← tri_apply]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, tri_apply, ap, newton3,
    trace_add,trace_smul,Glennie.trace_unit,trace_V, jordan_add_left,jordan_add_right,
    jordan_smul_left,jordan_smul_right,jordan_unit_left,jordan_unit_right,
    Glennie.inner_add_left,Glennie.inner_add_right,Glennie.inner_smul_left,Glennie.inner_smul_right,inner_unit_left,inner_unit_right]
  simp only [P.swap23 _ _ e, P.swap12 _ e _, h0,cubic_unit_unit_tangent,
    cubic_unit_tangent_tangent P e he,hm,hc,CA_eq_native,gA, trace_V,Glennie.trace_unit,
    show ∀ x y, trace (jordan x y) = inner x y from fun _ _ => rfl]
  ring
end
end AlbertGeometry.RecognitionFromCurvature
