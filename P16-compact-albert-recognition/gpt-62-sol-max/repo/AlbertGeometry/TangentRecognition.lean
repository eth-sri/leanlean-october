module
public import AlbertGeometry.AmbientCurvatureProduct
public import AlbertRecognition.CubicFiber
public import Mathlib.LinearAlgebra.Prod
@[expose] public section
namespace AlbertGeometry.TangentRecognition
open Glennie AlbertRecognition Cubic
open BasedNormDerivativeTransport.BasedNormIso BasedNormAdjointTransport
open AmbientLeviCivitaProduct AmbientCurvatureProduct
noncomputable section
open Glennie.SubmissionR04Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frameCubic (P : BasedCubic E) (e : E)
    (F : V ≃ₗ[ℝ] tangent P e) : SymmetricCubic := by
  let f := (tangent P e).subtype.comp F.toLinearMap
  let L := (ContinuousLinearMap.coeLM ℝ).comp (fullyCurried P.form).toLinearMap
  let L' := L.compr₂ (ContinuousLinearMap.coeLM ℝ)
  refine ⟨(L'.compl₁₂ f f).compr₂ (LinearMap.lcomp ℝ ℝ f), fun x y z => ?_, fun x y z => ?_⟩
  · exact (fullyCurried_apply ..).trans ((P.swap12 ..).trans (fullyCurried_apply ..).symm)
  · exact (fullyCurried_apply ..).trans ((P.swap23 ..).trans (fullyCurried_apply ..).symm)

@[simp] theorem frameCubic_apply (P : BasedCubic E) (e : E)
    (F : V ≃ₗ[ℝ] tangent P e) (x y z : V) :
    (frameCubic P e F).form x y z = P.form ![(F x : E), (F y : E), (F z : E)] :=
  fullyCurried_apply _ _ _ _

private def split {M : Type*} [AddCommGroup M] [Module ℝ M]
    (L : M →ₗ[ℝ] ℝ) (u : M) (hu : L u = 3) : (ℝ × L.ker) ≃ₗ[ℝ] M where
  toFun p := p.1 • u + p.2
  invFun x := (L x / 3, ⟨x - (L x / 3) • u, by
    simp [hu, smul_eq_mul]⟩)
  left_inv p := by
    have hp : L (p.2 : M) = 0 := p.2.2
    have h : L (p.1 • u + (p.2 : M)) / 3 = p.1 := by simp [hu, hp, smul_eq_mul]
    refine Prod.ext h (Subtype.ext ?_)
    change p.1 • u + (p.2 : M) - (L (p.1 • u + (p.2 : M)) / 3) • u = p.2
    rw [h]; abel
  right_inv x := by simp
  map_add' p q := by simp [add_smul]; abel
  map_smul' t p := by simp [smul_add, smul_smul, smul_eq_mul]

private theorem cubic_add_smul (P : BasedCubic E) (x y : E) (t : ℝ) :
    cubic P (x + t • y) = cubic P x +
      t * (3 * P.form ![x,x,y]) + (t^2 * (3 * P.form ![y,y,x])) + t^3 * cubic P y := by
  simp only [diagonalCubic_eq, ← fullyCurried_apply, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  simp only [fullyCurried_apply]
  rw [P.swap12 y x x, P.swap23 x y x, P.swap12 x y y, P.swap23 y x y]
  ring

private theorem norm_split (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (t : ℝ) (u : tangent P e) :
    cubic P (t • e + (u : E)) =
      t ^ 3 - (3 / 2) * t * metric P e u u + cubic P (u : E) := by
  have hz : fderiv ℝ (cubic P) e (u : E) = 0 := u.2
  have h1 := hz
  rw [fderiv_diagonalCubic_apply_symmetric] at h1
  have h2 := logHessianForm_apply P (by rw [he]; norm_num) (u : E) (u : E)
  rw [he, cubicHessian_apply, hz] at h2
  rw [add_comm, cubic_add_smul, he, P.swap23 (u : E) (u : E) e,
    P.swap12 (u : E) e (u : E)]
  linear_combination (3 / 2) * t * h2 + t^2 * h1

private theorem native_norm_split (t : ℝ) (u : V) :
    nativeCubic (t • (1 : Albert) + (u : Albert)) =
      t ^ 3 - (3 / 2) * t * gA u u + referenceCubic.form u u u := by
  change _ = _ + CA u u u
  rw [CA_eq_native, gA]
  simp only [nativeCubic, trace_add, trace_smul, trace_unit, trace_V,
    jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
    jordan_unit_left, jordan_unit_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_unit_left, inner_unit_right,
    inner_comm (jordan (u : Albert) (u : Albert)) (u : Albert)]
  simp only [Glennie.inner]
  ring

/-- Curvature fixes the tangent cubic up to negating the tangent factor. -/
theorem norm_unit_of_q (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (F : V ≃ₗ[ℝ] tangent P e)
    (hm : ∀ x y, metric P e (F x) (F y) = gA x y)
    (hq : q (frameCubic P e F) = q referenceCubic) :
    ∃ A : E ≃ₗ[ℝ] Albert, A e = 1 ∧ ∀ x, nativeCubic (A x) = cubic P x := by
  obtain ⟨r, hr, hB⟩ := q_fiber_reference _ hq
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at hr
  let D := F.trans (LinearEquiv.smulOfNeZero ℝ (tangent P e) r hr0)
  let S := split (fderiv ℝ (cubic P) e).toLinearMap e
    (fderiv_diagonalCubic_at_one P e he)
  let B : (ℝ × V) ≃ₗ[ℝ] Albert := split Glennie.traceLinear (1 : Albert) trace_unit
  let I := ((LinearEquiv.refl ℝ ℝ).prodCongr D).trans S
  have hI (t : ℝ) (v : V) : I (t,v) = t • e + (r • (F v : E)) := rfl
  refine ⟨I.symm.trans B, ?_, ?_⟩
  · have h : I (1,0) = e := by simp [hI]
    rw [← h, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    change (1 : ℝ) • (1 : Albert) + 0 = 1
    simp
  · intro x
    obtain ⟨⟨t,v⟩, rfl⟩ := I.surjective x
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hI]
    change nativeCubic (t • (1 : Albert) + (v : Albert)) =
      cubic P (t • e + ((r • F v : tangent P e) : E))
    rw [native_norm_split, norm_split P e he]
    have hc := congrArg (fun C : SymmetricCubic => C.form v v v) hB
    rw [frameCubic_apply, scalarCubic_form] at hc
    simp only [Submodule.coe_smul, map_smul, smul_apply,
      smul_eq_mul, hm, diagonalCubic_eq, ← fullyCurried_apply]
    rw [fullyCurried_apply, hc]
    simp only [← mul_assoc, hr, one_mul]

/-- The mixed polarization of the actual diagonal cubic. -/
private theorem polar_cubic (P : BasedCubic E) (x y z : E) :
    6 * P.form ![x,y,z] = cubic P (x+y+z) - cubic P (x+y) - cubic P (y+z) -
      cubic P (z+x) + cubic P x + cubic P y + cubic P z := by
  simp only [diagonalCubic_eq, ← fullyCurried_apply, map_add, add_apply]
  simp only [fullyCurried_apply, P.swap12, P.swap23]
  ring

private theorem native_polarization (P : BasedCubic E) (A : E ≃ₗ[ℝ] Albert)
    (hn : ∀ x, nativeCubic (A x) = cubic P x) (x y z : E) :
    6 * P.form ![x,y,z] = trace (A x) * trace (A y) * trace (A z) -
      (trace (A x) * inner (A y) (A z) + trace (A y) * inner (A x) (A z) +
        trace (A z) * inner (A x) (A y)) + 2 * inner (jordan (A x) (A y)) (A z) := by
  rw [polar_cubic]
  simp only [← hn, map_add, nativeCubic, trace_add, inner_add_left, inner_add_right,
    jordan_add_left, jordan_add_right, ← inner_jordan_associative]
  have h (u v w : Albert) : inner (jordan u v) w = inner (jordan u w) v := by
    rw [inner_jordan_associative, inner_jordan_associative, jordan_comm v w]
  simp only [jordan_comm, h, inner_comm]
  ring

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Recover the adjoint from the affine-line coefficient of the norm.
The metric uses the second coefficient through the normalized unit. -/
theorem actual_geometry_of_norm (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x)
    (A : E ≃ₗ[ℝ] Albert) (hu : A e = 1)
    (hn : ∀ x, nativeCubic (A x) = cubic P x) :
    (∀ x, traceAt P e x = Glennie.trace (A x)) ∧
    (∀ x y, rawPair P e x y = Glennie.inner (A x) (A y)) ∧
    (∀ x y, A (product P e x y) =
      jordan (A x) (A y)) ∧
    (∀ x y, A (ambientConnection P e x y) = -jordan (A x) (A y)) ∧
    (∀ x y z, A (ambientCurvature P e x y z) =
      -(jordan (A x) (jordan (A y) (A z)) - jordan (A y) (jordan (A x) (A z)))) := by
  have htrace (x : E) : traceAt P e x = trace (A x) := by
    rw [traceAt, fderiv_diagonalCubic_apply_symmetric]
    have h := native_polarization P A hn e e x
    simp only [hu, trace_unit, inner_unit_left, jordan_unit_left] at h
    linarith
  have hb (x y : E) : rawPair P e x y = inner (A x) (A y) := by
    rw [rawTraceForm_apply, htrace, htrace, cubicHessian_apply]
    have h := native_polarization P A hn e x y
    simp only [hu, trace_unit, inner_unit_left, jordan_unit_left] at h
    linarith
  have hB := rawTraceForm_isInvertible P e he hp
  have hJ (x y : E) : A (product P e x y) = jordan (A x) (A y) := by
    apply ext_inner_right ℝ
    intro w
    obtain ⟨z, rfl⟩ := A.surjective w
    simp only [hilbert_inner_eq_native]
    rw [← hb, intrinsicProduct_pairing P e he hB]
    simp only [intrinsicS, htrace, hb]
    linarith [native_polarization P A hn x y z]
  have hG (x y : E) : A (ambientConnection P e x y) = -jordan (A x) (A y) := by
    rw [ambientGamma_at_one_eq_neg_product P e he hp, map_neg, hJ]
  refine ⟨htrace, hb, hJ, hG, fun x y z => ?_⟩
  have he' : 0 < cubic P e := by simp [he]
  rw [ambientCurvature_eq_neg_Gamma_commutator P he' hp]
  simp only [map_neg, map_sub, hG, jordan_neg_right, neg_neg]

end
end AlbertGeometry.TangentRecognition
