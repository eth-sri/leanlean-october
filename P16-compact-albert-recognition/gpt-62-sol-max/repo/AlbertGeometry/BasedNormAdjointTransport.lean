module

public import AlbertGeometry.BasedNormDerivativeTransport
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
@[expose] public section
namespace AlbertGeometry.BasedNormAdjointTransport
noncomputable section
open Glennie.SubmissionR04Intrinsic
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In finite dimension an injective bilinear pairing is invertible into the dual. -/
theorem dual_isInvertible [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (h : ∀ x : E, B x x = 0 → x = 0) : B.IsInvertible := by
  let d : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  letI := d.finiteDimensional
  have hi : Function.Injective B := (LinearMap.ker_eq_bot (f := B.toLinearMap)).mp <|
    LinearMap.ker_eq_bot'.mpr fun x hx => h x (congrArg (fun f : E →L[ℝ] ℝ => f x) hx)
  exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq B.toLinearMap hi
    ((Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans d.finrank_eq)).toContinuousLinearEquiv, rfl⟩

theorem rawTraceForm_isInvertible [FiniteDimensional ℝ E]
    (P : BasedCubic E) (e : E) (he : cubic P e = 1)
    (hp : ∀ x : E, x ≠ 0 → 0 < metric P e x x) :
    (rawPair P e).IsInvertible :=
  dual_isInvertible _ fun x hx => by
    by_contra hn
    linarith [rawTraceForm_eq_three_logMetric P e he x x, hp x hn]

theorem intrinsicAdjoint_pairing (P : BasedCubic E) (e : E)
    (hB : (rawPair P e).IsInvertible) (x y : E) :
    rawPair P e (adjoint P e x) y = fderiv ℝ (cubic P) x y :=
  congrArg (fun L : E →L[ℝ] ℝ => L y) (hB.self_apply_inverse _)

/-- Unhalved polarization of the actual quadratic adjoint. -/
def intrinsicCross (P : BasedCubic E) (e x y : E) : E :=
  adjoint P e (x + y) - adjoint P e x - adjoint P e y

def intrinsicS (P : BasedCubic E) (e x y : E) : ℝ :=
  traceAt P e x * traceAt P e y - rawPair P e x y

end
end AlbertGeometry.BasedNormAdjointTransport
