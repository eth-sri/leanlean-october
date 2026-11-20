module

public import RequestProject.NeumannBoundaryPole
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannResonanceDimension
public import RequestProject.NeumannConstantTrace
public import RequestProject.SobolevCircle

/-!
# The actual Neumann form with bounded boundary coordinates

These constructions accept a bounded coordinate trace Q. The interior
operator and its spectral sequence remain the actual variational Neumann
ones. In conformal coordinates Q is the constructed conformal half trace;
it need not come from a constant-speed circle parameter. Compatibility
with physical boundary data is a separate identity for that actual Q.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter Topology
open scoped InnerProductSpace

/- The identities below are proved while the Hilbert spaces are abstract.
Specializing their opaque proofs avoids recomputing the concrete H¹ and
Fourier-space structures in operator coercions and adjoint identities. -/

section HilbertBarriers

variable {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

section

variable (Q : H →L[ℂ] G) (A : H →L[ℂ] H) (W : H → H → ℂ) (hA : ∀ v u, ⟪v, A u⟫_ℂ = W v u)
    (hunit : IsUnit A) (b : G)

include hA in
private theorem normalized_trace_weak_iff (u : H) :
    (∀ v, W v u = ⟪Q v, b⟫_ℂ) ↔ A u = ContinuousLinearMap.adjoint Q b := by
  constructor
  · intro hu
    exact ext_inner_left ℂ fun v =>
      (hA v u).trans ((hu v).trans
        (ContinuousLinearMap.adjoint_inner_right Q v b).symm)
  · intro hu v
    exact (hA v u).symm.trans
      ((congrArg (fun x : H => ⟪v, x⟫_ℂ) hu).trans
        (ContinuousLinearMap.adjoint_inner_right Q v b))

omit [CompleteSpace H] in
private theorem normalized_form_inverse_apply (hA : IsUnit A) (x : H) :
    A (Ring.inverse A x) = x := congrArg (fun B : H →L[ℂ] H => B x) (Ring.mul_inverse_cancel A hA)

include hA hunit in
private theorem normalized_trace_inverse_solution :
    ∀ v, W v (((Ring.inverse A).comp (ContinuousLinearMap.adjoint Q)) b) =
      ⟪Q v, b⟫_ℂ := by
  apply (normalized_trace_weak_iff Q A W hA b _).2
  exact normalized_form_inverse_apply A hunit (ContinuousLinearMap.adjoint Q b)

private theorem normalized_trace_sandwich_isSelfAdjoint (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (Q.comp (A.comp (ContinuousLinearMap.adjoint Q))) :=
  hA.conj_adjoint Q

private theorem normalized_trace_sandwich_pole {A P R : H →L[ℂ] H} {a c d : ℂ}
    (ha : a = c * d) (hA : A = a • P + R) :
    Q.comp (A.comp (ContinuousLinearMap.adjoint Q)) =
      c • (d • (Q.comp (P.comp (ContinuousLinearMap.adjoint Q)))) +
        Q.comp (R.comp (ContinuousLinearMap.adjoint Q)) := by
  rw [hA, ha]
  simp [smul_smul]

end

end HilbertBarriers

section

variable {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z)

section

variable (E₀ E : ℝ) (b : L2Z) (u : NeumannH1 Ω)

include E in
def normalizedNeumannPoisson : L2Z →L[ℂ] NeumannH1 Ω :=
  (h1HelmholtzResolvent Ω E).comp (ContinuousLinearMap.adjoint Q)

include E in
def normalizedNeumannBoundary : FourierOp :=
  Q.comp (normalizedNeumannPoisson Q E)

include E b u in
def IsNormalizedNeumannSolution : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ = ⟪Q v, b⟫_ℂ

theorem isNormalizedNeumannSolution_iff :
    IsNormalizedNeumannSolution Q E b u ↔
      h1HelmholtzForm Ω E u = ContinuousLinearMap.adjoint Q b := by
  exact normalized_trace_weak_iff  (G := L2Z) Q
    (h1HelmholtzForm Ω E)
    (fun v w => (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) -
      E * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ)
    (h1HelmholtzForm_inner Ω E) b u

theorem normalizedNeumannPoisson_isSolution {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (b : L2Z) :
    IsNormalizedNeumannSolution Q E b (normalizedNeumannPoisson Q E b) := by
  exact normalized_trace_inverse_solution  (G := L2Z) Q
    (h1HelmholtzForm Ω E)
    (fun v w => (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) -
      E * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ)
    (h1HelmholtzForm_inner Ω E) hE b

theorem normalizedNeumannBoundary_isSelfAdjoint :
    IsSelfAdjoint (normalizedNeumannBoundary Q E) := normalized_trace_sandwich_isSelfAdjoint  (G := L2Z) Q
      (h1HelmholtzResolvent Ω E) (h1HelmholtzResolvent_isSelfAdjoint Ω E)

include E₀ in
def normalizedNeumannResidue : FourierOp :=
  ((E₀ + 1 : ℝ) : ℂ) •
    (Q ∘L (h1ResonantSpace Ω E₀).starProjection ∘L ContinuousLinearMap.adjoint Q)

include E E₀ in
def normalizedNeumannRegular : FourierOp :=
  Q ∘L h1RegularResolvent Ω E₀ E ∘L ContinuousLinearMap.adjoint Q

end

theorem normalizedNeumannBoundary_eq_pole_add_regular
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E₀ E : ℝ}
    (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀) (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    normalizedNeumannBoundary Q E =
      (-((E - E₀ : ℝ) : ℂ)⁻¹) • normalizedNeumannResidue Q E₀ +
        normalizedNeumannRegular Q E₀ E := by
  
  refine normalized_trace_sandwich_pole  (G := L2Z) Q ?_
    (h1HelmholtzResolvent_eq_pole_add_regular hb hL hE₀ hne hunit)
  ring

end

end PolyaNeumann

end
