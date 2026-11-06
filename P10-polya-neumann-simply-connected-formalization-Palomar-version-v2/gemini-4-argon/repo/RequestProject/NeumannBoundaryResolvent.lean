module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Algebra.Star.Basic
public import RequestProject.TraceH1
public import RequestProject.NeumannMultiplicity
public import RequestProject.FiniteRankCompletion

/-!
# The genuine L² Neumann-to-Dirichlet map

With the shifted energy inner product on H¹, the weak Helmholtz form is
`B_E = I - (E + 1) J† J`, where `J` is the actual inclusion into L²(Ω).
The min–max nonresonance condition forces its kernel to vanish. Rellich
compactness and the proved Fredholm alternative then give a bounded inverse.

The Poisson solution is `B_E⁻¹ Trace† g`, and its actual boundary trace is the
L² Neumann-to-Dirichlet map. Boundary measure is ordinary `dθ`, exactly as in
`TraceH1`. This file does not assert the fractional Sobolev mapping properties
or the conformal principal part needed for the later boundary reduction.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory
open scoped Real InnerProductSpace ComplexConjugate

/-- The actual Helmholtz form operator on the shifted-energy H¹ space. -/
def h1HelmholtzForm Ω (E : ℝ) : NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  1 - ((E + 1 : ℝ) : ℂ) •
    ((ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω))

/-- Its inner product is the weak Neumann form minus the energy mass term. -/
theorem h1HelmholtzForm_inner Ω E v u :
    ⟪v, h1HelmholtzForm Ω E u⟫_ℂ =
      (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
        (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ := by
  have key : ∀ c x, ⟪v, c • x⟫_ℂ = c * ⟪v, x⟫_ℂ :=
    fun c x => by
      rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_right]
  simp only [h1HelmholtzForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right]
  rw [key, ContinuousLinearMap.adjoint_inner_right, h1_inner]
  push_cast
  ring

/-- Kernel vectors of the form operator give actual weak Neumann eigenfunctions. -/
theorem h1HelmholtzForm_kernel_mem Ω E u
    (hu : h1HelmholtzForm Ω E u = 0) : h1Value Ω u ∈ neumannEigenspace Ω E := by
  refine ⟨fun i => h1Gradient Ω i u, h1Value_weakGradient Ω u, ?_⟩
  intro v g hg
  have h := h1HelmholtzForm_inner Ω E (h1Vector hg) u
  rw [hu, inner_zero_right, h1Value_h1Vector] at h
  simp only [h1Gradient_h1Vector] at h
  exact sub_eq_zero.mp h.symm

theorem h1HelmholtzForm_injective  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    Function.Injective (h1HelmholtzForm Ω E) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hm := h1HelmholtzForm_kernel_mem Ω E u hu
  rw [show neumannEigenspace Ω E = ⊥ by
    haveI : FiniteDimensional ℂ (neumannEigenspace Ω E) :=
      finiteDimensional_neumannEigenspace hb hL E
    have hr := finrank_neumannEigenspace_le hb hL hE
    rw [(show {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E} = ∅ by
      ext j
      simp [hnr j]), Set.encard_empty] at hr
    exact Submodule.finrank_eq_zero.mp (by
      exact_mod_cast (le_antisymm hr (zero_le))), Submodule.mem_bot] at hm
  apply h1Value_injective hL.1.1
  simpa using hm

/-- Nonresonance implies a bounded inverse of the actual form operator, by
the proved identity-plus-compact Fredholm alternative. -/
theorem h1HelmholtzForm_isUnit  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    IsUnit (h1HelmholtzForm Ω E) := by
  let C := -((E + 1 : ℝ) : ℂ) •
    (ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω)
  have heq : (1 : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) + C = h1HelmholtzForm Ω E := by
    simpa only [C, h1HelmholtzForm, sub_eq_add_neg] using
      congrArg (fun T : NeumannH1 Ω →L[ℂ] NeumannH1 Ω => 1 + T)
        (_root_.neg_smul ((E + 1 : ℝ) : ℂ)
          ((ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω)))
  have hinj : Function.Injective ((1 : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) + C) := by
    rw [heq]
    exact h1HelmholtzForm_injective hb hL hE hnr
  rw [← heq]
  exact isUnit_of_bijective _ ⟨hinj, (injective_iff_surjective_one_add ((((h1Value_isCompactOperator hb hL).clm_comp (ContinuousLinearMap.adjoint (h1Value Ω))).smul (-((E + 1 : ℝ) : ℂ))))).mp hinj⟩

/-- A globally defined inverse; its solution properties below are asserted
only at energies whose nonresonance has been established. -/
def h1HelmholtzResolvent Ω (E : ℝ) : NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  Ring.inverse (h1HelmholtzForm Ω E)

theorem h1HelmholtzResolvent_isSelfAdjoint Ω E :
    IsSelfAdjoint (h1HelmholtzResolvent Ω E) := by
  rw [isSelfAdjoint_iff]
  exact (Ring.inverse_star (h1HelmholtzForm Ω E)).symm.trans
    (congrArg Ring.inverse (show IsSelfAdjoint (h1HelmholtzForm Ω E) by
      exact (IsSelfAdjoint.one (NeumannH1 Ω →L[ℂ] NeumannH1 Ω)).sub
        ((show IsSelfAdjoint ((E + 1 : ℝ) : ℂ) by
          simp [IsSelfAdjoint]).smul (ContinuousLinearMap.isPositive_adjoint_comp_self (h1Value Ω)).isSelfAdjoint)).star_eq)


/-- The weak Helmholtz equation with the actual boundary conormal load.
The boundary trace in the right hand side is the constructed genuine trace. -/
def IsBoundaryNeumannSolution  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : IsBoundaryParam Ω γ)
    (E : ℝ) (g : BoundaryL2) (u : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ =
        ⟪h1BoundaryTrace hb hL hγ v, g⟫_ℂ

theorem isBoundaryNeumannSolution_iff_form_eq {Ω : Set ℂ} hb
    hL {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    E g u :
    IsBoundaryNeumannSolution hb hL hγ E g u ↔
      h1HelmholtzForm Ω E u = h1BoundaryLoad hb hL hγ g := by
  constructor
  · intro hu
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, h1BoundaryLoad_inner]
    exact hu v
  · intro hu v
    rw [← h1HelmholtzForm_inner, hu, h1BoundaryLoad_inner]



end PolyaNeumann

end
