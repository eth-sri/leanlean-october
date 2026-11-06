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
def h1HelmholtzForm (Ω : Set ℂ) (E : ℝ) : NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  1 - ((E + 1 : ℝ) : ℂ) •
    ((ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω))

/-- Its inner product is the weak Neumann form minus the energy mass term. -/
theorem h1HelmholtzForm_inner (Ω : Set ℂ) (E : ℝ) (v u : NeumannH1 Ω) :
    ⟪v, h1HelmholtzForm Ω E u⟫_ℂ =
      (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
        (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ := by
  have key : ∀ (c : ℂ) (x : NeumannH1 Ω), ⟪v, c • x⟫_ℂ = c * ⟪v, x⟫_ℂ :=
    fun c x => by
      rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_right]
  simp only [h1HelmholtzForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right]
  rw [key, ContinuousLinearMap.adjoint_inner_right, h1_inner]
  push_cast
  ring

theorem h1HelmholtzForm_isSelfAdjoint (Ω : Set ℂ) (E : ℝ) :
    IsSelfAdjoint (h1HelmholtzForm Ω E) := by
  have hc : IsSelfAdjoint ((E + 1 : ℝ) : ℂ) := by
    simp [IsSelfAdjoint]
  have hId : IsSelfAdjoint (1 : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) :=
    IsSelfAdjoint.one (NeumannH1 Ω →L[ℂ] NeumannH1 Ω)
  exact hId.sub
    (hc.smul (ContinuousLinearMap.isPositive_adjoint_comp_self (h1Value Ω)).isSelfAdjoint)

/-- Kernel vectors of the form operator give actual weak Neumann eigenfunctions. -/
theorem h1HelmholtzForm_kernel_mem (Ω : Set ℂ) (E : ℝ) (u : NeumannH1 Ω)
    (hu : h1HelmholtzForm Ω E u = 0) : h1Value Ω u ∈ neumannEigenspace Ω E := by
  refine ⟨fun i => h1Gradient Ω i u, h1Value_weakGradient Ω u, ?_⟩
  intro v g hg
  have h := h1HelmholtzForm_inner Ω E (h1Vector hg) u
  rw [hu, inner_zero_right, h1Value_h1Vector] at h
  simp only [h1Gradient_h1Vector] at h
  exact sub_eq_zero.mp h.symm

/-- The min–max nonresonance condition makes the genuine weak eigenspace zero.
Only the previously proved multiplicity inequality is used. -/
theorem neumannEigenspace_eq_bot_of_nonresonant {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    neumannEigenspace Ω E = ⊥ := by
  haveI : FiniteDimensional ℂ (neumannEigenspace Ω E) :=
    finiteDimensional_neumannEigenspace hb hL E
  have hempty : {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E} = ∅ := by
    ext j
    simp [hnr j]
  have hr := finrank_neumannEigenspace_le hb hL hE
  rw [hempty, Set.encard_empty] at hr
  have hr0 : (Module.finrank ℂ (neumannEigenspace Ω E) : ℕ∞) = 0 :=
    le_antisymm hr (zero_le)
  have hrnat : Module.finrank ℂ (neumannEigenspace Ω E) = 0 := by
    exact_mod_cast hr0
  exact Submodule.finrank_eq_zero.mp hrnat

theorem h1HelmholtzForm_injective {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    Function.Injective (h1HelmholtzForm Ω E) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hm := h1HelmholtzForm_kernel_mem Ω E u hu
  rw [neumannEigenspace_eq_bot_of_nonresonant hb hL hE hnr, Submodule.mem_bot] at hm
  apply h1Value_injective hL.1.1
  simpa using hm

/-- Rellich compactness supplies the compact perturbation in the form operator. -/
theorem h1HelmholtzForm_compact_part {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (E : ℝ) :
    IsCompactOperator (-((E + 1 : ℝ) : ℂ) •
      ((ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω))) := by
  have h := ((h1Value_isCompactOperator hb hL).clm_comp
    (ContinuousLinearMap.adjoint (h1Value Ω))).smul (-((E + 1 : ℝ) : ℂ))
  exact h

/-- Nonresonance implies a bounded inverse of the actual form operator, by
the proved identity-plus-compact Fredholm alternative. -/
theorem h1HelmholtzForm_isUnit {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    IsUnit (h1HelmholtzForm Ω E) := by
  let C : NeumannH1 Ω →L[ℂ] NeumannH1 Ω := -((E + 1 : ℝ) : ℂ) •
    ((ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω))
  have hC : IsCompactOperator C := h1HelmholtzForm_compact_part hb hL E
  have heq : (1 : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) + C = h1HelmholtzForm Ω E := by
    simpa only [C, h1HelmholtzForm, sub_eq_add_neg] using
      congrArg (fun T : NeumannH1 Ω →L[ℂ] NeumannH1 Ω => 1 + T)
        (_root_.neg_smul ((E + 1 : ℝ) : ℂ)
          ((ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω)))
  have hinj : Function.Injective ((1 : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) + C) := by
    rw [heq]
    exact h1HelmholtzForm_injective hb hL hE hnr
  rw [← heq]
  exact isUnit_of_bijective _ ⟨hinj, (injective_iff_surjective_one_add hC).mp hinj⟩

/-- A globally defined inverse; its solution properties below are asserted
only at energies whose nonresonance has been established. -/
def h1HelmholtzResolvent (Ω : Set ℂ) (E : ℝ) : NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  Ring.inverse (h1HelmholtzForm Ω E)

theorem h1HelmholtzResolvent_isSelfAdjoint (Ω : Set ℂ) (E : ℝ) :
    IsSelfAdjoint (h1HelmholtzResolvent Ω E) := by
  rw [isSelfAdjoint_iff]
  change star (Ring.inverse (h1HelmholtzForm Ω E)) = Ring.inverse (h1HelmholtzForm Ω E)
  exact (Ring.inverse_star (h1HelmholtzForm Ω E)).symm.trans
    (congrArg Ring.inverse (h1HelmholtzForm_isSelfAdjoint Ω E).star_eq)

/-- The actual H¹ solution with prescribed L² conormal density. -/
def neumannBoundaryPoisson {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) :
    BoundaryL2 →L[ℂ] NeumannH1 Ω :=
  (h1HelmholtzResolvent Ω E).comp (h1BoundaryLoad hb hL hγ)

/-- The weak Helmholtz equation with the actual boundary conormal load.
The boundary trace in the right hand side is the constructed genuine trace. -/
def IsBoundaryNeumannSolution {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (E : ℝ) (g : BoundaryL2) (u : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ =
        ⟪h1BoundaryTrace hb hL hγ v, g⟫_ℂ

theorem isBoundaryNeumannSolution_iff_form_eq {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (E : ℝ) (g : BoundaryL2) (u : NeumannH1 Ω) :
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

/-- The genuine L² Neumann-to-Dirichlet map is the actual trace of the unique
variational solution at nonresonant energies. -/
def neumannToDirichletL2 {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) :
    BoundaryL2 →L[ℂ] BoundaryL2 :=
  (h1BoundaryTrace hb hL hγ).comp (neumannBoundaryPoisson hb hL hγ E)

@[simp] theorem neumannToDirichletL2_apply {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (E : ℝ) (g : BoundaryL2) :
    neumannToDirichletL2 hb hL hγ E g =
      h1BoundaryTrace hb hL hγ (neumannBoundaryPoisson hb hL hγ E g) := rfl

end PolyaNeumann

end
