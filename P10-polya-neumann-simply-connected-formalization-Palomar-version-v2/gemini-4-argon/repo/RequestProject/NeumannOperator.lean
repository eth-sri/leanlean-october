module

public import RequestProject.NeumannSobolev
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The actual Neumann operator and its shifted resolvent

The inverse of the Hilbert form `q + ⟨·,·⟩` is constructed by the
adjoint of the genuine H¹ inclusion. This gives a single-valued, densely
defined Neumann operator, with exactly the weak equation already used in
the eigenspace definitions.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ}

/-- The shifted form resolvent: `K = (A_N + I)⁻¹ = J J†`. -/
def neumannResolvent Ω : L2 Ω →L[ℂ] L2 Ω :=
  (h1Value Ω).comp (ContinuousLinearMap.adjoint (h1Value Ω))


theorem neumannResolvent_inner Ω f g :
    ⟪neumannResolvent Ω f, g⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint (h1Value Ω) f,
        ContinuousLinearMap.adjoint (h1Value Ω) g⟫_ℂ :=
  (ContinuousLinearMap.adjoint_inner_right (h1Value Ω)
    (ContinuousLinearMap.adjoint (h1Value Ω) f) g).symm

theorem neumannResolvent_isPositive Ω : (neumannResolvent Ω).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint (h1Value Ω)

local notation "Φ0" => h1Value Ω

theorem neumannResolvent_compact  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : IsCompactOperator (neumannResolvent Ω) :=
  (h1Value_isCompactOperator hb hL).comp_clm (ContinuousLinearMap.adjoint (Φ0))

local notation "Φ2" => IsOpen Ω

theorem h1Value_adjoint_eq_zero_iff  (hΩ : Φ2) f :
    ContinuousLinearMap.adjoint (h1Value Ω) f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply eq_zero_of_inner_h1 hΩ f
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_right (Φ0) u f, hf, inner_zero_right]
  · rintro rfl
    exact map_zero _

theorem neumannResolvent_strictPositive  (hΩ : Φ2)
    f (hf : f ≠ 0) : 0 < (⟪neumannResolvent Ω f, f⟫_ℂ).re := by
  rw [neumannResolvent_inner]
  exact (re_inner_self_pos (𝕜 := ℂ)).mpr (by
    intro h
    exact hf ((h1Value_adjoint_eq_zero_iff hΩ f).mp h))

/-- The inverse shifted operator, before subtracting the identity. -/
def neumannShiftedOperator Ω : L2 Ω →ₗ.[ℂ] L2 Ω :=
  ((neumannResolvent Ω).toLinearMap.toPMap ⊤).inverse

theorem neumannShiftedOperator_domain Ω :
    (neumannShiftedOperator Ω).domain = (neumannResolvent Ω).range := by
  rw [neumannShiftedOperator, LinearPMap.inverse_domain]
  ext f
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, Submodule.mem_top⟩, hv⟩

def neumannShiftedVector Ω (f : L2 Ω) : (neumannShiftedOperator Ω).domain :=
  ⟨neumannResolvent Ω f, by rw [neumannShiftedOperator_domain]; exact ⟨f, rfl⟩⟩


local notation "Φ3" => neumannShiftedOperator Ω

local notation "Φ4" => neumannResolvent Ω

theorem neumannShiftedOperator_apply_vector  (hΩ : Φ2) f :
    Φ3 (neumannShiftedVector Ω f) = f := by
  exact LinearPMap.inverse_apply_eq (by
    rw [LinearPMap.ker_eq_bot']
    intro u hu
    apply Subtype.ext
    exact (show Function.Injective (Φ4) by
      change Function.Injective (Φ4).toLinearMap
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro f hf
      change Φ4 f = 0 at hf
      exact (h1Value_adjoint_eq_zero_iff hΩ f).mp (by
        apply (inner_self_eq_zero (𝕜 := ℂ)).mp
        rw [← neumannResolvent_inner Ω f f, hf, inner_zero_left])).eq_iff.mp
      (by rw [ZeroMemClass.coe_zero, map_zero]; exact hu)) (x := ⟨f, Submodule.mem_top⟩) rfl

theorem neumannResolvent_shiftedOperator  (hΩ : Φ2)
    u :
    Φ4 (Φ3 u) = (u : L2 Ω) := by
  obtain ⟨f, hf⟩ : ∃ f, Φ4 f = u := by
    have hu : (u : L2 Ω) ∈ (Φ4).range := by
      simpa [neumannShiftedOperator_domain] using u.property
    exact hu
  rw [(Subtype.ext hf.symm : u = neumannShiftedVector Ω f), neumannShiftedOperator_apply_vector hΩ]
  rfl

theorem neumannShiftedOperator_form_representation  (hΩ : Φ2)
    u f :
    (∃ hu : Φ0 u ∈ (Φ3).domain,
      Φ3 ⟨Φ0 u, hu⟩ = f) ↔
      ∀ v : NeumannH1 Ω, ⟪v, u⟫_ℂ = ⟪h1Value Ω v, f⟫_ℂ := by
  constructor
  · rintro ⟨hu, huf⟩
    have hJu := neumannResolvent_shiftedOperator hΩ ⟨Φ0 u, hu⟩
    rw [huf] at hJu
    have huadj : u = ContinuousLinearMap.adjoint (Φ0) f :=
      h1Value_injective hΩ hJu.symm
    intro v
    rw [huadj]
    exact ContinuousLinearMap.adjoint_inner_right (Φ0) v f
  · intro huf
    have hJu : Φ0 u = Φ4 f := by rw [show u = ContinuousLinearMap.adjoint (Φ0) f by
      apply ext_inner_left ℂ
      intro v
      exact (huf v).trans (ContinuousLinearMap.adjoint_inner_right (Φ0) v f).symm]; rfl
    have hm : Φ0 u ∈ (Φ3).domain := by
      rw [neumannShiftedOperator_domain]
      exact ⟨f, hJu.symm⟩
    refine ⟨hm, ?_⟩
    rw [(Subtype.ext hJu : (⟨Φ0 u, hm⟩ : (Φ3).domain) = neumannShiftedVector Ω f)]
    exact neumannShiftedOperator_apply_vector hΩ f

/-- The Neumann Laplacian itself, obtained by subtracting the shift. -/
def neumannOperator Ω : L2 Ω →ₗ.[ℂ] L2 Ω where
  domain := (neumannShiftedOperator Ω).domain
  toFun := (neumannShiftedOperator Ω).toFun - (neumannShiftedOperator Ω).domain.subtype

@[simp] theorem neumannOperator_domain Ω :
    (neumannOperator Ω).domain = (neumannResolvent Ω).range :=
  neumannShiftedOperator_domain Ω

@[simp] theorem neumannOperator_apply Ω u :
    neumannOperator Ω u = neumannShiftedOperator Ω u - (u : L2 Ω) := rfl

/-- Representation by the actual gradient form, with no spectral assumptions. -/
local notation "Φ1" => neumannOperator Ω

theorem neumannOperator_form_representation  (hΩ : Φ2)
    u f :
    (∃ hu : Φ0 u ∈ (Φ1).domain,
      Φ1 ⟨Φ0 u, hu⟩ = f) ↔
      ∀ v : NeumannH1 Ω,
        ∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ = ⟪h1Value Ω v, f⟫_ℂ := by
  rw [show (∃ hu : Φ0 u ∈ (Φ1).domain, Φ1 ⟨Φ0 u, hu⟩ = f) ↔ (∃ hu : Φ0 u ∈ (Φ3).domain, Φ3 ⟨Φ0 u, hu⟩ = f + Φ0 u) by
    change (∃ hu : Φ0 u ∈ (Φ3).domain,
      Φ3 ⟨Φ0 u, hu⟩ - Φ0 u = f) ↔ _
    simp [sub_eq_iff_eq_add], neumannShiftedOperator_form_representation hΩ u (f + Φ0 u)]
  apply forall_congr'
  intro v
  rw [h1_inner, inner_add_right, add_comm (inner ℂ (Φ0 v) f), add_left_cancel_iff]

theorem neumannOperator_mem_H1  (hΩ : Φ2)
    (u : (Φ1).domain) : (u : L2 Ω) ∈ H1 Ω := by
  rw [← h1Value_range]
  refine ⟨ContinuousLinearMap.adjoint (Φ0) (Φ3 u), ?_⟩
  exact neumannResolvent_shiftedOperator hΩ u

/-- The operator graph agrees with the genuine weak Neumann equation. -/
theorem neumannOperator_weak_representation  (hΩ : Φ2)
    (u f : L2 Ω) :
    (∃ hu : u ∈ (Φ1).domain, Φ1 ⟨u, hu⟩ = f) ↔
      ∃ g, IsWeakGradient Ω u g ∧ ∀ v h, IsWeakGradient Ω v h →
        ∑ i, ⟪h i, g i⟫_ℂ = ⟪v, f⟫_ℂ := by
  constructor
  · rintro ⟨hu, huf⟩
    obtain ⟨g, hg⟩ := neumannOperator_mem_H1 hΩ ⟨u, hu⟩
    refine ⟨g, hg, fun v h hv => ?_⟩
    simpa using ((neumannOperator_form_representation hΩ (h1Vector hg) f).mp ⟨hu, huf⟩) (h1Vector hv)
  · rintro ⟨g, hg, hw⟩
    apply (neumannOperator_form_representation hΩ (h1Vector hg) f).mpr
    intro v
    exact hw _ _ (h1Value_weakGradient Ω v)

/-- Operator eigenvectors, viewed in the ambient L² space. -/
def neumannOperatorEigenspace Ω (E : ℝ) : Submodule ℂ (L2 Ω) :=
  ((neumannOperator Ω).toFun - (E : ℂ) • (neumannOperator Ω).domain.subtype).ker.map
    (neumannOperator Ω).domain.subtype

theorem mem_neumannOperatorEigenspace_iff Ω E u :
    u ∈ neumannOperatorEigenspace Ω E ↔
      ∃ hu : u ∈ (neumannOperator Ω).domain,
        neumannOperator Ω ⟨u, hu⟩ = (E : ℂ) • u := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.property, ?_⟩
    have h := LinearMap.mem_ker.mp hv
    change neumannOperator Ω v - E • v = 0 at h
    exact sub_eq_zero.mp h
  · rintro ⟨hu, hAu⟩
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact sub_eq_zero.mpr hAu

/-- Exact identification, including the zero eigenvalue and multiplicities. -/
theorem neumannOperatorEigenspace_eq  (hΩ : Φ2) E :
    neumannOperatorEigenspace Ω E = neumannEigenspace Ω E := by
  ext u
  rw [mem_neumannOperatorEigenspace_iff, neumannOperator_weak_representation hΩ]
  simp only [inner_smul_right]
  rfl

theorem neumannOperator_nonneg  (hΩ : Φ2)
    (u : (Φ1).domain) :
    0 ≤ (⟪(u : L2 Ω), neumannOperator Ω u⟫_ℂ).re := by
  obtain ⟨g, hg, hw⟩ := (neumannOperator_weak_representation hΩ u
    (Φ1 u)).mp ⟨u.property, rfl⟩
  have h := congrArg Complex.re (hw u g hg)
  rw [Complex.re_sum] at h
  rw [← h]
  exact Finset.sum_nonneg fun i _ => inner_self_nonneg (𝕜 := ℂ)

def neumannOperatorVector Ω (f : L2 Ω) : (neumannOperator Ω).domain :=
  neumannShiftedVector Ω f


theorem neumannResolvent_operator  (hΩ : Φ2)
    u :
    Φ4 (Φ1 u + (u : L2 Ω)) = (u : L2 Ω) := by
  rw [neumannOperator_apply, sub_add_cancel]
  exact neumannResolvent_shiftedOperator hΩ u

/-- The inverse spectral parameter is proved from both resolvent identities. -/
theorem neumannOperator_eigen_iff_resolvent  (hΩ : Φ2)
    (c : ℂ) (hc : c + 1 ≠ 0) u :
    (∃ hu : u ∈ (Φ1).domain,
      Φ1 ⟨u, hu⟩ = c • u) ↔
      neumannResolvent Ω u = (c + 1)⁻¹ • u := by
  constructor
  · rintro ⟨hu, hAu⟩
    have h := neumannResolvent_operator hΩ ⟨u, hu⟩
    rw [hAu, show c • u + u = (c + 1) • u by rw [add_smul, one_smul], map_smul] at h
    calc
      _ = _ := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = _ := congrArg ((c + 1)⁻¹ • ·) h
  · intro hK
    have hKu : Φ4 ((c + 1) • u) = u := by
      rw [map_smul, hK, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hm : u ∈ (Φ1).domain := by
      rw [neumannOperator_domain]
      exact ⟨(c + 1) • u, hKu⟩
    refine ⟨hm, ?_⟩
    have h_inl f : Φ1 (neumannOperatorVector Ω f) = f - Φ4 f := by
      rw [neumannOperator_apply]
      exact congrArg (fun x => x - Φ4 f)
        (neumannShiftedOperator_apply_vector hΩ f)
    rw [(Subtype.ext hKu.symm : (⟨u, hm⟩ : (Φ1).domain) = neumannOperatorVector Ω ((c + 1) • u)), h_inl, hKu, add_smul, one_smul, add_sub_cancel_right]

end PolyaNeumann

end
