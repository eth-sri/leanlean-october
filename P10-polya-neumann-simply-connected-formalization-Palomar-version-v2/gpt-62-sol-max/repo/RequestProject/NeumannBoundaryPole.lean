module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import RequestProject.NeumannBoundaryResolvent

/-!
# The actual Neumann boundary pole

The resonant space is the kernel of the genuine H¹ Helmholtz operator.
Its orthogonal complement is fixed at the reference energy. Fredholm
invertibility on that complement gives a continuous regular resolvent at
the reference energy, including at resonance. The full inverse at nearby
nonresonant energies then has an exact pole, and taking the actual trace
on both sides gives the finite-rank residue of the actual L² NtD map.

All boundary spaces use ordinary coordinate measure `dθ`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

/-- The resonance space of the actual form operator at the reference energy. -/
def h1ResonantSpace (Ω : Set ℂ) (E₀ : ℝ) : Submodule ℂ (NeumannH1 Ω) :=
  (h1HelmholtzForm Ω E₀).ker

instance (Ω : Set ℂ) (E₀ : ℝ) : CompleteSpace (h1ResonantSpace Ω E₀) :=
  (h1HelmholtzForm Ω E₀).isClosed_ker.completeSpace_coe

instance h1ComplementNormedSpace (Ω : Set ℂ) (E₀ : ℝ) :
    NormedSpace ℂ (h1ResonantSpace Ω E₀)ᗮ :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (h1ResonantSpace Ω E₀)ᗮ

instance h1ComplementEndSMul (Ω : Set ℂ) (E₀ : ℝ) :
    SMul ℂ ((h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ) :=
  ContinuousLinearMap.instSMul (S₂ := ℂ) (σ₁₂ := RingHom.id ℂ)
    (M₁ := (h1ResonantSpace Ω E₀)ᗮ) (M₂ := (h1ResonantSpace Ω E₀)ᗮ)

theorem finiteDimensional_h1ResonantSpace {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (E₀ : ℝ) :
    FiniteDimensional ℂ (h1ResonantSpace Ω E₀) := by
  let C := -((E₀ + 1 : ℝ) : ℂ) • h1MassOperator Ω
  have hC : IsCompactOperator C := h1HelmholtzForm_compact_part hb hL E₀
  have heq : (1 : NeumannH1 Ω →L[ℂ] NeumannH1 Ω) + C = h1HelmholtzForm Ω E₀ := by
    simpa only [C, h1HelmholtzForm, h1MassOperator, sub_eq_add_neg] using
      congrArg (fun T : NeumannH1 Ω →L[ℂ] NeumannH1 Ω => 1 + T)
        (_root_.neg_smul ((E₀ + 1 : ℝ) : ℂ) (h1MassOperator Ω))
  have hf := finiteDimensional_ker_one_add hC
  rw [heq] at hf
  exact hf

theorem h1ResonantMass_eq_inverse_smul {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {u : NeumannH1 Ω} (hu : u ∈ h1ResonantSpace Ω E₀) :
    h1MassOperator Ω u = (((E₀ + 1 : ℝ) : ℂ)⁻¹) • u := by
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show E₀ + 1 ≠ 0 by linarith)
  change u - ((E₀ + 1 : ℝ) : ℂ) • h1MassOperator Ω u = 0 at hu
  simpa only [inv_smul_smul₀ hc] using
    congrArg (fun v : NeumannH1 Ω => ((E₀ + 1 : ℝ) : ℂ)⁻¹ • v) (sub_eq_zero.mp hu).symm

theorem h1MassOperator_preserves_resonantComplement {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {u : NeumannH1 Ω} (hu : u ∈ (h1ResonantSpace Ω E₀)ᗮ) :
    h1MassOperator Ω u ∈ (h1ResonantSpace Ω E₀)ᗮ := by
  rw [Submodule.mem_orthogonal] at hu ⊢
  intro v hv
  calc
    _ = ⟪h1MassOperator Ω v, u⟫_ℂ := ((h1MassOperator_isSelfAdjoint Ω).isSymmetric v u).symm
    _ = 0 := by
      rw [h1ResonantMass_eq_inverse_smul hE₀ hv]
      exact hu _ ((h1ResonantSpace Ω E₀).smul_mem _ hv)

/-- Compression of the actual mass operator to the fixed orthogonal
complement. Invariance is proved above from the actual self-adjoint form. -/
def h1ComplementMass (Ω : Set ℂ) (E₀ : ℝ) :
    (h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ :=
  (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection ∘L h1MassOperator Ω ∘L
    (h1ResonantSpace Ω E₀)ᗮ.subtypeL

theorem h1ComplementMass_coe_eq {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (u : (h1ResonantSpace Ω E₀)ᗮ) :
    (h1ComplementMass Ω E₀ u : NeumannH1 Ω) = h1MassOperator Ω u :=   Submodule.starProjection_eq_self_iff.mpr (h1MassOperator_preserves_resonantComplement hE₀ u.property)

theorem h1ComplementMass_isCompactOperator {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (E₀ : ℝ) :
    IsCompactOperator (h1ComplementMass Ω E₀) :=
  ((h1MassOperator_isCompactOperator hb hL).comp_clm
    (h1ResonantSpace Ω E₀)ᗮ.subtypeL).clm_comp
      (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection

/-- The genuine form operator on the fixed complement, at a varying energy. -/
def h1ComplementForm (Ω : Set ℂ) (E₀ E : ℝ) :
    (h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ :=
  1 - ((E + 1 : ℝ) : ℂ) • h1ComplementMass Ω E₀

theorem h1ComplementForm_coe_eq {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (E : ℝ) (u : (h1ResonantSpace Ω E₀)ᗮ) :
    (h1ComplementForm Ω E₀ E u : NeumannH1 Ω) = h1HelmholtzForm Ω E u := by
  simp only [h1ComplementForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,
    Submodule.coe_sub, Submodule.coe_smul, h1ComplementMass_coe_eq hE₀]
  rfl

/-- At the reference energy the genuine complement operator is injective:
a vector in both the actual kernel and its orthogonal complement is zero. -/
theorem h1ComplementForm_injective {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    Function.Injective (h1ComplementForm Ω E₀ E₀) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hzero : h1HelmholtzForm Ω E₀ (u : NeumannH1 Ω) = 0 := by
    rw [← h1ComplementForm_coe_eq hE₀ E₀ u, hu]
    rfl
  have hker := hzero
  have hinner := ((h1ResonantSpace Ω E₀).mem_orthogonal u).1 u.property u hker
  apply Subtype.ext
  exact inner_self_eq_zero.mp hinner

/-- The proved Fredholm alternative supplies invertibility on the fixed
complement at the reference energy, including at resonance. -/
theorem h1ComplementForm_isUnit {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    IsUnit (h1ComplementForm Ω E₀ E₀) := by
  exact @isUnit_one_sub_smul_of_compact _ _ (h1ComplementNormedSpace Ω E₀) _ (h1ComplementMass Ω E₀)
    (h1ComplementMass_isCompactOperator hb hL E₀) ((E₀ + 1 : ℝ) : ℂ)
    (h1ComplementForm_injective hE₀)

theorem continuous_h1ComplementForm (Ω : Set ℂ) (E₀ : ℝ) :
    Continuous (h1ComplementForm Ω E₀) := by
  unfold h1ComplementForm
  fun_prop

/-- A neighbourhood in which the complement inverse is genuine and
continuous in operator norm. The reference energy belongs to it. -/
theorem h1ComplementForm_isUnit_near {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    ∃ U ∈ 𝓝 E₀, (∀ E ∈ U, IsUnit (h1ComplementForm Ω E₀ E)) ∧
      ContinuousOn (fun E => Ring.inverse (h1ComplementForm Ω E₀ E)) U := by
  let f := h1ComplementForm Ω E₀
  have hc := continuous_h1ComplementForm Ω E₀
  refine ⟨f ⁻¹' {x | IsUnit x}, (Units.isOpen.preimage hc).mem_nhds
    (h1ComplementForm_isUnit hb hL hE₀), fun _ h => h, ?_⟩
  rintro E ⟨u, hu⟩
  exact ((hu ▸ NormedRing.inverse_continuousAt u).comp hc.continuousAt).continuousWithinAt

/-- The regular H¹ resolvent, obtained from the actual complement inverse.
It retains its correct value at the reference energy. -/
def h1RegularResolvent (Ω : Set ℂ) (E₀ E : ℝ) : NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  (h1ResonantSpace Ω E₀)ᗮ.subtypeL ∘L
    (Ring.inverse (h1ComplementForm Ω E₀ E) ∘L (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection :
      NeumannH1 Ω →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ)

private lemma h1HelmholtzForm_on_resonantSpace {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (E : ℝ) {u : NeumannH1 Ω} (hu : u ∈ h1ResonantSpace Ω E₀) :
    h1HelmholtzForm Ω E u =
      (((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ)) • u := by
  change u - ((E + 1 : ℝ) : ℂ) • h1MassOperator Ω u = _
  rw [h1ResonantMass_eq_inverse_smul hE₀ hu, smul_smul]
  nth_rw 1 [← one_smul ℂ u]
  rw [← sub_smul]
  congr 1
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show E₀ + 1 ≠ 0 by linarith)
  field_simp [hc]
  push_cast
  ring

theorem apply_ringInverse_of_isUnit {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : X →L[ℂ] X) (hA : IsUnit A) (x : X) : A (Ring.inverse A x) = x :=
  congrArg (fun B : X →L[ℂ] X => B x) (Ring.mul_inverse_cancel A hA)

theorem h1RegularResolvent_projected_solve {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω E (h1RegularResolvent Ω E₀ E u) =
      (h1ResonantSpace Ω E₀)ᗮ.starProjection u := by
  let x := (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection u
  change h1HelmholtzForm Ω E (↑(Ring.inverse (h1ComplementForm Ω E₀ E) x)) = (x : NeumannH1 Ω)
  rw [← h1ComplementForm_coe_eq hE₀]
  exact congrArg Subtype.val (@apply_ringInverse_of_isUnit _ _ (h1ComplementNormedSpace Ω E₀) _ hunit x)

private lemma h1PoleCandidate_solve {Ω : Set ℂ}
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀)
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω E
      ((-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
        (h1ResonantSpace Ω E₀).starProjection u + h1RegularResolvent Ω E₀ E u) = u := by
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show E₀ + 1 ≠ 0 by linarith)
  have hd : ((E - E₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hne)
  have hscalar : (-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) *
      (((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ)) = 1 := by
    field_simp [hc, hd]
    push_cast
    ring
  rw [map_add, map_smul, h1HelmholtzForm_on_resonantSpace hE₀ E
      (Submodule.starProjection_apply_mem _ _), h1RegularResolvent_projected_solve hE₀ hunit,
    smul_smul, hscalar, one_smul, Submodule.starProjection_orthogonal_val]
  abel

/-- The explicit pole candidate is a right inverse away from the reference
energy. Self-adjointness then gives injectivity, without
assuming nonresonance or solvability at the varying energy. -/
theorem h1HelmholtzForm_isUnit_off_reference {Ω : Set ℂ}
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀)
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    IsUnit (h1HelmholtzForm Ω E) := by
  have hsurj : Function.Surjective (h1HelmholtzForm Ω E) := fun u =>
    ⟨(-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
      (h1ResonantSpace Ω E₀).starProjection u + h1RegularResolvent Ω E₀ E u,
      h1PoleCandidate_solve hE₀ hne hunit u⟩
  refine isUnit_of_bijective _ ⟨(injective_iff_map_eq_zero _).2 ?_, hsurj⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h := (h1HelmholtzForm_isSelfAdjoint Ω E).isSymmetric y (h1HelmholtzForm Ω E y)
  simpa only [ContinuousLinearMap.coe_coe, hx, inner_zero_right, inner_self_eq_zero] using h

/-- The exact pole formula for the genuine H¹ inverse. The complement is
invertible near the reference energy by the theorem above; invertibility
of the full operator away from the reference point is proved explicitly. -/
theorem h1HelmholtzResolvent_eq_pole_add_regular {Ω : Set ℂ}
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀)
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    h1HelmholtzResolvent Ω E =
      (-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
        (h1ResonantSpace Ω E₀).starProjection + h1RegularResolvent Ω E₀ E := by
  have hu := h1HelmholtzForm_isUnit_off_reference hE₀ hne hunit
  apply ContinuousLinearMap.ext
  intro u
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  have hleft : h1HelmholtzForm Ω E (h1HelmholtzResolvent Ω E u) = u := by
    change h1HelmholtzForm Ω E (Ring.inverse (h1HelmholtzForm Ω E) u) = u
    rw [← ContinuousLinearMap.mul_apply,
      Ring.mul_inverse_cancel _ hu,
      ContinuousLinearMap.one_apply]
  rw [hleft]
  exact (h1PoleCandidate_solve hE₀ hne hunit u).symm



end PolyaNeumann

end
