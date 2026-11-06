module

public import RequestProject.PlanarTypes

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
open scoped InnerProductSpace

private lemma isUnit_one_sub_smul_of_compact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (M : X →L[ℂ] X) (hM : IsCompactOperator M) (c : ℂ)
    (hinj : Function.Injective ((1 : X →L[ℂ] X) - c • M)) :
    IsUnit ((1 : X →L[ℂ] X) - c • M) := by
  let C  := -c • M
  have hC : IsCompactOperator C := by
    exact hM.smul (-c)
  have heq : (1 : X →L[ℂ] X) + C = 1 - c • M := by
    module
  have hinj'  := heq.symm ▸ hinj
  have hunit  :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj', (injective_iff_surjective_one_add hC).mp hinj'⟩
  exact heq ▸ hunit

private lemma continuous_inverse_near_unit
    {A : Type*} [NormedRing A] [CompleteSpace A]
    (B : ℝ → A) (hB : Continuous B) E₀ (hunit : IsUnit (B E₀)) :
    ∃ U ∈ 𝓝 E₀, (∀ E ∈ U, IsUnit (B E)) ∧
      ContinuousOn (fun E => Ring.inverse (B E)) U := by
  refine ⟨B ⁻¹' {x | IsUnit x}, (Units.isOpen.preimage hB).mem_nhds hunit,
    fun E hE => hE, ?_⟩
  intro E hE
  obtain ⟨u, hu⟩ := hE
  have hi  :=
    hu ▸ NormedRing.inverse_continuousAt u
  fun_prop

/-- The actual compact mass operator in the shifted-energy H¹ space. -/
def h1MassOperator (Ω : PlanarSet) : ComplexEnd (NeumannH1 Ω) :=
  (ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω)

theorem h1MassOperator_isSelfAdjoint Ω :
    IsSelfAdjoint (h1MassOperator Ω) :=
  (ContinuousLinearMap.isPositive_adjoint_comp_self (h1Value Ω)).isSelfAdjoint

theorem h1MassOperator_isCompactOperator  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : IsCompactOperator (h1MassOperator Ω) :=
  (h1Value_isCompactOperator hb hL).clm_comp (ContinuousLinearMap.adjoint (h1Value Ω))

/-- The resonance space of the actual form operator at the reference energy. -/
def h1ResonantSpace Ω E₀  :=
  (h1HelmholtzForm Ω E₀).ker

instance (Ω : PlanarSet) (E₀ : ℝ) : CompleteSpace (h1ResonantSpace Ω E₀) :=
  (h1HelmholtzForm Ω E₀).isClosed_ker.completeSpace_coe

instance h1ComplementNormedSpace (Ω : PlanarSet) (E₀ : ℝ) :
    NormedSpace ℂ (h1ResonantSpace Ω E₀)ᗮ :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (h1ResonantSpace Ω E₀)ᗮ

instance h1ComplementEndSMul (Ω : PlanarSet) (E₀ : ℝ) :
    SMul ℂ ((h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ) :=
  ContinuousLinearMap.instSMul (S₂ := ℂ) (σ₁₂ := RingHom.id ℂ)
    (M₁ := (h1ResonantSpace Ω E₀)ᗮ) (M₂ := (h1ResonantSpace Ω E₀)ᗮ)

theorem finiteDimensional_h1ResonantSpace  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) E₀ :
    FiniteDimensional ℂ (h1ResonantSpace Ω E₀) := by
  let C  := -((E₀ + 1 : ℝ) : ℂ) • h1MassOperator Ω
  have hC : IsCompactOperator C := by
    exact
      (h1MassOperator_isCompactOperator hb hL).smul (-((E₀ + 1 : ℝ) : ℂ))
  have heq : (1 : ComplexEnd (NeumannH1 Ω)) + C = h1HelmholtzForm Ω E₀ := by
    simpa only [C, h1HelmholtzForm, h1MassOperator, sub_eq_add_neg] using
      congrArg (fun T : ComplexEnd (NeumannH1 Ω) => 1 + T)
        (_root_.neg_smul ((E₀ + 1 : ℝ) : ℂ) (h1MassOperator Ω))
  have hf := finiteDimensional_ker_one_add hC
  rw [heq] at hf
  exact hf

section
variable {Ω : PlanarSet} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)

section
include Ω E₀ hE₀

lemma h1ResonantMass_eq_inverse_smul
     (hu : u ∈ h1ResonantSpace Ω E₀) :
    h1MassOperator Ω u = (((E₀ + 1 : ℝ) : ℂ)⁻¹) • u := by
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show E₀ + 1 ≠ 0 by linarith)
  have heq : u = ((E₀ + 1 : ℝ) : ℂ) • h1MassOperator Ω u := by
    change u - ((E₀ + 1 : ℝ) : ℂ) • h1MassOperator Ω u = 0 at hu
    exact sub_eq_zero.mp hu
  calc
    _ = (((E₀ + 1 : ℝ) : ℂ)⁻¹) •
        (((E₀ + 1 : ℝ) : ℂ) • h1MassOperator Ω u) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = _ := by rw [← heq]

lemma h1MassOperator_preserves_resonantComplement
    {u : NeumannH1 Ω} (hu : u ∈ (h1ResonantSpace Ω E₀)ᗮ) :
    h1MassOperator Ω u ∈ (h1ResonantSpace Ω E₀)ᗮ := by
  intro v hv
  have hzero  :=
    ((h1ResonantSpace Ω E₀).mem_orthogonal u).1 hu v hv
  calc
    _ = ⟪h1MassOperator Ω v, u⟫_ℂ :=
      ((h1MassOperator_isSelfAdjoint Ω).isSymmetric v u).symm
    _ = ⟪(((E₀ + 1 : ℝ) : ℂ)⁻¹) • v, u⟫_ℂ :=
      congrArg (fun w : NeumannH1 Ω => ⟪w, u⟫_ℂ)
        (h1ResonantMass_eq_inverse_smul hE₀ hv)
    _ = 0 := by
      rw [Submodule.coe_inner, Submodule.coe_smul, inner_smul_left, ← Submodule.coe_inner, hzero,
        mul_zero]

end


/-- Compression of the actual mass operator to the fixed orthogonal
complement. Invariance is proved above from the actual self-adjoint form. -/
def h1ComplementMass (Ω : PlanarSet) (E₀ : ℝ) :
    (h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ :=
  (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection ∘L h1MassOperator Ω ∘L
    (h1ResonantSpace Ω E₀)ᗮ.subtypeL

include Ω E₀ hE₀ in
lemma h1ComplementMass_coe_eq
    (u : (h1ResonantSpace Ω E₀)ᗮ) :
    (h1ComplementMass Ω E₀ u : NeumannH1 Ω) = h1MassOperator Ω u := by
  have hmem := h1MassOperator_preserves_resonantComplement hE₀ u.property
  have hproj := Submodule.orthogonalProjection_mem_subspace_eq_self
    (⟨h1MassOperator Ω u, hmem⟩)
  exact congrArg Subtype.val hproj

theorem h1ComplementMass_isCompactOperator 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) E₀ :
    IsCompactOperator (h1ComplementMass Ω E₀) :=
  ((h1MassOperator_isCompactOperator hb hL).comp_clm
    (h1ResonantSpace Ω E₀)ᗮ.subtypeL).clm_comp
      (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection

/-- The genuine form operator on the fixed complement, at a varying energy. -/
def h1ComplementForm (Ω : PlanarSet) (E₀ E : ℝ) :
    (h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ :=
  1 - ((E + 1 : ℝ) : ℂ) • h1ComplementMass Ω E₀

section
include Ω E₀ hE₀

lemma h1ComplementForm_coe_eq
    (E : ℝ) (u : (h1ResonantSpace Ω E₀)ᗮ) :
    (h1ComplementForm Ω E₀ E u : NeumannH1 Ω) = h1HelmholtzForm Ω E u := by
  simp only [h1ComplementForm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul, h1ComplementMass_coe_eq hE₀]
  rfl

/-- At the reference energy the genuine complement operator is injective:
a vector in both the actual kernel and its orthogonal complement is zero. -/
theorem h1ComplementForm_injective :
    Function.Injective (h1ComplementForm Ω E₀ E₀) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hzero : h1HelmholtzForm Ω E₀ (u : NeumannH1 Ω) = 0 := by
    rw [← h1ComplementForm_coe_eq hE₀ E₀ u, hu]
    rfl
  have hker  := hzero
  have hinner := ((h1ResonantSpace Ω E₀).mem_orthogonal u).1 u.property u hker
  apply Subtype.ext
  exact inner_self_eq_zero.mp hinner

end


/-- The proved Fredholm alternative supplies invertibility on the fixed
complement at the reference energy, including at resonance. -/
theorem h1ComplementForm_isUnit {Ω : PlanarSet} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    IsUnit (h1ComplementForm Ω E₀ E₀) := @isUnit_one_sub_smul_of_compact _ _ (h1ComplementNormedSpace Ω E₀) _ (h1ComplementMass Ω E₀)
    (h1ComplementMass_isCompactOperator hb hL E₀) ((E₀ + 1 : ℝ))
    (h1ComplementForm_injective hE₀)

theorem continuous_h1ComplementForm Ω E₀ :
    Continuous (h1ComplementForm Ω E₀) := by
  unfold h1ComplementForm
  fun_prop

/-- A neighbourhood in which the complement inverse is genuine and
continuous in operator norm. The reference energy belongs to it. -/
theorem h1ComplementForm_isUnit_near {Ω : PlanarSet} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    ∃ U ∈ 𝓝 E₀, (∀ E ∈ U, IsUnit (h1ComplementForm Ω E₀ E)) ∧
      ContinuousOn (fun E => Ring.inverse (h1ComplementForm Ω E₀ E)) U := continuous_inverse_near_unit (h1ComplementForm Ω E₀)
    (continuous_h1ComplementForm Ω E₀) E₀ (h1ComplementForm_isUnit hb hL hE₀)

/-- The regular H¹ resolvent, obtained from the actual complement inverse.
It retains its correct value at the reference energy. -/
def h1RegularResolvent (Ω : PlanarSet) (E₀ E : ℝ) : ComplexEnd (NeumannH1 Ω) :=
  (h1ResonantSpace Ω E₀)ᗮ.subtypeL ∘L
    (Ring.inverse (h1ComplementForm Ω E₀ E) ∘L (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection :
      NeumannH1 Ω →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ)

section
include Ω E₀ hE₀

private lemma h1HelmholtzForm_on_resonantSpace
    E  (hu : u ∈ h1ResonantSpace Ω E₀) :
    h1HelmholtzForm Ω E u =
      (((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ)) • u := by
  change u - ((E + 1 : ℝ) : ℂ) • h1MassOperator Ω u = _
  rw [h1ResonantMass_eq_inverse_smul hE₀ hu, smul_smul]
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show E₀ + 1 ≠ 0 by linarith)
  have hscalar : 1 - ((E + 1 : ℝ) : ℂ) * ((E₀ + 1 : ℝ) : ℂ)⁻¹ =
      ((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ) := by
    field_simp
    push_cast
    ring
  calc
    _ = (1 - ((E + 1 : ℝ)) * ((E₀ + 1 : ℝ) : ℂ)⁻¹) • u := by
      rw [sub_smul, one_smul]
    _ = _ := congrArg (fun r : ℂ => r • u) hscalar

lemma h1RegularResolvent_projected_solve
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω E (h1RegularResolvent Ω E₀ E u) =
      (h1ResonantSpace Ω E₀)ᗮ.starProjection u := by
  calc
    _ = (h1ComplementForm Ω E₀ E
        (Ring.inverse (h1ComplementForm Ω E₀ E)
          ((h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection u)) : NeumannH1 Ω) :=
      (h1ComplementForm_coe_eq hE₀ E _).symm
    _ = ((h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection u) := by
      apply congrArg (fun w : (h1ResonantSpace Ω E₀)ᗮ => (w : NeumannH1 Ω))
      simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
        congrArg (fun A : (h1ResonantSpace Ω E₀)ᗮ →L[ℂ]
            (h1ResonantSpace Ω E₀)ᗮ =>
          A ((h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection u))
          (Ring.mul_inverse_cancel _ hunit)
    _ = _ := rfl

end


end


private lemma h1PoleCandidate_solve {Ω : PlanarSet}
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀)
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω E
      ((-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
        (h1ResonantSpace Ω E₀).starProjection u + h1RegularResolvent Ω E₀ E u) = u := by
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show E₀ + 1 ≠ 0 by linarith)
  have hd : ((E - E₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hne)
  have hscalar : (-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) *
      (((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ)) = 1 := by
    field_simp
    push_cast
    ring
  calc
    _ = (-(((E₀ + 1 : ℝ)) / ((E - E₀ : ℝ) : ℂ))) •
        (h1HelmholtzForm Ω E ((h1ResonantSpace Ω E₀).starProjection u)) +
        h1HelmholtzForm Ω E (h1RegularResolvent Ω E₀ E u) := by
      rw [map_add, map_smul]
    _ = (-(((E₀ + 1 : ℝ)) / ((E - E₀ : ℝ) : ℂ))) •
        ((((E₀ - E : ℝ)) / ((E₀ + 1 : ℝ) : ℂ)) •
          (h1ResonantSpace Ω E₀).starProjection u) +
        (h1ResonantSpace Ω E₀)ᗮ.starProjection u :=
      congrArg₂ (fun x y : NeumannH1 Ω => x + y)
        (congrArg ((((-(((E₀ + 1 : ℝ)) / ((E - E₀ : ℝ) : ℂ))) • id)))
          (h1HelmholtzForm_on_resonantSpace hE₀ E
            ((h1ResonantSpace Ω E₀).starProjection_apply_mem u)))
        (h1RegularResolvent_projected_solve hE₀ hunit u)
    _ = (h1ResonantSpace Ω E₀).starProjection u +
        (h1ResonantSpace Ω E₀)ᗮ.starProjection u := by
      apply congrArg (fun x : NeumannH1 Ω => x +
        (h1ResonantSpace Ω E₀)ᗮ.starProjection u)
      exact (smul_smul
        (-(((E₀ + 1 : ℝ)) / ((E - E₀ : ℝ) : ℂ)))
        (((E₀ - E : ℝ)) / ((E₀ + 1 : ℝ)))
        ((h1ResonantSpace Ω E₀).starProjection u)).trans
          ((congrArg (fun c : ℂ => c • (h1ResonantSpace Ω E₀).starProjection u)
            hscalar).trans (one_smul ℂ ((h1ResonantSpace Ω E₀).starProjection u)))
    _ = u := (h1ResonantSpace Ω E₀).starProjection_add_starProjection_orthogonal u

section
variable {Ω : PlanarSet} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀) (hunit : IsUnit (h1ComplementForm Ω E₀ E))
include Ω hb hL E₀ E hE₀ hne hunit

/-- The explicit pole candidate is a right inverse away from the reference
energy. Fredholm therefore makes the full actual operator a unit, without
assuming nonresonance or solvability at the varying energy. -/
theorem h1HelmholtzForm_isUnit_off_reference :
    IsUnit (h1HelmholtzForm Ω E) := by
  have hsurj : Function.Surjective (h1HelmholtzForm Ω E) := fun u =>
    ⟨(-(((E₀ + 1 : ℝ)) / ((E - E₀ : ℝ) : ℂ))) •
      (h1ResonantSpace Ω E₀).starProjection u + h1RegularResolvent Ω E₀ E u,
      h1PoleCandidate_solve hE₀ hne hunit u⟩
  let C  := -((E + 1 : ℝ) : ℂ) • h1MassOperator Ω
  have hC : IsCompactOperator C := by
    exact
      (h1MassOperator_isCompactOperator hb hL).smul (-((E + 1 : ℝ) : ℂ))
  have heq : (1 : ComplexEnd (NeumannH1 Ω)) + C = h1HelmholtzForm Ω E := by
    simpa only [C, h1HelmholtzForm, h1MassOperator, sub_eq_add_neg] using
      congrArg (fun T : ComplexEnd (NeumannH1 Ω) => 1 + T)
        (_root_.neg_smul ((E + 1 : ℝ) : ℂ) (h1MassOperator Ω))
  have hinj : Function.Injective (h1HelmholtzForm Ω E) := by
    rw [← heq]
    apply injective_of_surjective_one_add hC
    rwa [heq]
  exact isUnit_of_bijective _ ⟨hinj, hsurj⟩

/-- The exact pole formula for the genuine H¹ inverse. The complement is
invertible near the reference energy by the theorem above; invertibility
of the full operator away from the reference point is proved explicitly. -/
theorem h1HelmholtzResolvent_eq_pole_add_regular :
    h1HelmholtzResolvent Ω E =
      (-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
        (h1ResonantSpace Ω E₀).starProjection + h1RegularResolvent Ω E₀ E := by
  have hu := h1HelmholtzForm_isUnit_off_reference hb hL hE₀ hne hunit
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

end


end PolyaNeumann

end
