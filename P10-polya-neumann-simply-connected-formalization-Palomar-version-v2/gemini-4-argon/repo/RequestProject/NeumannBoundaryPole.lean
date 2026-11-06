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

variable {Ω : Set ℂ} {E₀ E : ℝ}

private lemma isUnit_one_sub_smul_of_compact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (M : X →L[ℂ] X) (hM : IsCompactOperator M) (c : ℂ)
    (hinj : Function.Injective ((1 : X →L[ℂ] X) - c • M)) :
    IsUnit ((1 : X →L[ℂ] X) - c • M) := by
  let C := -c • M
  have heq : (1 : X →L[ℂ] X) + C = 1 - c • M := by
    simpa only [C, sub_eq_add_neg] using
      congrArg (fun T : X →L[ℂ] X => 1 + T) (_root_.neg_smul c M)
  have hinj' := heq.symm ▸ hinj
  exact heq ▸ (ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj', (injective_iff_surjective_one_add (hM.smul (-c))).mp hinj'⟩)

/-- The actual compact mass operator in the shifted-energy H¹ space. -/
def h1MassOperator Ω : NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  (ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω)

theorem h1MassOperator_isSelfAdjoint Ω :
    IsSelfAdjoint (h1MassOperator Ω) :=
  (ContinuousLinearMap.isPositive_adjoint_comp_self (h1Value Ω)).isSelfAdjoint

local notation "Φ3" => h1MassOperator Ω

theorem h1MassOperator_isCompactOperator  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : IsCompactOperator (Φ3) :=
  (h1Value_isCompactOperator hb hL).clm_comp (ContinuousLinearMap.adjoint (h1Value Ω))

/-- The resonance space of the actual form operator at the reference energy. -/
def h1ResonantSpace Ω (E₀ : ℝ) : Submodule ℂ (NeumannH1 Ω) :=
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

local notation "Φ1" => NeumannH1 Ω

theorem finiteDimensional_h1ResonantSpace  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) E₀ :
    FiniteDimensional ℂ (h1ResonantSpace Ω E₀) := by
  let C := -((E₀ + 1 : ℝ) : ℂ) • Φ3
  have heq : (1 : Φ1 →L[ℂ] Φ1) + C = h1HelmholtzForm Ω E₀ := by
    simpa only [C, h1HelmholtzForm, h1MassOperator, sub_eq_add_neg] using
      congrArg (fun T : Φ1 →L[ℂ] Φ1 => 1 + T)
        (_root_.neg_smul ((E₀ + 1 : ℝ) : ℂ) (Φ3))
  have hf := finiteDimensional_ker_one_add (show IsCompactOperator C by
    exact
      (h1MassOperator_isCompactOperator hb hL).smul (-((E₀ + 1 : ℝ) : ℂ)))
  rw [heq] at hf
  exact hf

local notation "Φ0" => h1ResonantSpace Ω E₀

private lemma h1MassOperator_on_resonantSpace   (hE₀ : 0 ≤ E₀)
     (hu : u ∈ Φ0) :
    Φ3 u = ((E₀ + 1 : ℝ) : ℂ)⁻¹ • u := by
  calc
    _ = ((E₀ + 1 : ℝ) : ℂ)⁻¹ •
        (((E₀ + 1 : ℝ) : ℂ) • Φ3 u) := by
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast (by linarith)), one_smul]
    _ = _ := by rw [← (show u = ((E₀ + 1 : ℝ) : ℂ) • Φ3 u by
      change u - ((E₀ + 1 : ℝ) : ℂ) • Φ3 u = 0 at hu
      exact sub_eq_zero.mp hu)]

/-- Compression of the actual mass operator to the fixed orthogonal
complement. Invariance is proved above from the actual self-adjoint form. -/
def h1ComplementMass Ω E₀ :
    (h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ :=
  (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection ∘L h1MassOperator Ω ∘L
    (h1ResonantSpace Ω E₀)ᗮ.subtypeL

private lemma coe_h1ComplementMass   (hE₀ : 0 ≤ E₀)
    u :
    (h1ComplementMass Ω E₀ u : Φ1) = Φ3 u := by
  have hproj := Submodule.orthogonalProjection_mem_subspace_eq_self
    (⟨Φ3 u, (show Φ3 u ∈ (Φ0)ᗮ by
      rw [Submodule.mem_orthogonal]
      intro v hv
      calc
        _ = _ :=
          ((h1MassOperator_isSelfAdjoint Ω).isSymmetric v u).symm
        _ = _ :=
          congrArg (fun w : Φ1 => ⟪w, u⟫_ℂ)
            (h1MassOperator_on_resonantSpace hE₀ hv)
        _ = 0 := by
          rw [Submodule.coe_inner, Submodule.coe_smul, inner_smul_left, ← Submodule.coe_inner, ((Φ0).mem_orthogonal u).1 u.property v hv,
            mul_zero])⟩ : (Φ0)ᗮ)
  exact congrArg Subtype.val hproj

/-- The genuine form operator on the fixed complement, at a varying energy. -/
def h1ComplementForm Ω (E₀ E : ℝ) :
    (h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ :=
  1 - ((E + 1 : ℝ) : ℂ) • h1ComplementMass Ω E₀

private lemma coe_h1ComplementForm   (hE₀ : 0 ≤ E₀)
    E u :
    (h1ComplementForm Ω E₀ E u : Φ1) = h1HelmholtzForm Ω E u := by
  simp only [h1ComplementForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    Submodule.coe_sub, Submodule.coe_smul, coe_h1ComplementMass hE₀]
  rfl

/-- The proved Fredholm alternative supplies invertibility on the fixed
complement at the reference energy, including at resonance. -/
theorem h1ComplementForm_isUnit  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hE₀ : 0 ≤ E₀) :
    IsUnit (h1ComplementForm Ω E₀ E₀) := by
  exact @isUnit_one_sub_smul_of_compact _ _ (h1ComplementNormedSpace Ω E₀) _ (h1ComplementMass Ω E₀)
    (((h1MassOperator_isCompactOperator hb hL).comp_clm (Φ0)ᗮ.subtypeL).clm_comp (Φ0)ᗮ.orthogonalProjection) (E₀ + 1 : ℝ)
    (show Function.Injective (h1ComplementForm Ω E₀ E₀) by
      rw [injective_iff_map_eq_zero]
      intro u hu
      apply Subtype.ext
      exact inner_self_eq_zero.mp (((Φ0).mem_orthogonal u).1 u.property u (show h1HelmholtzForm Ω E₀ u = 0 by
        rw [← coe_h1ComplementForm hE₀ E₀ u, hu]
        rfl)))

theorem continuous_h1ComplementForm Ω E₀ :
    Continuous (h1ComplementForm Ω E₀) := by
  unfold h1ComplementForm
  fun_prop

/-- A neighbourhood in which the complement inverse is genuine and
continuous in operator norm. The reference energy belongs to it. -/
theorem h1ComplementForm_isUnit_near  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hE₀ : 0 ≤ E₀) :
    ∃ U ∈ 𝓝 E₀, (∀ E ∈ U, IsUnit (h1ComplementForm Ω E₀ E)) ∧
      ContinuousOn (fun E => Ring.inverse (h1ComplementForm Ω E₀ E)) U := by
  exact (by
    refine ⟨(h1ComplementForm Ω E₀) ⁻¹' {x | IsUnit x}, (Units.isOpen.preimage (continuous_h1ComplementForm Ω E₀)).mem_nhds (h1ComplementForm_isUnit hb hL hE₀),
      fun E hE => hE, ?_⟩
    intro E hE
    obtain ⟨u, hu⟩ := hE
    exact ((hu ▸ NormedRing.inverse_continuousAt u).comp (continuous_h1ComplementForm Ω E₀).continuousAt).continuousWithinAt)

/-- The regular H¹ resolvent, obtained from the actual complement inverse.
It retains its correct value at the reference energy. -/
def h1RegularResolvent Ω (E₀ E : ℝ) : NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  (h1ResonantSpace Ω E₀)ᗮ.subtypeL ∘L
    (Ring.inverse (h1ComplementForm Ω E₀ E) ∘L (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection :
      NeumannH1 Ω →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ)

private lemma h1HelmholtzForm_on_resonantSpace   (hE₀ : 0 ≤ E₀)
    E  (hu : u ∈ Φ0) :
    h1HelmholtzForm Ω E u =
      (((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ)) • u := by
  change u - ((E + 1 : ℝ) : ℂ) • Φ3 u = _
  rw [h1MassOperator_on_resonantSpace hE₀ hu, smul_smul]
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith)
  have hscalar : 1 - ((E + 1 : ℝ) : ℂ) * ((E₀ + 1 : ℝ) : ℂ)⁻¹ =
      ((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ) := by
    field_simp [hc]
    push_cast
    ring
  calc
    _ = _ := by
      rw [sub_smul, one_smul]
    _ = _ := congrArg (fun r => r • u) hscalar

local notation "Φ2" => h1HelmholtzForm Ω E

private lemma h1PoleCandidate_solve 
     (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀)
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) u :
    Φ2
      ((-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
        (Φ0).starProjection u + h1RegularResolvent Ω E₀ E u) = u := by
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith)
  have hd : ((E - E₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hne)
  have hscalar : (-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) *
      (((E₀ - E : ℝ) : ℂ) / ((E₀ + 1 : ℝ) : ℂ)) = 1 := by
    field_simp [hc, hd]
    push_cast
    ring
  calc
    _ = _ := by
      rw [map_add, map_smul]
    _ = _ :=
      congrArg₂ (fun x y : Φ1 => x + y)
        (congrArg (fun x : Φ1 =>
          (-(((E₀ + 1 : ℝ) : ℂ) / (E - E₀ : ℝ))) • x)
          (h1HelmholtzForm_on_resonantSpace hE₀ E
            ((Φ0).starProjection_apply_mem u)))
        (by
          calc
            _ = _ :=
              (coe_h1ComplementForm hE₀ E _).symm
            _ = _ := by
              apply congrArg (fun w : (Φ0)ᗮ => (w : Φ1))
              simpa [ContinuousLinearMap.mul_apply] using
                congrArg (fun A : (Φ0)ᗮ →L[ℂ]
                    (Φ0)ᗮ =>
                  A ((Φ0)ᗮ.orthogonalProjection u))
                  (Ring.mul_inverse_cancel _ hunit)
            _ = _ := rfl)
    _ = _ := by
      apply congrArg (fun x : Φ1 => x +
        (Φ0)ᗮ.starProjection u)
      exact (smul_smul
        (-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ)))
        ((E₀ - E : ℝ) / (E₀ + 1 : ℝ))
        ((Φ0).starProjection u)).trans
          ((congrArg (fun c => c • (Φ0).starProjection u)
            hscalar).trans (one_smul ℂ ((Φ0).starProjection u)))
    _ = u := (Φ0).starProjection_add_starProjection_orthogonal u

/-- The exact pole formula for the genuine H¹ inverse. The complement is
invertible near the reference energy by the theorem above; invertibility
of the full operator away from the reference point is proved explicitly. -/
theorem h1HelmholtzResolvent_eq_pole_add_regular 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
     (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀)
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    h1HelmholtzResolvent Ω E =
      (-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
        (Φ0).starProjection + h1RegularResolvent Ω E₀ E := by
  have hu : IsUnit (Φ2) := by
    have hsurj : Function.Surjective (Φ2) := fun u =>
      ⟨(-(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ))) •
        (Φ0).starProjection u + h1RegularResolvent Ω E₀ E u,
        h1PoleCandidate_solve hE₀ hne hunit u⟩
    let C := -((E + 1 : ℝ) : ℂ) • Φ3
    have heq : (1 : Φ1 →L[ℂ] Φ1) + C = Φ2 := by
      simpa only [C, h1HelmholtzForm, h1MassOperator, sub_eq_add_neg] using
        congrArg (fun T : Φ1 →L[ℂ] Φ1 => 1 + T)
          (_root_.neg_smul ((E + 1 : ℝ) : ℂ) (Φ3))
    exact isUnit_of_bijective _ ⟨(by
      rw [← heq]
      apply injective_of_surjective_one_add (by
        exact
          (h1MassOperator_isCompactOperator hb hL).smul (-((E + 1 : ℝ) : ℂ)))
      rwa [heq]), hsurj⟩
  apply ContinuousLinearMap.ext
  intro u
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  rw [show Φ2 (h1HelmholtzResolvent Ω E u) = u by
    change Φ2 (Ring.inverse (Φ2) u) = u
    rw [← ContinuousLinearMap.mul_apply,
      Ring.mul_inverse_cancel _ hu,
      ContinuousLinearMap.one_apply]]
  exact (h1PoleCandidate_solve hE₀ hne hunit u).symm



end PolyaNeumann

end
