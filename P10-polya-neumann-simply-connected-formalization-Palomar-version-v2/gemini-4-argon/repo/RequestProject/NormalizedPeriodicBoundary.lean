module

public import RequestProject.PeriodicRegularContinuity
public import RequestProject.PeriodicRegularSelfAdjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannResonanceDimension
public import RequestProject.NeumannConstantTrace
public import RequestProject.NeumannRegularSolutionAtReference

/-! The genuine normalized periodic boundary family and its Neumann pole.
The decomposition includes a nonresonant reference energy itself. -/

@[expose] public section
noncomputable section
namespace PolyaNeumann
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate

variable {Ω : Set ℂ}

private theorem periodic_projected_trace_gram
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (S : Submodule ℂ H) [CompleteSpace S] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) (Q : H →L[ℂ] G) (c : ℝ) (hc : 0 ≤ c) :
    (c : ℂ) • (Q ∘L S.starProjection ∘L adjoint Q) =
      ∑ i, InnerProductSpace.rankOne ℂ ((Real.sqrt c : ℂ) • Q (b i))
        ((Real.sqrt c : ℂ) • Q (b i)) := by
  classical
  rw [show Q ∘L S.starProjection ∘L adjoint Q = (Q.comp S.subtypeL).comp (adjoint (Q.comp S.subtypeL)) by
    simp only [adjoint_comp, Submodule.adjoint_subtypeL,
      Submodule.starProjection, comp_assoc]]
  apply ContinuousLinearMap.ext
  intro g
  change (c : ℂ) • Q (adjoint (Q.comp S.subtypeL) g : S) = _
  simp_rw [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]
  rw [← b.sum_repr' (adjoint (Q.comp S.subtypeL) g)]
  simp [adjoint_inner_right, Submodule.subtypeL_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun a : ℂ => a • Q (b i))
  calc
    _ =
        (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) * ⟪Q (b i), g⟫_ℂ := by rw [show (Real.sqrt c : ℂ) * Real.sqrt c = c by
          exact_mod_cast Real.mul_self_sqrt hc]
    _ = ((Real.sqrt c) * ⟪Q (b i), g⟫_ℂ) * Real.sqrt c := by ring

theorem normalizedNeumannResidue_eq_sum_rankOne 
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E₀)) :
    normalizedNeumannResidue Q E₀ = ∑ i,
      InnerProductSpace.rankOne ℂ ((Real.sqrt (E₀ + 1) : ℂ) • Q (b i))
        ((Real.sqrt (E₀ + 1) : ℂ) • Q (b i)) := by
  exact periodic_projected_trace_gram (h1ResonantSpace Ω E₀) b Q (E₀ + 1)
    (by linarith)

theorem h1Resonant_starProjection_eq_zero_of_form_isUnit  
    (hunit : IsUnit (h1HelmholtzForm Ω E₀)) u :
    (h1ResonantSpace Ω E₀).starProjection u = 0 := by
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).injective
  rw [map_zero]
  exact ((h1ResonantSpace Ω E₀).orthogonalProjection u).property

theorem normalizedNeumannBoundary_eq_regular_at_nonresonant_reference 
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1HelmholtzForm Ω E₀)) :
    normalizedNeumannBoundary Q E₀ = normalizedNeumannRegular Q E₀ E₀ := by
  apply ContinuousLinearMap.ext
  intro b
  have h := normalizedNeumannRegular_eq_trace_of_solution_at_reference Q hb hL hE₀
    b (normalizedNeumannPoisson Q E₀ b) (normalizedNeumannPoisson_isSolution Q hunit b)
  rw [h1Resonant_starProjection_eq_zero_of_form_isUnit hunit, map_zero, sub_zero] at h
  exact h.symm

def normalizedPeriodicBoundaryFamily 
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (E : ℝ) : L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannBoundary Q E - normalizedInverseAbsOperator) +
    principalNormalized + correctedRemainderOperator (Ws E) 0 0

theorem normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference
     (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) Ws
     (hE₀ : 0 ≤ E₀) (hunit : IsUnit (h1HelmholtzForm Ω E₀)) :
    normalizedPeriodicBoundaryFamily Q Ws E₀ = normalizedPeriodicRegularFamily Q E₀ Ws E₀ := by
  simp [normalizedPeriodicBoundaryFamily, normalizedPeriodicRegularFamily, normalizedNeumannBoundary_eq_regular_at_nonresonant_reference Q hb hL hE₀ hunit]

theorem normalizedPeriodicBoundaryFamily_isSelfAdjoint 
    (Q : NeumannH1 Ω →L[ℂ] L2Z)  
    Ws 
    (hK : LipschitzWith K γ) (hW : IsTransport γ E (Ws E))
    (hbase : Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2) :
    IsSelfAdjoint (normalizedPeriodicBoundaryFamily Q Ws E) := by
  rw [normalizedPeriodicBoundaryFamily, correctedRemainderOperator_eq _ _ _ hbase]
  have hm := hsMatrixOp_isSelfAdjoint _ hbase (correctedRemainderMatrix_zero_hermitian hK hW)
  have h1 := normalizedNeumannBoundary_isSelfAdjoint Q E
  have h2 := @normalizedInverseAbsOperator_isSelfAdjoint
  have h3 := @principalNormalized_isSelfAdjoint
  simp only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hm h1 h2 h3 ⊢
  rw [map_add, map_add, map_smulₛₗ, map_sub, h1, h2, h3, hm, map_ofNat]

theorem normalizedPeriodicBoundaryFamily_eq_pole_add_regular 
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) Ws
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hfull : IsUnit (h1HelmholtzForm Ω E))
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    normalizedPeriodicBoundaryFamily Q Ws E =
      ((-2 / (E - E₀) : ℝ) : ℂ) • normalizedNeumannResidue Q E₀ +
        normalizedPeriodicRegularFamily Q E₀ Ws E := by
  rw [normalizedPeriodicBoundaryFamily,
    show normalizedNeumannBoundary Q E = (-((E - E₀ : ℝ) : ℂ)⁻¹) • normalizedNeumannResidue Q E₀ + normalizedNeumannRegular Q E₀ E by
      by_cases hne : E ≠ E₀
      · exact normalizedNeumannBoundary_eq_pole_add_regular Q hb hL hE₀ hne hunit
      · have heq := not_ne_iff.mp hne
        subst E
        simp
        rw [normalizedNeumannBoundary_eq_regular_at_nonresonant_reference Q hb hL hE₀ hfull]
        ext x
        simp]
  simp only [normalizedPeriodicRegularFamily, smul_sub, smul_add, smul_smul, show 2 * (-((E - E₀ : ℝ) : ℂ)⁻¹) = ((-2 / (E - E₀) : ℝ) : ℂ) by
    push_cast
    ring]
  abel

end PolyaNeumann
end
