module

public import RequestProject.NeumannProjectedWeak
public import RequestProject.NeumannNormalizedBoundary

/-!
# The actual regular solution at a resonant reference energy

The regular resolvent applied to the genuine form of a vector is exactly
its orthogonal component outside the genuine Neumann resonance space.
Consequently the regular normalized boundary solution for any actual
weak solution has its trace with precisely that resonant component
removed. No spectral nonresonance is assumed at the reference energy.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open scoped InnerProductSpace

private theorem regular_inverse_apply_form
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (B : Sᗮ →L[ℂ] Sᗮ)
    (hzero : ∀ s ∈ S, A s = 0)
    (hcoe : ∀ v : Sᗮ, B v = A (v : H))
    (hunit : IsUnit B) u :
    ((Ring.inverse B) (Sᗮ.orthogonalProjection (A u)) : H) =
      (Sᗮ.orthogonalProjection u : H) := by
  let v := Sᗮ.orthogonalProjection u
  rw [show Sᗮ.orthogonalProjection (A u) = B v by
    rw [show A u = A v by
      have h := congrArg A (S.starProjection_add_starProjection_orthogonal u)
      simp only [map_add, Submodule.starProjection_apply] at h
      rw [hzero _ (S.orthogonalProjection u).property, zero_add] at h
      exact h.symm, ← hcoe v]
    exact Sᗮ.orthogonalProjection_mem_subspace_eq_self (B v)]
  exact congrArg (fun w : Sᗮ => (w : H)) (by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : Sᗮ →L[ℂ] Sᗮ => T v) (Ring.inverse_mul_cancel B hunit))

/-- The original regular resolvent removes the original Neumann
resonance component at the reference energy itself. -/
theorem h1RegularResolvent_form_at_reference {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
     (hE₀ : 0 ≤ E₀) (u : NeumannH1 Ω) :
    h1RegularResolvent Ω E₀ E₀ (h1HelmholtzForm Ω E₀ u) =
      (h1ResonantSpace Ω E₀)ᗮ.starProjection u := by
  exact regular_inverse_apply_form (H := NeumannH1 Ω) (h1ResonantSpace Ω E₀)
    (h1HelmholtzForm Ω E₀) (h1ComplementForm Ω E₀ E₀)
    (fun _ hs => hs) (h1ComplementForm_coe_eq hE₀ E₀)
    (h1ComplementForm_isUnit hb hL hE₀) u

/-- At resonance a genuine weak Neumann solution identifies the regular
solution, including exactly the removed physical resonance component. -/
theorem normalizedNeumannRegular_eq_trace_of_solution_at_reference 
    Q
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
     (hE₀ : 0 ≤ E₀) b u
    (hu : IsNormalizedNeumannSolution Q E₀ b u) :
    normalizedNeumannRegular Q E₀ E₀ b =
      Q u - Q ((h1ResonantSpace Ω E₀).starProjection u) := by
  change Q (h1RegularResolvent Ω E₀ E₀ (ContinuousLinearMap.adjoint Q b)) = _
  rw [← (isNormalizedNeumannSolution_iff Q E₀ b u).mp hu, h1RegularResolvent_form_at_reference hb hL hE₀ u]
  have hdecomp := congrArg Q
    ((h1ResonantSpace Ω E₀).starProjection_add_starProjection_orthogonal u)
  rw [map_add] at hdecomp
  exact eq_sub_of_add_eq' hdecomp

end PolyaNeumann

end
