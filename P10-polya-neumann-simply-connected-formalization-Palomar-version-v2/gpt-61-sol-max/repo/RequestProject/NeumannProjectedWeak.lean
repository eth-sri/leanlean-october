module

public import RequestProject.NeumannBoundaryPole


public import RequestProject.PlanarTypes

public import RequestProject.NeumannNormalizedBoundary

/-!
# The actual weak equation for the projected Neumann resolvent

The fixed complement is invariant under the genuine mass and Helmholtz
operators. Consequently the regular resolvent solves the actual form
equation with exactly the resonant component of the load removed. The
removed component has its genuine physical mass pairing, with the factor
`E₀ + 1` from the shifted-energy H¹ inner product.

These identities use the actual variational resonance space and do not
assume any boundary principal-part or smoothing formula.
-/

public section



namespace PolyaNeumann

open Set
open scoped InnerProductSpace

/- These computations are checked before specialization to the concrete
H¹ space. The public conclusions below retain the actual operators. -/


private theorem projected_shifted_mass_scalar
    a b (E : ℝ) (h : a = (E : ℂ) * b) :
    b + a = ((E + 1 : ℝ) : ℂ) * b := by
  rw [h]
  push_cast
  ring

private theorem projected_form_pairing_of_solve
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H)
    (W M : H → H → ℂ) c
    (hA : ∀ v u, ⟪v, A u⟫_ℂ = W v u)
    (hM : ∀ w ∈ S, ∀ v, ⟪v, w⟫_ℂ = c * M v w)
    {u x } (hsolve : A u = Sᗮ.starProjection x) v :
    W v u = ⟪v, x⟫_ℂ - c * M v (S.starProjection x) := by
  calc
    W v u = ⟪v, A u⟫_ℂ := (hA v u).symm
    _ = ⟪v, Sᗮ.starProjection x⟫_ℂ := congrArg (fun w : H => ⟪v, w⟫_ℂ) hsolve
    _ = ⟪v, x⟫_ℂ - ⟪v, S.starProjection x⟫_ℂ := by
      rw [Submodule.starProjection_orthogonal_val, inner_sub_right]
    _ = _ := congrArg (fun z : ℂ => ⟪v, x⟫_ℂ - z)
      (hM _ (S.starProjection_apply_mem x) v)

private theorem projected_adjoint_pairing_sub
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (Q : H →L[ℂ] G) (v : H) (b : G) (z : ℂ) :
    ⟪v, ContinuousLinearMap.adjoint Q b⟫_ℂ - z = ⟪Q v, b⟫_ℂ - z :=
  congrArg (fun t : ℂ => t - z) (ContinuousLinearMap.adjoint_inner_right Q v b)



section
variable {Ω } {E₀ } {w } (hw : w ∈ h1ResonantSpace Ω E₀) (v : NeumannH1 Ω)
include Ω E₀ w hw v

/-- Actual resonant vectors satisfy the zero-load weak Neumann equation
against every genuine H¹ test vector. -/
theorem h1Resonant_weak_pairing :
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) =
      (E₀ : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := by
  have hzero : h1HelmholtzForm Ω E₀ w = 0 := hw
  have h := h1HelmholtzForm_inner Ω E₀ v w
  rw [hzero, inner_zero_right] at h
  exact sub_eq_zero.mp h.symm

/-- The shifted H¹ pairing of an actual resonant vector is its physical
mass pairing multiplied by `E₀ + 1`. -/
theorem h1Resonant_inner_eq_mass :
    ⟪v, w⟫_ℂ = ((E₀ + 1 : ℝ) : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := (h1_inner Ω v w).trans
    (projected_shifted_mass_scalar _ _ E₀ (h1Resonant_weak_pairing hw v))

end


/-- The all-test-vector weak equation for the genuine regular resolvent.
The removed resonant load contributes with a minus sign and the actual
shifted-energy factor `E₀ + 1`. -/
theorem h1RegularResolvent_weak_pairing {Ω : PlanarSet} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (x : NeumannH1 Ω) :
    ∀ v : NeumannH1 Ω,
      (∑ i, ⟪h1Gradient Ω i v,
        h1Gradient Ω i (h1RegularResolvent Ω E₀ E x)⟫_ℂ) -
          (E : ℂ) * ⟪h1Value Ω v,
            h1Value Ω (h1RegularResolvent Ω E₀ E x)⟫_ℂ =
        ⟪v, x⟫_ℂ - ((E₀ + 1 : ℝ) : ℂ) *
          ⟪h1Value Ω v, h1Value Ω ((h1ResonantSpace Ω E₀).starProjection x)⟫_ℂ := by
  intro v
  exact projected_form_pairing_of_solve (h1ResonantSpace Ω E₀)
    (h1HelmholtzForm Ω E)
    (fun v u => (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      E * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ)
    (fun v u => ⟪h1Value Ω v, h1Value Ω u⟫_ℂ) ((E₀ + 1 : ℝ))
    (h1HelmholtzForm_inner Ω E) (fun _ hw v => h1Resonant_inner_eq_mass hw v)
    (h1RegularResolvent_projected_solve hE₀ hunit x) v

/-- The actual regular solution with normalized boundary load `Q† b`
satisfies the projected weak Neumann equation against every H¹ vector. -/
theorem h1RegularResolvent_adjoint_weak_pairing {Ω : PlanarSet}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (b : L2Z) :
    ∀ v : NeumannH1 Ω,
      (∑ i, ⟪h1Gradient Ω i v,
        h1Gradient Ω i (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ) -
          (E : ℂ) * ⟪h1Value Ω v,
            h1Value Ω (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ =
        ⟪Q v, b⟫_ℂ - ((E₀ + 1 : ℝ) : ℂ) *
          ⟪h1Value Ω v, h1Value Ω ((h1ResonantSpace Ω E₀).starProjection
            (ContinuousLinearMap.adjoint Q b))⟫_ℂ := by
  intro v
  simp_all only [h1RegularResolvent_weak_pairing, projected_adjoint_pairing_sub]

end PolyaNeumann
