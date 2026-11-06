module

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

@[expose] public section


noncomputable section

namespace PolyaNeumann

open Set
open scoped Real InnerProductSpace ComplexConjugate

/- These computations are checked before specialization to the concrete
H¹ space. The public conclusions below retain the actual operators. -/
variable {Ω : Set ℂ}

private theorem projected_mass_from_kernel
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    M (c : ℂ) (hc : c ≠ 0) u
    (hu : ((1 : H →L[ℂ] H) - c • M) u = 0) : M u = c⁻¹ • u := by
  have heq : u = c • M u := sub_eq_zero.mp (by
    simpa using hu)
  calc
    _ = _ := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = _ := congrArg (fun v => c⁻¹ • v) heq.symm

private theorem projected_mass_preserves_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) (M : H →L[ℂ] H) (hM : IsSelfAdjoint M) (c : ℂ)
    (hS : ∀ v ∈ S, M v = c • v) {u : H} (hu : u ∈ Sᗮ) : M u ∈ Sᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  calc
    _ = _ := (hM.isSymmetric v u).symm
    _ = _ := congrArg (fun w => ⟪w, u⟫_ℂ) (hS v hv)
    _ = 0 := by simp only [inner_smul_left, (S.mem_orthogonal u).1 hu v hv, mul_zero]

private theorem projected_compression_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] M
    (hS : ∀ v ∈ S, M v ∈ S) u :
    ((S.orthogonalProjection ∘L M ∘L S.subtypeL) u : H) = M u := by
  simpa [Submodule.subtypeL_apply] using
    congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self (K := S) ⟨M u, hS u u.property⟩)

private theorem projected_form_coe
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Submodule ℂ H) M C
    (hC : ∀ u : S, (C u : H) = M u) (c : ℂ) u :
    (((1 : S →L[ℂ] S) - c • C) u : H) =
      ((1 : H →L[ℂ] H) - c • M) u := by
  simp [hC]

private theorem projected_inverse_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsUnit A) x : A (Ring.inverse A x) = x := by
  simpa [ContinuousLinearMap.mul_apply] using
    congrArg (fun B : H →L[ℂ] H => B x) (Ring.mul_inverse_cancel A hA)

private theorem projected_regular_solve
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H) (B : S →L[ℂ] S)
    (hAB : ∀ u : S, A u = (B u : H)) (hB : IsUnit B) x :
    A ((S.subtypeL ∘L Ring.inverse B ∘L S.orthogonalProjection) x) =
      S.starProjection x := by
  calc
    _ = _ := by
      simpa [Submodule.subtypeL_apply] using
        hAB (Ring.inverse B (S.orthogonalProjection x))
    _ = _ :=
      congrArg (fun v : S => (v : H))
        (projected_inverse_apply B hB (S.orthogonalProjection x))
    _ = _ := rfl

private theorem projected_form_pairing_of_solve
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H)
    (W M : H → H → ℂ) c
    (hA : ∀ v u, ⟪v, A u⟫_ℂ = W v u)
    (hM : ∀ w ∈ S, ∀ v, ⟪v, w⟫_ℂ = c * M v w)
    {u x} (hsolve : A u = Sᗮ.starProjection x) (v : H) :
    W v u = ⟪v, x⟫_ℂ - c * M v (S.starProjection x) := by
  calc
    _ = _ := (hA v u).symm
    _ = _ := congrArg (fun w => ⟪v, w⟫_ℂ) hsolve
    _ = _ := by
      rw [Submodule.starProjection_orthogonal_val, inner_sub_right]
    _ = _ := congrArg (fun z => ⟪v, x⟫_ℂ - z)
      (hM _ (S.starProjection_apply_mem x) v)

/-- The genuine mass operator acts by the shifted inverse eigenvalue on
the actual kernel of the Helmholtz form. -/
theorem h1ResonantMass_eq_inverse_smul  {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
     (hu : u ∈ h1ResonantSpace Ω E₀) :
    h1MassOperator Ω u = ((E₀ + 1 : ℝ) : ℂ)⁻¹ • u := by
  exact projected_mass_from_kernel (h1MassOperator Ω) (E₀ + 1 : ℝ) (by
    exact_mod_cast (by linarith)) u hu

/-- Self-adjointness and the actual resonant mass identity show that the
fixed orthogonal complement is invariant under the mass operator. -/
theorem h1MassOperator_preserves_resonantComplement  
    (hE₀ : 0 ≤ E₀) {u : NeumannH1 Ω} (hu : u ∈ (h1ResonantSpace Ω E₀)ᗮ) :
    h1MassOperator Ω u ∈ (h1ResonantSpace Ω E₀)ᗮ := by
  exact projected_mass_preserves_orthogonal (h1ResonantSpace Ω E₀)
    (h1MassOperator Ω) (h1MassOperator_isSelfAdjoint Ω)
    ((E₀ + 1 : ℝ)⁻¹)
    (fun _ hv => h1ResonantMass_eq_inverse_smul hE₀ hv) hu

/-- The compressed mass operator is the actual mass operator on its
invariant complement, including after embedding into the full H¹ space. -/
theorem h1ComplementForm_coe_eq   (hE₀ : 0 ≤ E₀)
    (E : ℝ) (u : (h1ResonantSpace Ω E₀)ᗮ) :
    (h1ComplementForm Ω E₀ E u : NeumannH1 Ω) = h1HelmholtzForm Ω E u := by
  have h_inl u : (h1ComplementMass Ω E₀ u : NeumannH1 Ω) = h1MassOperator Ω u := by
    exact projected_compression_apply (h1ResonantSpace Ω E₀)ᗮ (h1MassOperator Ω)
      (fun _ hv => h1MassOperator_preserves_resonantComplement hE₀ hv) u
  exact projected_form_coe (h1ResonantSpace Ω E₀)ᗮ (h1MassOperator Ω)
    (h1ComplementMass Ω E₀) h_inl
    (E + 1 : ℝ) u

/-- The shifted H¹ pairing of an actual resonant vector is its physical
mass pairing multiplied by `E₀ + 1`. -/
theorem h1Resonant_inner_eq_mass  
    {w : NeumannH1 Ω} (hw : w ∈ h1ResonantSpace Ω E₀) v :
    ⟪v, w⟫_ℂ = ((E₀ + 1 : ℝ) : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := by
  exact (h1_inner Ω v w).trans
    (by
      rw [show (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) = (E₀ : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ by
        have hzero : h1HelmholtzForm Ω E₀ w = 0 := hw
        have h := h1HelmholtzForm_inner Ω E₀ v w
        rw [hzero, inner_zero_right] at h
        exact sub_eq_zero.mp h.symm]
      push_cast
      ring)

/-- The actual regular solution with normalized boundary load `Q† b`
satisfies the projected weak Neumann equation against every H¹ vector. -/
theorem h1RegularResolvent_adjoint_weak_pairing {Ω}
    (Q : NeumannH1 Ω →L[ℂ] L2Z)  (hE₀ : 0 ≤ E₀)
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
  exact ((show ∀ v : NeumannH1 Ω, (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ) - (E : ℂ) * ⟪h1Value Ω v, h1Value Ω (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ = ⟪v, (ContinuousLinearMap.adjoint Q b)⟫_ℂ - (E₀ + 1 : ℝ) * ⟪h1Value Ω v, h1Value Ω ((h1ResonantSpace Ω E₀).starProjection (ContinuousLinearMap.adjoint Q b))⟫_ℂ by
    intro v
    exact projected_form_pairing_of_solve (h1ResonantSpace Ω E₀)
      (h1HelmholtzForm Ω E)
      (fun v u => (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
        E * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ)
      (fun v u => ⟪h1Value Ω v, h1Value Ω u⟫_ℂ) (E₀ + 1 : ℝ)
      (h1HelmholtzForm_inner Ω E) (fun _ hw v => h1Resonant_inner_eq_mass hw v)
      (by
        exact projected_regular_solve (h1ResonantSpace Ω E₀)ᗮ (h1HelmholtzForm Ω E)
          (h1ComplementForm Ω E₀ E) (fun v => (h1ComplementForm_coe_eq hE₀ E v).symm)
          hunit (ContinuousLinearMap.adjoint Q b)) v) v).trans (congrArg (fun t => t - _) (ContinuousLinearMap.adjoint_inner_right Q v b))

end PolyaNeumann

end
