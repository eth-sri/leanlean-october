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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped Real InnerProductSpace ComplexConjugate

/- These computations are checked before specialization to the concrete
H¹ space. The public conclusions below retain the actual operators. -/
private theorem projected_mass_from_kernel
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (M : H →L[ℂ] H) (c : ℂ) (hc : c ≠ 0) (u : H)
    (hu : ((1 : H →L[ℂ] H) - c • M) u = 0) : M u = c⁻¹ • u := by
  
  calc
    _ = c⁻¹ • (c • M u) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = _ := congrArg (fun v : H => c⁻¹ • v) (sub_eq_zero.mp (hu)).symm

private theorem projected_mass_preserves_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) (M : H →L[ℂ] H) (hM : IsSelfAdjoint M) (c : ℂ)
    (hS : ∀ v ∈ S, M v = c • v) {u : H} (hu : u ∈ Sᗮ) : M u ∈ Sᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  
  calc
    _ = _ := (hM.isSymmetric v u).symm
    _ = _ := congrArg (fun w : H => ⟪w, u⟫_ℂ) (hS v hv)
    _ = 0 := by simp [inner_smul_left, ((S.mem_orthogonal u).1 hu v hv)]

private theorem projected_compression_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (M : H →L[ℂ] H)
    (hS : ∀ v ∈ S, M v ∈ S) (u : S) :
    ((S.orthogonalProjection ∘L M ∘L S.subtypeL) u : H) = M u := by
  
  exact congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self (K := S)
    (⟨M u, hS u u.property⟩ : S))

private theorem projected_form_coe
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Submodule ℂ H) (M : H →L[ℂ] H) (C : S →L[ℂ] S)
    (hC : ∀ u : S, (C u : H) = M u) (c : ℂ) (u : S) :
    (((1 : S →L[ℂ] S) - c • C) u : H) =
      ((1 : H →L[ℂ] H) - c • M) u := by
  simp [hC]

private theorem projected_inverse_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsUnit A) (x : H) : A (Ring.inverse A x) = x := congrArg (fun B : H →L[ℂ] H => B x) (Ring.mul_inverse_cancel A hA)

private theorem projected_regular_solve
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H) (B : S →L[ℂ] S)
    (hAB : ∀ u : S, A (u : H) = (B u : H)) (hB : IsUnit B) (x : H) :
    A ((S.subtypeL ∘L Ring.inverse B ∘L S.orthogonalProjection) x) =
      S.starProjection x := by
  calc
    _ = _ := hAB (Ring.inverse B (S.orthogonalProjection x))
    _ = _ :=
      congrArg (fun v : S => (v : H))
        (projected_inverse_apply B hB (S.orthogonalProjection x))
    _ = _ := rfl

private theorem projected_shifted_mass_scalar
    (a b : ℂ) (E : ℝ) (h : a = (E : ℂ) * b) :
    b + a = ((E + 1 : ℝ) : ℂ) * b := by
  rw [h]
  push_cast
  ring

private theorem projected_form_pairing_of_solve
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H)
    (W M : H → H → ℂ) (c : ℂ)
    (hA : ∀ v u, ⟪v, A u⟫_ℂ = W v u)
    (hM : ∀ w ∈ S, ∀ v, ⟪v, w⟫_ℂ = c * M v w)
    {u x : H} (hsolve : A u = Sᗮ.starProjection x) (v : H) :
    W v u = ⟪v, x⟫_ℂ - c * M v (S.starProjection x) := by
  calc
    _ = _ := (hA v u).symm
    _ = _ := congrArg (fun w : H => ⟪v, w⟫_ℂ) hsolve
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

/-- Actual resonant vectors satisfy the zero-load weak Neumann equation
against every genuine H¹ test vector. -/
theorem h1Resonant_weak_pairing {Ω : Set ℂ} {E₀ : ℝ}
    {w : NeumannH1 Ω} (hw : w ∈ h1ResonantSpace Ω E₀) (v : NeumannH1 Ω) :
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) =
      (E₀ : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := by
  have hzero : h1HelmholtzForm Ω E₀ w = 0 := hw
  have h := h1HelmholtzForm_inner Ω E₀ v w
  rw [hzero, inner_zero_right] at h
  exact sub_eq_zero.mp h.symm

/-- The shifted H¹ pairing of an actual resonant vector is its physical
mass pairing multiplied by `E₀ + 1`. -/
theorem h1Resonant_inner_eq_mass {Ω : Set ℂ} {E₀ : ℝ}
    {w : NeumannH1 Ω} (hw : w ∈ h1ResonantSpace Ω E₀) (v : NeumannH1 Ω) :
    ⟪v, w⟫_ℂ = ((E₀ + 1 : ℝ) : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := (h1_inner Ω v w).trans
    (projected_shifted_mass_scalar _ _ E₀ (h1Resonant_weak_pairing hw v))

/-- The all-test-vector weak equation for the genuine regular resolvent.
The removed resonant load contributes with a minus sign and the actual
shifted-energy factor `E₀ + 1`. -/
theorem h1RegularResolvent_weak_pairing {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
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
    (fun v u => ⟪h1Value Ω v, h1Value Ω u⟫_ℂ) ((E₀ + 1 : ℝ) : ℂ)
    (h1HelmholtzForm_inner Ω E) (fun _ hw v => h1Resonant_inner_eq_mass hw v)
    (h1RegularResolvent_solve hE₀ hunit x) v

/-- The actual regular solution with normalized boundary load `Q† b`
satisfies the projected weak Neumann equation against every H¹ vector. -/
theorem h1RegularResolvent_adjoint_weak_pairing {Ω : Set ℂ}
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
  exact (h1RegularResolvent_weak_pairing hE₀ hunit
    (ContinuousLinearMap.adjoint Q b) v).trans (projected_adjoint_pairing_sub Q v b _)

end PolyaNeumann

end
