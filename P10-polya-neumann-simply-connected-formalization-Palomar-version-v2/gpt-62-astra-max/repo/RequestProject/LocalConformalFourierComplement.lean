module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.PositiveFourierBasis
public import RequestProject.PlanarNotation

/-!
# A genuine finite Fourier complement for the physical conormal chart

The finite-rank completion is chosen in the actual standard Fourier bases.
Both vectors of every rank-one correction have finite Fourier support.
This is the extra property needed for preservation of Sobolev regularity;
finite rank alone would not imply that property.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set Filter
open scoped Topology InnerProductSpace

local notation "H₀" => nonpositiveFourierSubspace

theorem normalizedConormal_fixed_fourier_complement
    {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b) (ha : IsWL1 (1 / 2) a)
    (hg : IsWL1 (1 / 2) g) {E₀ : ℝ}
    (hinj : Function.Injective ((normalizedConormal hb ha hg E₀).comp (H₀).subtypeL)) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      (∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite) ∧
      (∀ r, (Function.support (v r : ℤ → ℂ)).Finite) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((normalizedConormal hb ha hg (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse
          ((normalizedConormal hb ha hg (E : ℂ)).comp (H₀).subtypeL ∘L
            (H₀).orthogonalProjection +
            (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
              H₀ᗮ.orthogonalProjection)) U := by
  
  have heq : (normalizedConormal hb ha hg E₀).comp (H₀).subtypeL ∘L
      (H₀).orthogonalProjection + Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection -
        1 =
      (normalizedConormal hb ha hg E₀ - 1) ∘L
        ((H₀).subtypeL ∘L (H₀).orthogonalProjection) := by
    ext1 x
    have hx := (H₀).starProjection_add_starProjection_orthogonal x
    rw [Submodule.starProjection_apply, Submodule.starProjection_apply] at hx
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, Submodule.subtypeL_apply]
    rw [← sub_eq_zero]
    have horth : (H₀ᗮ.orthogonalProjection x : L2Z) =
        x - ((H₀).orthogonalProjection x : L2Z) := by
      simp
    rw [horth]
    abel
  have hcpt : IsCompactOperator ((normalizedConormal hb ha hg E₀).comp (H₀).subtypeL ∘L
      (H₀).orthogonalProjection + Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection -
        (1 : L2Z →L[ℂ] L2Z)) := by
    rw [heq]
    exact (isCompactOperator_normalizedConormal_sub_one hb ha hg E₀).comp_clm _
  obtain ⟨d, u, v, hu, hv, U, hU, hunit, hcont⟩ :=
    exists_fixed_complement_basis H₀ (((continuous_normalizedConormal hb ha hg).comp Complex.continuous_ofReal).clm_comp
      continuous_const) hcpt hinj stdBasisZ positiveFourierHilbertBasis
  exact ⟨d, u, v,
    (fun r => finite_support_of_mem_span_positiveFourierHilbertBasis (hu r)),
    (fun r => finite_support_of_mem_span_stdBasisZ (hv r)), U, hU, hunit, hcont⟩

section PhysicalCoordinates

theorem exists_localConformal_fixed_fourier_complement_of_cutC_ne_zero (Φ : DiskCoordinates) {E₀ : ℝ}
    (hE₀ : 0 ≤ E₀) {W : TransportPath} (hW : IsTransport Φ.boundary E₀ W)
    (hcut : cutVector W ≠ 0) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      (∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite) ∧
      (∀ r, (Function.support (v r : ℤ → ℂ)).Finite) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((Φ.conormal (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse ((Φ.conormal (E : ℂ)).comp (H₀).subtypeL ∘L
          (H₀).orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) U := by
  apply normalizedConormal_fixed_fourier_complement (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ)
  intro b d hbd
  apply Subtype.ext
  exact (localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero
    Φ E₀ hE₀ hW hcut)
    b.property d.property hbd

end PhysicalCoordinates

end PolyaNeumann

end
