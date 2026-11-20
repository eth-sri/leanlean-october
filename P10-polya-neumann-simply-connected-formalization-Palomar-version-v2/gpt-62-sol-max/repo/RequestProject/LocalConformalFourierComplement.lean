module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalVekuaForward
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.PositiveFourierBasis

/-!
# A genuine finite Fourier complement for the physical conormal chart

The finite-rank completion is chosen in the actual standard Fourier bases.
The output vector of each rank-one correction has finite Fourier support.
This is the extra property needed for preservation of Sobolev regularity;
finite rank alone would not imply that property.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter
open scoped Topology InnerProductSpace

local notation "H₀" => nonpositiveFourierSubspace

theorem normalizedConormal_fixed_fourier_complement
    {b a g : ℤ → ℂ} (hb : IsWL1 (1 / 2) b) (ha : IsWL1 (1 / 2) a)
    (hg : IsWL1 (1 / 2) g) {E₀ : ℝ}
    (hinj : Function.Injective ((normalizedConormal hb ha hg E₀).comp (H₀).subtypeL)) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      (∀ r, (Function.support (v r : ℤ → ℂ)).Finite) ∧
      ∀ᶠ E : ℝ in 𝓝 E₀, IsUnit ((normalizedConormal hb ha hg (E : ℂ)).comp (H₀).subtypeL ∘L
        (H₀).orthogonalProjection +
        (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) ∘L
          H₀ᗮ.orthogonalProjection) := by
  have hJ : Continuous fun E : ℝ =>
      (normalizedConormal hb ha hg (E : ℂ)).comp (H₀).subtypeL :=
    ((continuous_normalizedConormal hb ha hg).comp Complex.continuous_ofReal).clm_comp
      continuous_const
  have heq : (normalizedConormal hb ha hg E₀).comp (H₀).subtypeL ∘L
      (H₀).orthogonalProjection + Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection -
        (1 : L2Z →L[ℂ] L2Z) =
      (normalizedConormal hb ha hg E₀ - (1 : L2Z →L[ℂ] L2Z)) ∘L
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
  obtain ⟨d, u, v, hv, hunit⟩ := exists_fixed_complement_basis H₀ hJ hcpt hinj stdBasisZ
  exact ⟨d, u, v, fun r => finite_support_of_mem_span_stdBasisZ (hv r), hunit⟩

end PolyaNeumann

end
