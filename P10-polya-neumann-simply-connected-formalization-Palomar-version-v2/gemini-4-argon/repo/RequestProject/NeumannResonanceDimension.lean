module

public import RequestProject.NeumannBoundaryPole
public import RequestProject.NeumannSpectral

/-!
# Dimension of the genuine form resonance space

The H¹ kernel used in the boundary pole is linearly equivalent to the
original weak Neumann eigenspace. Its complex dimension therefore agrees
with the multiplicity in the original variational sequence.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Topology
open scoped InnerProductSpace

/-- Inclusion sends the actual form kernel to the weak eigenspace. -/
def h1ResonantInclusion Ω E :
    h1ResonantSpace Ω E →ₗ[ℂ] neumannEigenspace Ω E where
  toFun u := ⟨h1Value Ω u,
    h1HelmholtzForm_kernel_mem Ω E u u.property⟩
  map_add' u v := Subtype.ext ((h1Value Ω).map_add u v)
  map_smul' c u := Subtype.ext ((h1Value Ω).map_smul c u)

theorem h1ResonantSpace_multiplicity_eq  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hE : 0 ≤ E) :
    (Module.finrank ℂ (h1ResonantSpace Ω E) : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [(LinearEquiv.ofBijective (h1ResonantInclusion Ω E) ⟨(by
    intro u v huv
    apply Subtype.ext
    apply h1Value_injective hL.1.1
    exact congrArg Subtype.val huv), (show Function.Surjective (h1ResonantInclusion Ω E) by
      intro u
      obtain ⟨g, hg, hw⟩ := u.property
      exact ⟨⟨h1Vector hg, (show h1HelmholtzForm Ω E (h1Vector hg) = 0 by
        apply ext_inner_left ℂ
        intro v
        rw [h1HelmholtzForm_inner, inner_zero_right]
        simp only [h1Value_h1Vector, h1Gradient_h1Vector]
        exact sub_eq_zero.mpr (hw (h1Value Ω v) (fun i => h1Gradient Ω i v)
          (h1Value_weakGradient Ω v)))⟩, Subtype.ext rfl⟩)⟩).finrank_eq]
  exact neumannEigenvalue_multiplicity_eq hb hL hE

end PolyaNeumann

end
