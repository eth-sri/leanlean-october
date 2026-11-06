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
def h1ResonantInclusion (Ω : Set ℂ) (E : ℝ) :
    h1ResonantSpace Ω E →ₗ[ℂ] neumannEigenspace Ω E where
  toFun u := ⟨h1Value Ω u,
    h1HelmholtzForm_kernel_mem Ω E u u.property⟩
  map_add' u v := Subtype.ext ((h1Value Ω).map_add u v)
  map_smul' c u := Subtype.ext ((h1Value Ω).map_smul c u)

theorem h1ResonantInclusion_injective {Ω : Set ℂ} (hΩ : IsOpen Ω) (E : ℝ) :
    Function.Injective (h1ResonantInclusion Ω E) := by
  intro u v huv
  apply Subtype.ext
  apply h1Value_injective hΩ
  exact congrArg Subtype.val huv

/-- Every genuine weak eigenfunction has an H¹ lift in the form kernel. -/
theorem h1ResonantInclusion_surjective (Ω : Set ℂ) (E : ℝ) :
    Function.Surjective (h1ResonantInclusion Ω E) := by
  intro u
  obtain ⟨g, hg, hw⟩ := u.property
  have hzero : h1HelmholtzForm Ω E (h1Vector hg) = 0 := by
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, inner_zero_right]
    simp only [h1Value_h1Vector, h1Gradient_h1Vector]
    exact sub_eq_zero.mpr (hw (h1Value Ω v) (fun i => h1Gradient Ω i v)
      (h1Value_weakGradient Ω v))
  exact ⟨⟨h1Vector hg, hzero⟩, Subtype.ext rfl⟩

def h1ResonantEquiv {Ω : Set ℂ} (hΩ : IsOpen Ω) (E : ℝ) :
    h1ResonantSpace Ω E ≃ₗ[ℂ] neumannEigenspace Ω E :=
  LinearEquiv.ofBijective (h1ResonantInclusion Ω E)
    ⟨h1ResonantInclusion_injective hΩ E, h1ResonantInclusion_surjective Ω E⟩

theorem h1ResonantSpace_multiplicity_eq {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (h1ResonantSpace Ω E) : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [(h1ResonantEquiv hL.1.1 E).finrank_eq]
  exact neumannEigenvalue_multiplicity_eq hb hL hE

end PolyaNeumann

end
