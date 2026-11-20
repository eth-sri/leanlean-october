module

public import RequestProject.NeumannBoundaryPole
public import RequestProject.NeumannMultiplicity

/-! The form kernel injects into the weak Neumann eigenspace, so its
dimension is bounded by the variational multiplicity. -/

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

theorem h1ResonantSpace_multiplicity_le {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (h1ResonantSpace Ω E) : ℕ∞) ≤
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  letI := finiteDimensional_neumannEigenspace hb hL E
  exact (ENat.coe_le_coe.mpr (LinearMap.finrank_le_finrank_of_injective
    (h1ResonantInclusion_injective hL.1.1 E))).trans (finrank_neumannEigenspace_le hb hL hE)

end PolyaNeumann
end
