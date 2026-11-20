/- Ordered-frame extension of native unital generation.
Unital generation comes from the native endpoint; no span premise. -/
module
public import Glennie.NativeGenerationEndpointR01
public import Glennie.Compact.LocalReconstruction

@[expose] public section
namespace Glennie.NativeOrderedFrameGenerationR01
noncomputable section
open Glennie.NativeGenerationEndpointR01
open Glennie.Compact.Affine20
open Glennie.Compact.Sections
open Glennie.Compact.LocalContrast

/-- The ambient unit is recovered from the actual frame sum, so a submodule
containing all labelled atoms has the required unital generation property. -/
theorem ordered_frame_atoms_generate
    (T : Triple) (hT : ∀ a, Frame (T a)) (hphi : phiOf T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hu : (1 : Albert) ∈ K := by
    rw [← (hT 0).sum_unit]
    exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
  apply eq_top_of_phi_ne_zero K hu hJ
    (encoder (T 0)) (encoder (T 1)) (encoder (T 2))
  · exact K.sub_mem (hAtoms 0 2) (hAtoms 0 0)
  · exact K.sub_mem (hAtoms 1 2) (hAtoms 1 0)
  · exact K.sub_mem (hAtoms 2 2) (hAtoms 2 0)
  · exact hphi

theorem ordered_frame_atoms_generate_of_score
    (T : Triple) (hT : ∀ a, Frame (T a)) (hs : score T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  apply ordered_frame_atoms_generate T hT _ K hJ hAtoms
  intro hz
  apply hs
  rw [score_eq_two_phi, hz, mul_zero]

end
end Glennie.NativeOrderedFrameGenerationR01
