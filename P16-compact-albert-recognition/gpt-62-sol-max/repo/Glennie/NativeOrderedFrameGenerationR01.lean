/- Ordered-frame extension of native unital generation.
Unital generation comes from the native endpoint; no span premise. -/
module
public import Glennie.NativeGenerationEndpointR01
public import Glennie.Compact.ObservationData
@[expose] public section
namespace Glennie.NativeOrderedFrameGenerationR01
noncomputable section
open Glennie.NativeGenerationEndpointR01
open Glennie.Compact.Affine20
open SubmissionR03 (phiOf score score_eq_two_phi)

/-- The ambient unit is recovered from the actual frame sum, so a submodule
containing all labelled atoms has the required unital generation property. -/
theorem ordered_frame_atoms_generate
    (T : Triple) (hT : IsFrameTriple T) (hphi : phiOf T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : JordanClosed K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hu : (1 : Albert) ∈ K := by
    rw [← (hT 0).sum_unit]
    exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
  have enc (a : Fin 3) : encoder (T a) ∈ K := K.sub_mem (hAtoms a 2) (hAtoms a 0)
  exact eq_top_of_phi_ne_zero K hu hJ _ _ _ (enc 0) (enc 1) (enc 2) hphi

theorem _root_.Glennie.SubmissionR03.atoms_generate_of_score
    (T : Triple) (hT : IsFrameTriple T) (hs : score T ≠ 0)
    (K : Submodule ℝ Albert)
    (hJ : JordanClosed K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ :=
  ordered_frame_atoms_generate T hT (fun h => hs (by simp [score_eq_two_phi, h])) K hJ hAtoms

end
end Glennie.NativeOrderedFrameGenerationR01
