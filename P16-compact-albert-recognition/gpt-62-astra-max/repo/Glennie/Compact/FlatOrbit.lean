module
public import Glennie.Compact.FrameTopology
@[expose] public section
namespace Glennie.Compact.FlatOrbit
noncomputable section
open Affine20
theorem mapAtoms_refl (T : Triple) :
    mapAtoms Glennie.CompactAutomorphism.refl T = T := rfl

/-- The action is associative. -/
theorem mapAtoms_comp (g h : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g (mapAtoms h T) = mapAtoms (g.comp h) T := rfl

/-- The action is invertible. -/
theorem mapAtoms_symm_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g.symm (mapAtoms g T) = T := by
  funext a i
  exact g.equiv.symm_apply_apply (T a i)

export _root_.Glennie.SubmissionR03 (autOrbit)

/-- Frames are preserved slotwise, by `map_frame` (`Automorphism.lean`). -/
theorem frame_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple)
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) (a : Fin 3) :
    Glennie.Frame (mapAtoms g T a) :=
  g.map_frame (T a) (hT a)

/-- Phi is an orbit invariant. This is the whole separation mechanism: `encoder_map`
(`Automorphism.lean`) moves the automorphism out of each encoder and `phi_map`
(`:49`) then cancels it. No genericity guard and no side condition. -/
theorem phi_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    Glennie.phi (Glennie.encoder (mapAtoms g T 0)) (Glennie.encoder (mapAtoms g T 1))
        (Glennie.encoder (mapAtoms g T 2)) =
      Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
        (Glennie.encoder (T 2)) := by
  have h : ∀ a : Fin 3,
      Glennie.encoder (mapAtoms g T a) = g.equiv (Glennie.encoder (T a)) := by
    intro a
    exact g.encoder_map (T a)
  rw [h 0, h 1, h 2, g.phi_map]

theorem phi_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1)) (Glennie.encoder (T 2)) =
      Glennie.phi (Glennie.encoder (S 0)) (Glennie.encoder (S 1))
        (Glennie.encoder (S 2)) := by
  obtain ⟨g, rfl⟩ := h
  exact phi_mapAtoms g S

end
end Glennie.Compact.FlatOrbit
