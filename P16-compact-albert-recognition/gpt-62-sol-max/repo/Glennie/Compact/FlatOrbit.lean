module

public import Glennie.Compact.Affine20.Relabel
public import Glennie.Compact.FlatBase
public import Mathlib.Logic.Equiv.Basic
@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

def autOrbit (S : Triple) : Set Triple :=
  {T | ∃ g : CompactAutomorphism, mapAtoms g S = T}

end
end Glennie.SubmissionR03

namespace Glennie.Compact.FlatOrbit

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The compact automorphism action on ordered triples

`mapAtoms g T a i = g.equiv (T a i)` (`Relabel.lean`) is a pointwise action on
all nine atoms at once. The package carries no `Group CompactAutomorphism`
instance, only `refl` (`Automorphism.lean`), `comp` and `symm`,
so the three action laws are recorded here as lemmas. They are what makes
`autOrbit` an equivalence class rather than merely an image. -/

/-- The action is associative. -/
theorem mapAtoms_comp (g h : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g (mapAtoms h T) = mapAtoms (g.comp h) T := rfl

/-- The action is invertible. -/
theorem mapAtoms_symm_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g.symm (mapAtoms g T) = T := by (funext a i; exact g.equiv.symm_apply_apply (T a i))

export Glennie.SubmissionR03 (autOrbit)

theorem frame_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple)
    (hT : IsFrameTriple T) (a : Fin 3) :
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
    rw [mapAtoms_slot]
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
