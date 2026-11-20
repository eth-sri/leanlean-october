module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Data.Set.Basic

/-!
# Affine set operations on native vectors

Pure set-theoretic translation identities. Measure-preserving and integral
transport statements belong in the later measure layer.
-/

@[expose] public section

namespace PDE

variable {d : ℕ} (z : Vec d) (U : Set (Vec d))

include z U in
/-- Translate a set of native vectors by `z`. -/
def translateSet : Set (Vec d) :=
  {x | ∃ y ∈ U, x = y + z}

theorem mem_translateSet_iff_sub_mem
    {z x : Vec d} {U : Set (Vec d)} :
    x ∈ translateSet z U ↔ x - z ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa
  · intro hx
    refine ⟨x - z, hx, ?_⟩
    simp

theorem preimage_subRight_eq_translateSet :
    (fun x : Vec d => x - z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem]

theorem preimage_addRight_translateSet_eq :
    (fun x : Vec d => x + z) ⁻¹' translateSet z U = U := by
  ext x
  simp [mem_translateSet_iff_sub_mem]

@[simp]
theorem translateSet_zero :
    translateSet (0 : Vec d) U = U := by
  ext x
  simp [translateSet]

end PDE
