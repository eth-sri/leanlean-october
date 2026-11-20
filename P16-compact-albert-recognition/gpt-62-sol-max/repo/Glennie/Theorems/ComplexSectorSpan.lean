module

public import Glennie.SectorSubspace
public import Glennie.Theorems.ProjectorFrame
/- Native frame adapters into the actual nine-dimensional complex sector.
The coordinate submodule and its dimension are proved in SectorSubspace. -/

public section
namespace Glennie
noncomputable section

theorem frame_in_complexSector (p : Fin 3 → Albert) (hp : Frame p)
    (he : InComplexSector (encoder p)) (i : Fin 3) : p i ∈ complexSector := by
  have he' : encoder p ∈ complexSector := (complexSector_mem_iff _).mpr he
  have hs : jordan (encoder p) (encoder p) ∈ complexSector :=
    (complexSector_mem_iff _).mpr (complexSector_jordan _ _ he he)
  have hu : (1 : Albert) ∈ complexSector := by
    rw [complexSector_mem_iff]
    simp [InComplexSector, OctInComplex]
  rw [frame_as_projector p hp]
  fin_cases i <;> simp [projectorFrame, he', hs, hu,
    Submodule.add_mem, Submodule.sub_mem]


end
end Glennie
