module

public import Glennie.SectorSubspace
public import Glennie.Theorems.Frames

@[expose] public section

namespace Glennie


section
theorem complexProjection_sub (x y : Albert) :
    complexProjection (x-y) = complexProjection x-complexProjection y := by
  ext <;> simp [complexProjection,complexOct,complexPart]

theorem complexProjection_add (x y : Albert) :
    complexProjection (x+y) = complexProjection x+complexProjection y := by
  ext <;> simp [complexProjection,complexOct,complexPart]

                                                     
                                                             
                                                                     

                                                                         
                                                         

/-- Polynomial projector recovery places the entire frame in the encoder's sector. -/
theorem frame_in_complexSector (p : Fin 3 → Albert) (hp : Frame p)
    (he : InComplexSector (encoder p)) (i : Fin 3) : p i ∈ complexSector := by
  have he' : encoder p ∈ complexSector := (complexSector_mem_iff _).mpr he
  have hs : jordan (encoder p) (encoder p) ∈ complexSector :=
    (complexSector_mem_iff _).mpr (complexSector_jordan _ _ he he)
  have hu : (1 : Albert) ∈ complexSector := by
    rw [complexSector_mem_iff]
    simp [InComplexSector,OctInComplex]
  rw [frame_as_projector p hp]
  fin_cases i
  · exact complexSector.smul_mem _ (complexSector.sub_mem hs he')
  · exact complexSector.sub_mem hu hs
  · exact complexSector.smul_mem _ (complexSector.add_mem hs he')


end
end Glennie
