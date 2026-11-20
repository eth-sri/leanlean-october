module

public import RequestProject.PresPosetDimension
public import RequestProject.OrderComparableCycleHomotopy

@[expose] public section


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

theorem rose_strict_triangles_empty : IsEmpty (StrictOrdTri (Rose α)) := by
  refine ⟨fun t => ?_⟩
  have h01 := roseDimension_strictMono t.2.1
  have h12 := roseDimension_strictMono t.2.2
  have hlo : 1 ≤ roseDimension t.1.1 := by cases t.1.1 <;> simp [roseDimension]
  have hhi : roseDimension t.1.2.2 ≤ 2 := by cases t.1.2.2 <;> simp [roseDimension]
  omega

end FiniteChains.PresModel
