module

public import RequestProject.PresPosetDimension
public import RequestProject.OrderComparableCycleHomotopy

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

theorem cylinder_strict_three_flags_empty (w : J → List (α × Bool)) :
    IsEmpty (StrictOrdTet (CylBase w)) := by
  refine ⟨fun t => ?_⟩
  have h01 := cylinderDimension_strictMono w t.2.1
  have h12 := cylinderDimension_strictMono w t.2.2.1
  have h23 := cylinderDimension_strictMono w t.2.2.2
  have hb := presPosDimension_le_two w (ConeAdj.inc (S := circSet w) t.1.2.2.2)
  change cylinderDimension w t.1.2.2.2 ≤ 2 at hb
  omega

end FiniteChains.PresModel
