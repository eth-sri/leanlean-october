module

public import RequestProject.QCubeSquareSubdivision

@[expose] public section

/-! Restriction to the actual top cube separates square subdivisions. -/
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem cubeSquareSubdivision_filter_top (d c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : d.spx = {v, w}) :
    (cubeSquareSubdivision d v w hne hs).filter
      (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = c) =
      if d = c then cubeSquareSubdivision d v w hne hs else 0 := by
  classical
  by_cases hdc : d = c
  · rw [if_pos hdc]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    grind [cubeSquareSubdivision_eq_zero_off_top]
  · rw [if_neg hdc]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    grind [cubeSquareSubdivision_eq_zero_off_top]

end FiniteChains.Davis
