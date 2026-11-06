import RequestProject.QCubeSquareSubdivision


/-! Restriction to the actual top cube separates square subdivisions. -/
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem cubeSquareSubdivision_filter_top d c v w hne
    hs :
    (cubeSquareSubdivision d v w hne hs).filter
      (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = c) =
      if d = c then cubeSquareSubdivision d v w hne hs else 0 := by
  classical
  by_cases hdc : d = c
  · rw [if_pos hdc]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro t ht
    by_contra h
    apply ht
    exact cubeSquareSubdivision_eq_zero_off_top d v w hne hs t (by simp_all)
  · rw [if_neg hdc]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro t ht
    apply cubeSquareSubdivision_eq_zero_off_top
    grind
