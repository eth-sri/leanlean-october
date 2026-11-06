import Mathlib.Tactic

import RequestProject.QCubeCoordinateEquiv
import RequestProject.OrderCxNullTransfer

/-! Coordinate maps used to contract a cube boundary after deletion of one facet. -/
namespace FiniteChains.Davis
variable {V : Type} [DecidableEq V]

  (j : V)
  (z : CubeCoord)
def coordinateFix   (c : Cube V)  :=
  Function.update c j z

/-- Open the selected coordinate, except on the opposite facet, which stays fixed. -/
def coordinateOpen   (c : Cube V)  :=
  if c j = z then c else Function.update c j CubeCoord.free

theorem coordinateFix_face_mono   {c d : Cube V}
    (h : CoordinateFace c d) : CoordinateFace (coordinateFix j z c) (coordinateFix j z d) := by
  intro v
  by_cases hv : v = j
  · simp_all [coordinateFix]
  · aesop (add simp [coordinateFix])

theorem coordinateOpen_face_mono   (hz : z ≠ CubeCoord.free)
    {c d : Cube V} (h : CoordinateFace c d) :
    CoordinateFace (coordinateOpen j z c) (coordinateOpen j z d) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hd : d j = z
    · have hc : c j = z := by
        rcases h j with hf | he
        · exact False.elim (hz (hd.symm.trans hf))
        · exact he.trans hd
      right
      simp [coordinateOpen, hc, hd]
    · simp_all [coordinateOpen]
  aesop (add simp [coordinateOpen])

theorem coordinate_face_open   (c : Cube V) :
    CoordinateFace c (coordinateOpen j z c) := by
  intro v
  unfold coordinateOpen
  grind

theorem coordinate_fix_face_open   (c : Cube V) :
    CoordinateFace (coordinateFix j z c) (coordinateOpen j z c) := by
  intro v
  by_cases hv : v = j
  · aesop (add simp [coordinateFix, coordinateOpen, Function.update_self])
  · aesop (add simp [coordinateOpen, coordinateFix])

abbrev coordinateFix_face_opposite_facet :=
  @FiniteChains.Davis.coordinateFix_face_mono

theorem coordinateOpen_face_top  
    {c t : Cube V} (ht : t j = CubeCoord.free) (h : CoordinateFace c t) :
    CoordinateFace (coordinateOpen j z c) t := by
  intro v
  by_cases hv : v = j
  · subst v
    exact Or.inl ht
  · aesop (add simp [coordinateOpen])

variable (b z : CubeCoord)
theorem cubeCoord_cases_of_opposite  (hb : b ≠ CubeCoord.free)
    (hz : z ≠ CubeCoord.free) (hbz : b ≠ z) (s : CubeCoord) :
    s = CubeCoord.free ∨ s = b ∨ s = z := by
  cases b <;> cases z <;> cases s <;> simp_all

theorem coordinateOpen_ne_top  
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    {c t : Cube V} (ht : t j = CubeCoord.free) (hct : c ≠ t)
    (hcf : c ≠ coordinateFix j b t) : coordinateOpen j z c ≠ t := by
  intro he
  by_cases hc : c j = z
  · simp_all [coordinateOpen]
  · have hrest : ∀ v, v ≠ j → c v = t v := by
      aesop (add simp [coordinateOpen])
    rcases cubeCoord_cases_of_opposite b z hb hz hbz (c j) with hfree | hval | hval
    · grind
    · apply hcf
      funext v
      by_cases hv : v = j
      · simp_all [coordinateFix]
      · simp_all [coordinateFix]
    · exact hc hval

theorem coordinateFix_ne_top   (hz : z ≠ CubeCoord.free)
    {c t : Cube V} (ht : t j = CubeCoord.free) : coordinateFix j z c ≠ t := by aesop (add simp [coordinateFix, Function.update_self, ht])

theorem coordinateFix_ne_facet   (hbz : b ≠ z)
    (c t : Cube V) : coordinateFix j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  simp [coordinateFix] at hh
  exact hbz hh.symm

theorem coordinateOpen_ne_facet  
    (hb : b ≠ CubeCoord.free) (hbz : b ≠ z) (c t : Cube V) :
    coordinateOpen j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  by_cases hc : c j = z
  · simp_all [coordinateOpen, coordinateFix]
  · simp_all [coordinateOpen, coordinateFix]

end FiniteChains.Davis
