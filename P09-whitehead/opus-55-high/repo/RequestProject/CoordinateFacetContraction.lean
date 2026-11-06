import RequestProject.QCubeCoordinateEquiv
import RequestProject.OrderCxNullTransfer


/-! Coordinate maps used to contract a cube boundary after deletion of one facet. -/
namespace FiniteChains.Davis
variable {V : Type} [DecidableEq V]

def coordinateFix (j : V) (z : CubeCoord) (c : Cube V) : Cube V :=
  Function.update c j z

/-- Open the selected coordinate, except on the opposite facet, which stays fixed. -/
def coordinateOpen (j : V) (z : CubeCoord) (c : Cube V) :=
  if c j = z then c else Function.update c j CubeCoord.free

theorem coordinateFix_face_mono j z {c d : Cube V}
    (h : CoordinateFace c d) : CoordinateFace (coordinateFix j z c) (coordinateFix j z d) := by
  intro v
  by_cases hv : v = j
  · simp_all [coordinateFix, Function.update_self]
  · simpa [coordinateFix, Function.update_of_ne hv] using h v

theorem coordinateOpen_face_mono j z (hz : z ≠ CubeCoord.free)
    {c d : Cube V} (h : CoordinateFace c d) :
    CoordinateFace (coordinateOpen j z c) (coordinateOpen j z d) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hd : d j = z
    · have hc : c j = z := by
        rcases h j with hf | he
        · simp_all
        simp_all
      right
      simp [coordinateOpen, hc, hd]
    · left
      simp [coordinateOpen, if_neg hd, Function.update_self]
  · have hc : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      grind
    have hd : coordinateOpen j z d v = d v := by
      unfold coordinateOpen
      grind
    aesop

theorem coordinate_face_open j z (c : Cube V) :
    CoordinateFace c (coordinateOpen j z c) := by
  intro v
  unfold coordinateOpen
  grind

theorem coordinate_fix_face_open j z (c : Cube V) :
    CoordinateFace (coordinateFix j z c) (coordinateOpen j z c) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hc : c j = z
    · right
      simp [coordinateFix, coordinateOpen, hc, Function.update_self]
    · left
      simp [coordinateOpen, if_neg hc, Function.update_self]
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      grind
    right
    simp [coordinateFix, Function.update_of_ne hv, ho]

theorem coordinateFix_face_opposite_facet j z
    {c t : Cube V} (h : CoordinateFace c t) :
    CoordinateFace (coordinateFix j z c) (coordinateFix j z t) :=
  coordinateFix_face_mono j z h

theorem coordinateOpen_face_top j z
    {c t : Cube V} (ht : t j = CubeCoord.free) (h : CoordinateFace c t) :
    CoordinateFace (coordinateOpen j z c) t := by
  intro v
  by_cases hv : v = j
  · simp_all
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      grind
    aesop

theorem cubeCoord_cases_of_opposite b z (hb : b ≠ CubeCoord.free)
    (hz : z ≠ CubeCoord.free) (hbz : b ≠ z) s :
    s = CubeCoord.free ∨ s = b ∨ s = z := by
  cases b <;> cases z <;> cases s <;> simp_all

theorem coordinateOpen_ne_top j b z
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    {c t : Cube V} (ht : t j = CubeCoord.free) (hct : c ≠ t)
    (hcf : c ≠ coordinateFix j b t) : coordinateOpen j z c ≠ t := by
  intro he
  by_cases hc : c j = z
  · exact hct (by simpa [coordinateOpen, hc] using he)
  · have hrest : ∀ v, v ≠ j → c v = t v := by
      intro v hv
      have hh := congrFun he v
      simp_all [coordinateOpen, Function.update_of_ne hv]
    rcases cubeCoord_cases_of_opposite b z hb hz hbz (c j) with hfree | hval | hval
    · grind
    · apply hcf
      funext v
      by_cases hv : v = j
      · simp_all [coordinateFix, Function.update_self]
      · simp_all [coordinateFix]
    simp_all

theorem coordinateFix_ne_top j z (hz : z ≠ CubeCoord.free)
    {c t : Cube V} (ht : t j = CubeCoord.free) : coordinateFix j z c ≠ t := by
  intro he
  have hh := congrFun he j
  simp_all [coordinateFix, Function.update_self, ht]

theorem coordinateFix_ne_facet j b z (hbz : b ≠ z)
    (c t : Cube V) : coordinateFix j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  simp_all [coordinateFix, Function.update_self]

theorem coordinateOpen_ne_facet j b z
    (hb : b ≠ CubeCoord.free) (hbz : b ≠ z) (c t : Cube V) :
    coordinateOpen j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  by_cases hc : c j = z
  · simp_all [coordinateOpen, coordinateFix, Function.update_self]
  · simp_all [coordinateOpen, coordinateFix, Function.update_self]
