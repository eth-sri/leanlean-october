module

public import RequestProject.QCubeCoordinateEquiv
public import RequestProject.OrderCxNullTransfer

@[expose] public section

/-! Coordinate maps used to contract a cube boundary after deletion of one facet. -/
namespace FiniteChains.Davis
variable {V : Type} [DecidableEq V]

variable (j : V) (z : CubeCoord)

variable (c : Cube V)

def coordinateFix :=
  Function.update c j z

/-- Open the selected coordinate, except on the opposite facet, which stays fixed. -/
def coordinateOpen :=
  if c j = z then c else Function.update c j CubeCoord.free

theorem coordinateFix_face_mono {c d : Cube V}
    (h : CoordinateFace c d) : CoordinateFace (coordinateFix j z c) (coordinateFix j z d) := by
  intro v
  by_cases hv : v = j
  · simp_all [coordinateFix, Function.update_self]
  · simpa only [coordinateFix, Function.update_of_ne hv] using h v

theorem coordinateOpen_face_mono (hz : z ≠ CubeCoord.free)
    {c d : Cube V} (h : CoordinateFace c d) :
    CoordinateFace (coordinateOpen j z c) (coordinateOpen j z d) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hd : d j = z
    · have hc : c j = z := by
        rcases h j with hf | he
        · simp_all
        · exact he.trans hd
      simp [coordinateOpen, hc, hd]
    · simp_all [coordinateOpen, if_neg, Function.update_self]
  · have hc : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      grind
    have hd : coordinateOpen j z d v = d v := by
      unfold coordinateOpen
      grind
    aesop

variable (c : Cube V)

theorem coordinate_face_open :
    CoordinateFace c (coordinateOpen j z c) := by
  intro v
  unfold coordinateOpen <;> grind

theorem coordinate_fix_face_open :
    CoordinateFace (coordinateFix j z c) (coordinateOpen j z c) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hc : c j = z
    · simp [coordinateFix, coordinateOpen, hc, Function.update_self]
    · simp_all [coordinateOpen, if_neg, Function.update_self]
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      grind
    simp_all [coordinateFix, Function.update_of_ne, ho]

variable {c t : Cube V}

theorem coordinateFix_face_opposite_facet (h : CoordinateFace c t) :
    CoordinateFace (coordinateFix j z c) (coordinateFix j z t) :=
  coordinateFix_face_mono j z h

theorem coordinateOpen_face_top (ht : t j = CubeCoord.free) (h : CoordinateFace c t) :
    CoordinateFace (coordinateOpen j z c) t := by
  intro v
  by_cases hv : v = j
  · simp_all
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      grind
    aesop

theorem cubeCoord_cases_of_opposite (b z : CubeCoord) (hb : b ≠ CubeCoord.free)
    (hz : z ≠ CubeCoord.free) (hbz : b ≠ z) (s : CubeCoord) :
    s = CubeCoord.free ∨ s = b ∨ s = z := by
  cases b <;> cases z <;> cases s <;> simp_all

variable (j : V)

theorem coordinateOpen_ne_top (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    {c t : Cube V} (ht : t j = CubeCoord.free) (hct : c ≠ t)
    (hcf : c ≠ coordinateFix j b t) : coordinateOpen j z c ≠ t := by
  intro he
  by_cases hc : c j = z
  · simp_all [coordinateOpen, hc]
  · have hrest : ∀ v, v ≠ j → c v = t v := by
      intro v hv
      have hh := congrFun he v
      simp_all [coordinateOpen, if_neg, Function.update_of_ne]
    rcases cubeCoord_cases_of_opposite b z hb hz hbz (c j) with hfree | hval | hval
    · grind
    · apply hcf
      funext v
      by_cases hv : v = j
      · simp_all [coordinateFix, Function.update_self]
      · simp_all [coordinateFix, Function.update_of_ne]
    · exact hc hval

theorem coordinateFix_ne_top (z : CubeCoord) (hz : z ≠ CubeCoord.free)
    {c t : Cube V} (ht : t j = CubeCoord.free) : coordinateFix j z c ≠ t := by
  intro he
  have hh := congrFun he j
  simp_all [coordinateFix, Function.update_self, ht]

variable (b z : CubeCoord)

theorem coordinateFix_ne_facet (hbz : b ≠ z)
    (c t : Cube V) : coordinateFix j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  simp_all [coordinateFix, Function.update_self]

theorem coordinateOpen_ne_facet
    (hb : b ≠ CubeCoord.free) (hbz : b ≠ z) (c t : Cube V) :
    coordinateOpen j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  by_cases hc : c j = z
  · simp_all [coordinateOpen, if_pos, coordinateFix, Function.update_self]
  · simp_all [coordinateOpen, if_neg, coordinateFix, Function.update_self]

end FiniteChains.Davis
