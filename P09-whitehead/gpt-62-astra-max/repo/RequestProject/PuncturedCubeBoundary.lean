module

public import RequestProject.CoordinateFacetContraction

@[expose] public section

/-! The actual proper face poset of an ordinary cube, with one facet deleted, contracts
onto the opposite facet by an explicit zigzag of monotone coordinate maps. -/
namespace FiniteChains.Davis
open Comb
variable {V : Type} [DecidableEq V]

variable (t : Cube V) (j : V) (b : CubeCoord)

def PuncturedCubeFace :=
  {c : Cube V // CoordinateFace c t ∧ c ≠ t ∧ c ≠ coordinateFix j b t}

instance : PartialOrder (PuncturedCubeFace t j b) where
  le c d := CoordinateFace c.1 d.1
  le_refl c v := Or.inr rfl
  le_trans c d e hcd hde v := by
    rcases hde v with he | he
    · exact Or.inl he
    · rcases hcd v with hd | hd <;> simp_all
  le_antisymm c d hcd hdc := by
    apply Subtype.ext
    funext v
    rcases hcd v with hd | hd
    · rcases hdc v with hc | hc <;> simp_all
    · exact hd

omit [DecidableEq V] in
theorem face_trans {c d e : Cube V} (hcd : CoordinateFace c d)
    (hde : CoordinateFace d e) : CoordinateFace c e := by
  intro v
  rcases hde v with he | he
  · exact Or.inl he
  · rcases hcd v with hd | hd <;> simp_all

variable (t : Cube V) (j : V) (b z : CubeCoord)
  (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
  (ht : t j = CubeCoord.free)

variable (c : PuncturedCubeFace t j b)

def punctureProject : PuncturedCubeFace t j b :=
  ⟨coordinateFix j z c.1,
    face_trans (coordinate_fix_face_open j z c.1)
      (coordinateOpen_face_top j z ht c.2.1),
    coordinateFix_ne_top j z hz ht, coordinateFix_ne_facet j b z hbz c.1 t⟩

def punctureOpen : PuncturedCubeFace t j b :=
  ⟨coordinateOpen j z c.1,
    coordinateOpen_face_top j z ht c.2.1,
    coordinateOpen_ne_top j b z hb hz hbz ht c.2.2.1 c.2.2.2,
    coordinateOpen_ne_facet j b z hb hbz c.1 t⟩

def punctureOpposite : PuncturedCubeFace t j b :=
  ⟨coordinateFix j z t,
    face_trans (coordinate_fix_face_open j z t)
      (coordinateOpen_face_top j z ht (fun _ => Or.inr rfl)),
    coordinateFix_ne_top j z hz ht, coordinateFix_ne_facet j b z hbz t t⟩

theorem punctureProject_monotone : Monotone (punctureProject t j b z hz hbz ht) := by
  solve_by_elim [coordinateFix_face_mono]

theorem punctureOpen_monotone : Monotone (punctureOpen t j b z hb hz hbz ht) := by
  solve_by_elim [coordinateOpen_face_mono]

include z hb hz hbz ht in
/-- Every based edge loop of the ordinary punctured cube boundary is null homotopic. -/
theorem puncturedCubeBoundary_simplyConnected :
    SimplyConnected (orderCx (PuncturedCubeFace t j b)) := by
  apply simplyConnected_orderCx_of_zigzag
    (punctureProject_monotone t j b z hz hbz ht)
    (punctureOpen_monotone t j b z hb hz hbz ht)
    (fun c => coordinate_face_open j z c.1)
    (fun c => coordinate_fix_face_open j z c.1)
    (punctureOpposite t j b z hz hbz ht)
  intro c
  exact coordinateFix_face_opposite_facet j z c.2.1

include z hb hz hbz ht in
theorem puncturedCubeBoundary_isConnected :
    IsConnected (orderCx (PuncturedCubeFace t j b)) := by
  apply isConnected_orderCx_of_zigzag
    (f := punctureProject t j b z hz hbz ht)
    (g := punctureOpen t j b z hb hz hbz ht)
    (fun c => coordinate_face_open j z c.1)
    (fun c => coordinate_fix_face_open j z c.1)
    (punctureOpposite t j b z hz hbz ht)
  intro c
  exact coordinateFix_face_opposite_facet j z c.2.1

/-- Every genuine facet puncture is connected; no contraction data are assumed. -/
theorem ordinary_puncturedCubeBoundary_connected (t : Cube V) (j : V) (b : CubeCoord)
    (hb : b ≠ CubeCoord.free) (ht : t j = CubeCoord.free) :
    IsConnected (orderCx (PuncturedCubeFace t j b)) := by
  cases b with
  | free => simp_all
  | pos => exact puncturedCubeBoundary_isConnected t j .pos .neg hb (by decide) (by decide) ht
  | neg => exact puncturedCubeBoundary_isConnected t j .neg .pos hb (by decide) (by decide) ht

/-- Every genuine facet puncture is simply connected; no homotopy property is assumed. -/
theorem ordinary_puncturedCubeBoundary_simplyConnected (t : Cube V) (j : V) (b : CubeCoord)
    (hb : b ≠ CubeCoord.free) (ht : t j = CubeCoord.free) :
    SimplyConnected (orderCx (PuncturedCubeFace t j b)) := by
  cases b with
  | free => simp_all
  | pos => exact puncturedCubeBoundary_simplyConnected t j .pos .neg hb (by decide) (by decide) ht
  | neg => exact puncturedCubeBoundary_simplyConnected t j .neg .pos hb (by decide) (by decide) ht

end FiniteChains.Davis
