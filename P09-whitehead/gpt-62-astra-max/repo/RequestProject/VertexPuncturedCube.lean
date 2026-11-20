module

public import RequestProject.CoordinateFacetContraction

@[expose] public section

/-! Coordinate regions of the proper three-cube boundary with its positive vertex removed. -/
namespace FiniteChains.Davis
open Comb

def VertexPuncturedCube :=
  {c : Cube (Fin 3) // c ≠ (fun _ => CubeCoord.free) ∧ c ≠ (fun _ => CubeCoord.pos)}

instance : PartialOrder VertexPuncturedCube where
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

def vertexPunctureRight (c : VertexPuncturedCube) := c.1 0 ≠ CubeCoord.pos

def vertexPunctureRightPole : {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg (fun _ => CubeCoord.free), by
      constructor
      · simp [coordinateFix, Function.update_self]
      · intro h
        cases (congrFun h 0)⟩, by
    change coordinateFix 0 CubeCoord.neg (fun _ : Fin 3 => CubeCoord.free) 0 ≠ CubeCoord.pos
    decide⟩

variable (c : {c : VertexPuncturedCube // vertexPunctureRight c})

def vertexPunctureRightProjection :
    {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg c.1.1, by
      constructor
      · intro h
        cases (congrFun h 0)
      · intro h
        cases (congrFun h 0)⟩, by
    change coordinateFix 0 CubeCoord.neg c.1.1 0 ≠ CubeCoord.pos
    simp [coordinateFix, Function.update_self]⟩

theorem vertexPunctureRightProjection_le :
    vertexPunctureRightProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    have hc : c.1.1 0 ≠ CubeCoord.pos := c.2
    cases he : c.1.1 0 with
    | free => exact Or.inl rfl
    | pos => simp_all
    | neg =>
      aesop
  · right
    apply Function.update_of_ne <;> assumption

theorem vertexPunctureRightProjection_le_pole :
    vertexPunctureRightProjection c ≤ vertexPunctureRightPole :=
  by solve_by_elim [coordinateFix_face_mono]

theorem vertexPunctureRightProjection_monotone : Monotone vertexPunctureRightProjection := by
  solve_by_elim [coordinateFix_face_mono]

theorem vertexPunctureRight_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  simplyConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole
    (fun h => vertexPunctureRightProjection_monotone h)

theorem vertexPunctureRight_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  isConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole

def vertexPunctureCornerEdge : Cube (Fin 3) := coordinateFix 0 CubeCoord.free (fun _ => CubeCoord.pos)

def vertexPunctureLeft (c : VertexPuncturedCube) :=
  c.1 0 ≠ CubeCoord.neg ∧ c.1 ≠ vertexPunctureCornerEdge

theorem vertexPunctureLeftProjection_ne_vertex
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    coordinateFix 0 CubeCoord.pos c.1.1 ≠ (fun _ => CubeCoord.pos) := by
  intro h
  have hrest (v : Fin 3) (hv : v ≠ 0) : c.1.1 v = CubeCoord.pos := by
    have hh := congrFun h v
    simp_all [coordinateFix, Function.update_of_ne]
  cases he : c.1.1 0 with
  | neg => apply c.2.1 <;> assumption
  | pos =>
    grind
  | free =>
    apply c.2.2
    funext v
    by_cases hv : v = 0
    · aesop
    · simp_all [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne]

def vertexPunctureLeftPole : {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos (fun _ => CubeCoord.free), by
      constructor
      · simp [coordinateFix, Function.update_self]
      · intro h
        cases (congrFun h 1)⟩, by
    constructor
    · decide
    · intro h
      cases (congrFun h 0)⟩

variable (c : {c : VertexPuncturedCube // vertexPunctureLeft c})

def vertexPunctureLeftProjection :
    {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos c.1.1, by
      constructor
      · intro h
        cases (congrFun h 0)
      · exact vertexPunctureLeftProjection_ne_vertex c⟩, by
    constructor
    · simp [coordinateFix, Function.update_self]
    · intro h
      cases (congrFun h 0)⟩

theorem vertexPunctureLeftProjection_le :
    vertexPunctureLeftProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    cases he : c.1.1 0 with
    | free => exact Or.inl rfl
    | neg => exact False.elim (c.2.1 he)
    | pos =>
      aesop
  · right
    apply Function.update_of_ne <;> assumption

theorem vertexPunctureLeftProjection_le_pole :
    vertexPunctureLeftProjection c ≤ vertexPunctureLeftPole :=
  by solve_by_elim [coordinateFix_face_mono]

theorem vertexPunctureLeftProjection_monotone : Monotone vertexPunctureLeftProjection := by
  solve_by_elim [coordinateFix_face_mono]

theorem vertexPunctureLeft_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  simplyConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole
    (fun h => vertexPunctureLeftProjection_monotone h)

theorem vertexPunctureLeft_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  isConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole

variable (c : VertexPuncturedCube)

theorem vertexPuncture_positive_mem_left
    (hc : c.1 0 = CubeCoord.pos) : vertexPunctureLeft c := by
  constructor
  · simp_all
  · intro h
    simp_all [vertexPunctureCornerEdge, coordinateFix, Function.update_self, hc]

theorem vertexPuncture_cover :
    vertexPunctureLeft c ∨ vertexPunctureRight c := by
  by_cases hc : c.1 0 = CubeCoord.pos
  · solve_by_elim [vertexPuncture_positive_mem_left]
  · exact Or.inr hc

theorem vertexPuncture_positive_not_below_edge
    (hc : c.1 0 = CubeCoord.pos) : ¬ CoordinateFace c.1 vertexPunctureCornerEdge := by
  intro h
  apply c.2.2
  funext v
  by_cases hv : v = 0
  · simp_all
  · have he : vertexPunctureCornerEdge v = CubeCoord.pos := by
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv]
    have hh := h v
    simp_all

theorem vertexPuncture_unmixed (c d : VertexPuncturedCube) (h : c ≤ d) :
    (vertexPunctureLeft c ∧ vertexPunctureLeft d) ∨
      (vertexPunctureRight c ∧ vertexPunctureRight d) := by
  cases hd : d.1 0 with
  | pos =>
    have hc : c.1 0 = CubeCoord.pos := by
      have hh := h 0
      simp_all
    grind [vertexPuncture_positive_mem_left]
  | neg =>
    have hc : c.1 0 = CubeCoord.neg := by
      have hh := h 0
      simp_all
    right
    constructor <;> change _ ≠ CubeCoord.pos <;> simp_all
  | free =>
    have hdr : vertexPunctureRight d := by
      change d.1 0 ≠ CubeCoord.pos
      simp_all
    by_cases hcr : vertexPunctureRight c
    · simp_all
    · have hc := not_ne_iff.mp hcr
      left
      refine ⟨vertexPuncture_positive_mem_left c hc, ?_⟩
      constructor
      · simp_all
      · intro he
        exact vertexPuncture_positive_not_below_edge c hc (he ▸ h)

theorem vertexPuncture_intersection_iff (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∧ vertexPunctureRight c ↔
      c.1 0 = CubeCoord.free ∧ c.1 ≠ vertexPunctureCornerEdge := by
  constructor
  · rintro ⟨⟨hn, he⟩, hp⟩
    refine ⟨?_, he⟩
    cases hc : c.1 0 with
    | free => rfl
    | pos => solve_by_elim
    | neg => simp_all
  · rintro ⟨hf, he⟩
    constructor
    · refine ⟨?_, he⟩
      simp_all
    · change c.1 0 ≠ CubeCoord.pos
      simp_all

end FiniteChains.Davis
