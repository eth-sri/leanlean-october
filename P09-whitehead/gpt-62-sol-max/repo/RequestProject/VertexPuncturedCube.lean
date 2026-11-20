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
    · aesop
    · rcases hcd v with hd | hd
      · simp_all
      · simp_all
  le_antisymm c d hcd hdc := by
    apply Subtype.ext
    funext v
    rcases hcd v with hd | hd
    · rcases hdc v with hc | hc
      · exact hc.trans hd.symm
      · exact hc.symm
    · exact hd

def vertexPunctureRight (c : VertexPuncturedCube) : Prop := c.1 0 ≠ CubeCoord.pos

def vertexPunctureRightPole : {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg (fun _ => CubeCoord.free), by
      trivial⟩, by
    change coordinateFix 0 CubeCoord.neg (fun _  => CubeCoord.free) 0 ≠ CubeCoord.pos
    decide⟩

def vertexPunctureRightProjection (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        trivial
      · intro h
        have hh := congrFun h 0
        trivial⟩, by
    change coordinateFix 0 CubeCoord.neg c.1.1 0 ≠ CubeCoord.pos
    tauto⟩

theorem vertexPunctureRightProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    have hc  := c.2
    cases he : c.1.1 0 with
    | free => aesop
    | pos => tauto
    | neg =>
      tauto
  · right
    exact Function.update_of_ne hv _ _

theorem vertexPunctureRightProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ vertexPunctureRightPole :=
  coordinateFix_face_mono 0 CubeCoord.neg (fun _ => Or.inl rfl)

theorem vertexPunctureRightProjection_monotone : Monotone vertexPunctureRightProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.neg h

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

def vertexPunctureLeft (c : VertexPuncturedCube) : Prop :=
  c.1 0 ≠ CubeCoord.neg ∧ c.1 ≠ vertexPunctureCornerEdge

theorem vertexPunctureLeftProjection_ne_vertex
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    coordinateFix 0 CubeCoord.pos c.1.1 ≠ (fun _ => CubeCoord.pos) := by
  intro h
  have hrest (v : Fin 3) (hv : v ≠ 0) : c.1.1 v = CubeCoord.pos := by
    have hh := congrFun h v
    simpa only [coordinateFix, Function.update_of_ne hv] using hh
  cases he : c.1.1 0 with
  | neg => exact c.2.1 he
  | pos =>
    apply c.1.2.2
    funext v
    by_cases hv : v = 0
    · subst v
      exact he
    · exact hrest v hv
  | free =>
    apply c.2.2
    funext v
    by_cases hv : v = 0
    · subst v
      assumption
    · simpa only [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv] using hrest v hv

def vertexPunctureLeftPole : {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos (fun _ => CubeCoord.free), by
      trivial⟩, by
    constructor
    · change coordinateFix 0 CubeCoord.pos (fun _  => CubeCoord.free) 0 ≠ CubeCoord.neg
      decide
    · intro h
      have hh := congrFun h 0
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] at hh
      cases hh⟩

def vertexPunctureLeftProjection (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        trivial
      · exact vertexPunctureLeftProjection_ne_vertex c⟩, by
    constructor
    · change coordinateFix 0 CubeCoord.pos c.1.1 0 ≠ CubeCoord.neg
      tauto
    · intro h
      have hh := congrFun h 0
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] at hh
      cases hh⟩

theorem vertexPunctureLeftProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    cases he : c.1.1 0 with
    | free => aesop
    | neg => exact False.elim (c.2.1 he)
    | pos =>
      tauto
  · right
    exact Function.update_of_ne hv _ _

theorem vertexPunctureLeftProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ vertexPunctureLeftPole :=
  coordinateFix_face_mono 0 CubeCoord.pos (fun _ => Or.inl rfl)

theorem vertexPunctureLeftProjection_monotone : Monotone vertexPunctureLeftProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.pos h

theorem vertexPunctureLeft_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  simplyConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole
    (fun h => vertexPunctureLeftProjection_monotone h)

theorem vertexPunctureLeft_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  isConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole

theorem vertexPuncture_positive_mem_left (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : vertexPunctureLeft c := by
  constructor
  · simp_all
  · intro h
    simp_all [vertexPunctureCornerEdge, coordinateFix, Function.update_self]

theorem vertexPuncture_cover (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∨ vertexPunctureRight c := by
  by_cases hc : c.1 0 = CubeCoord.pos
  · exact Or.inl (vertexPuncture_positive_mem_left c hc)
  · aesop

theorem vertexPuncture_positive_not_below_edge (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : ¬ CoordinateFace c.1 vertexPunctureCornerEdge := by
  intro h
  apply c.2.2
  funext v
  by_cases hv : v = 0
  · simp_all
  · have he : vertexPunctureCornerEdge v = CubeCoord.pos := by
      simp [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv]
    have hh := h v
    aesop

theorem vertexPuncture_unmixed (c d : VertexPuncturedCube) (h : c ≤ d) :
    (vertexPunctureLeft c ∧ vertexPunctureLeft d) ∨
      (vertexPunctureRight c ∧ vertexPunctureRight d) := by
  cases hd : d.1 0 with
  | pos =>
    have hc : c.1 0 = CubeCoord.pos := by
      have hh := h 0
      aesop
    exact Or.inl ⟨vertexPuncture_positive_mem_left c hc, vertexPuncture_positive_mem_left d hd⟩
  | neg =>
    have hc : c.1 0 = CubeCoord.neg := by
      have hh := h 0
      aesop
    right
    constructor <;> change _ ≠ CubeCoord.pos
    · simp_all
    · simp_all
  | free =>
    have hdr : vertexPunctureRight d := by
      change d.1 0 ≠ CubeCoord.pos
      simp_all
    by_cases hcr : vertexPunctureRight c
    · tauto
    · have hc  := not_ne_iff.mp hcr
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
    | pos => tauto
    | neg => tauto
  · rintro ⟨hf, he⟩
    constructor
    · refine ⟨?_, he⟩
      simp_all
    · change c.1 0 ≠ CubeCoord.pos
      simp_all

end FiniteChains.Davis
