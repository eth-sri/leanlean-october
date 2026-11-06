import Mathlib.Tactic

import RequestProject.CoordinateFacetContraction

/-! Coordinate regions of the proper three-cube boundary with its positive vertex removed. -/
namespace FiniteChains.Davis
open Comb

def VertexPuncturedCube :=
  {c : Cube (Fin 3) // c ≠ (fun _ => CubeCoord.free) ∧ c ≠ (fun _ => CubeCoord.pos)}

instance : PartialOrder VertexPuncturedCube :=
  @Subtype.partialOrder _ coordinateFaceOrder _

def vertexPunctureRight (c : VertexPuncturedCube)  := c.1 0 ≠ CubeCoord.pos

def vertexPunctureRightPole : {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg (fun _ => CubeCoord.free), by
      constructor
      · simp_all [coordinateFix]
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix] at hh
        cases hh⟩, by
    simp_all [FiniteChains.Davis.vertexPunctureRight, coordinateFix]⟩

variable (c : {c : VertexPuncturedCube // vertexPunctureRight c})
def vertexPunctureRightProjection  :
    {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        simp  at hh
        cases hh
      · intro h
        have hh := congrFun h 0
        simp  at hh
        cases hh⟩, by
    simp_all [FiniteChains.Davis.vertexPunctureRight, coordinateFix]⟩

theorem vertexPunctureRightProjection_le
     :
    vertexPunctureRightProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    have hc : c.1.1 0 ≠ CubeCoord.pos := c.2
    cases he : c.1.1 0 <;> simp_all [vertexPunctureRightProjection, coordinateFix]
  · right
    exact Function.update_of_ne hv _ _

theorem vertexPunctureRightProjection_le_pole
     :
    vertexPunctureRightProjection c ≤ vertexPunctureRightPole :=
  coordinateFix_face_mono 0 CubeCoord.neg (fun _ => Or.inl rfl)

theorem vertexPunctureRightProjection_monotone : Monotone vertexPunctureRightProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.neg h

abbrev vertexPunctureRight_simplyConnected  :=
  simplyConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole
    (fun h => vertexPunctureRightProjection_monotone h)

abbrev vertexPunctureRight_connected  :=
  FiniteChains.Comb.isConnected_orderCx FiniteChains.Davis.vertexPunctureRightPole
    FiniteChains.Davis.vertexPunctureRightProjection FiniteChains.Davis.vertexPunctureRightProjection_le
    FiniteChains.Davis.vertexPunctureRightProjection_le_pole

def vertexPunctureCornerEdge : Cube (Fin 3) := coordinateFix 0 CubeCoord.free (fun _ => CubeCoord.pos)

def vertexPunctureLeft (c : VertexPuncturedCube)  :=
  c.1 0 ≠ CubeCoord.neg ∧ c.1 ≠ vertexPunctureCornerEdge

variable (c : {c : VertexPuncturedCube // vertexPunctureLeft c})
theorem vertexPunctureLeftProjection_ne_vertex
     :
    coordinateFix 0 CubeCoord.pos c.1.1 ≠ (fun _ => CubeCoord.pos) := by
  intro h
  have hrest (v : Fin 3) (hv : v ≠ 0) : c.1.1 v = CubeCoord.pos := by
    have hh := congrFun h v
    simpa only [coordinateFix, Function.update_of_ne hv] using hh
  cases he : c.1.1 0 with
  | neg => exact c.2.1 he
  | pos =>
    grind
  | free =>
    apply c.2.2
    funext v
    by_cases hv : v = 0
    · aesop
    simp_all [vertexPunctureCornerEdge, coordinateFix]

def vertexPunctureLeftPole : {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos (fun _ => CubeCoord.free), by
      constructor
      · simp_all [coordinateFix]
      · intro h
        have hh := congrFun h (1 : Fin 3)
        simp only [coordinateFix] at hh
        cases hh⟩, by
    constructor
    · simp_all [coordinateFix]
    · intro h
      have hh := congrFun h 0
      simp  at hh
      cases hh⟩

def vertexPunctureLeftProjection  :
    {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        simp  at hh
        cases hh
      · exact vertexPunctureLeftProjection_ne_vertex c⟩, by
    constructor
    · simp_all [coordinateFix]
    · intro h
      have hh := congrFun h 0
      simp  at hh
      cases hh⟩

theorem vertexPunctureLeftProjection_le
     :
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
    exact Function.update_of_ne hv _ _

theorem vertexPunctureLeftProjection_le_pole
     :
    vertexPunctureLeftProjection c ≤ vertexPunctureLeftPole :=
  coordinateFix_face_mono 0 CubeCoord.pos (fun _ => Or.inl rfl)

theorem vertexPunctureLeftProjection_monotone : Monotone vertexPunctureLeftProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.pos h

abbrev vertexPunctureLeft_simplyConnected  :=
  simplyConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole
    (fun h => vertexPunctureLeftProjection_monotone h)

abbrev vertexPunctureLeft_connected  :=
  FiniteChains.Comb.isConnected_orderCx FiniteChains.Davis.vertexPunctureLeftPole
    FiniteChains.Davis.vertexPunctureLeftProjection FiniteChains.Davis.vertexPunctureLeftProjection_le
    FiniteChains.Davis.vertexPunctureLeftProjection_le_pole

theorem vertexPuncture_positive_mem_left (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : vertexPunctureLeft c := by
  aesop (add simp [FiniteChains.Davis.vertexPunctureLeft, vertexPunctureCornerEdge, coordinateFix])

theorem vertexPuncture_cover (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∨ vertexPunctureRight c := by
  by_cases hc : c.1 0 = CubeCoord.pos
  · simp_all [vertexPuncture_positive_mem_left]
  · exact Or.inr hc

theorem vertexPuncture_positive_not_below_edge (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : ¬ CoordinateFace c.1 vertexPunctureCornerEdge := by
  intro h
  apply c.2.2
  funext v
  by_cases hv : v = 0
  · subst v
    exact hc
  · have he : vertexPunctureCornerEdge v = CubeCoord.pos := by
      simp_all [vertexPunctureCornerEdge, coordinateFix]
    have hh := h v
    rw [he] at hh
    rcases hh with hh | hh
    · cases hh
    · exact hh

theorem vertexPuncture_unmixed (c d : VertexPuncturedCube) (h : c ≤ d) :
    (vertexPunctureLeft c ∧ vertexPunctureLeft d) ∨
      (vertexPunctureRight c ∧ vertexPunctureRight d) := by
  cases hd : d.1 0 with
  | pos =>
    have hc : c.1 0 = CubeCoord.pos := by
      have hh := h 0
      rw [hd] at hh
      rcases hh with hh | hh
      · cases hh
      · exact hh
    simp_all [vertexPuncture_positive_mem_left]
  | neg =>
    have hc : c.1 0 = CubeCoord.neg := by
      have hh := h 0
      rw [hd] at hh
      rcases hh with hh | hh
      · cases hh
      · exact hh
    right
    constructor <;> change _ ≠ CubeCoord.pos
    · rw [hc]
      decide
    · rw [hd]
      decide
  | free =>
    have hdr : vertexPunctureRight d := by
      change d.1 0 ≠ CubeCoord.pos
      rw [hd]
      decide
    by_cases hcr : vertexPunctureRight c
    · exact Or.inr ⟨hcr, hdr⟩
    · have hc  := not_ne_iff.mp hcr
      left
      refine ⟨vertexPuncture_positive_mem_left c hc, ?_⟩
      constructor
      · rw [hd]
        decide
      · intro he
        exact vertexPuncture_positive_not_below_edge c hc (he ▸ h)

theorem vertexPuncture_intersection_iff (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∧ vertexPunctureRight c ↔
      c.1 0 = CubeCoord.free ∧ c.1 ≠ vertexPunctureCornerEdge := by
  constructor
  · rintro ⟨⟨hn, he⟩, hp⟩
    refine ⟨?_, he⟩
    cases hc : c.1 0 <;> aesop
  · rintro ⟨hf, he⟩
    constructor
    · refine ⟨?_, he⟩
      rw [hf]
      decide
    · change c.1 0 ≠ CubeCoord.pos
      rw [hf]
      decide

end FiniteChains.Davis
