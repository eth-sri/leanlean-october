module

public import RequestProject.CoordinateFacetContraction

@[expose] public section

namespace FiniteChains.Davis
open Comb

def VertexPuncturedCube :=
  {c : Cube (Fin 3) // c ≠ (fun _ => CubeCoord.free) ∧ c ≠ (fun _ => CubeCoord.pos)}

instance : PartialOrder VertexPuncturedCube where
  le c d := CoordinateFace c.1 d.1
  le_refl _ _ := .inr rfl
  le_trans _ _ _ hcd hde v :=
    (hde v).elim .inl fun he => (hcd v).imp (he.symm.trans ·) (·.trans he)
  le_antisymm _ _ hcd hdc := Subtype.ext <| funext fun v =>
    (hcd v).elim (fun hd => (hdc v).elim (·.trans hd.symm) (·.symm)) id

def vertexPunctureRight (c : VertexPuncturedCube) : Prop := c.1 0 ≠ CubeCoord.pos

def vertexPunctureRightPole : {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg (fun _ => CubeCoord.free),
    fun h => by have := congrFun h 0; simp [coordinateFix] at this,
    fun h => by have := congrFun h 0; simp [coordinateFix] at this⟩, by
    change coordinateFix 0 CubeCoord.neg (fun _ : Fin 3 => CubeCoord.free) 0 ≠ CubeCoord.pos
    simp [coordinateFix]⟩

def vertexPunctureRightProjection (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg c.1.1,
    fun h => by have := congrFun h 0; simp [coordinateFix] at this,
    fun h => by have := congrFun h 0; simp [coordinateFix] at this⟩, by
    change coordinateFix 0 CubeCoord.neg c.1.1 0 ≠ CubeCoord.pos
    simp [coordinateFix]⟩

theorem vertexPunctureRightProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ c := fun v => by
  by_cases hv : v = 0
  · subst v
    cases he : c.1.1 0 with
    | free => exact .inl rfl
    | pos => exact (c.2 he).elim
    | neg => exact .inr (by simp [vertexPunctureRightProjection, coordinateFix])
  · exact .inr (Function.update_of_ne hv _ _)

theorem vertexPunctureRightProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ vertexPunctureRightPole :=
  coordinateFix_face_mono 0 CubeCoord.neg fun _ => .inl rfl

theorem vertexPunctureRightProjection_monotone : Monotone vertexPunctureRightProjection :=
  fun _ _ h => coordinateFix_face_mono 0 CubeCoord.neg h

theorem vertexPunctureRight_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  simplyConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole
    fun h => vertexPunctureRightProjection_monotone h

theorem vertexPunctureRight_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  isConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole

def vertexPunctureCornerEdge : Cube (Fin 3) := coordinateFix 0 CubeCoord.free (fun _ => CubeCoord.pos)

def vertexPunctureLeft (c : VertexPuncturedCube) : Prop :=
  c.1 0 ≠ CubeCoord.neg ∧ c.1 ≠ vertexPunctureCornerEdge

def vertexPunctureLeftPole : {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos (fun _ => CubeCoord.free),
    fun h => by have := congrFun h 0; simp [coordinateFix] at this,
    fun h => by
      have hh := congrFun h (1 : Fin 3)
      simp only [coordinateFix, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)] at hh
      cases hh⟩,
    by change coordinateFix 0 CubeCoord.pos (fun _ : Fin 3 => CubeCoord.free) 0 ≠ CubeCoord.neg; simp [coordinateFix],
    fun h => by have := congrFun h 0; simp [vertexPunctureCornerEdge, coordinateFix] at this⟩

def vertexPunctureLeftProjection (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos c.1.1,
    fun h => by have := congrFun h 0; simp [coordinateFix] at this,
    fun h => by
      have hrest (v : Fin 3) (hv : v ≠ 0) : c.1.1 v = CubeCoord.pos := by
        simpa only [coordinateFix, Function.update_of_ne hv] using congrFun h v
      cases he : c.1.1 0 with
      | neg => exact c.2.1 he
      | pos => exact c.1.2.2 (funext fun v => if hv : v = 0 then hv ▸ he else hrest v hv)
      | free => exact c.2.2 (funext fun v => by
          by_cases hv : v = 0
          · subst v; simpa [vertexPunctureCornerEdge, coordinateFix] using he
          · simpa [vertexPunctureCornerEdge, coordinateFix, hv] using hrest v hv)⟩,
    by change coordinateFix 0 CubeCoord.pos c.1.1 0 ≠ CubeCoord.neg; simp [coordinateFix],
    fun h => by have := congrFun h 0; simp [vertexPunctureCornerEdge, coordinateFix] at this⟩

theorem vertexPunctureLeftProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ c := fun v => by
  by_cases hv : v = 0
  · subst v
    cases he : c.1.1 0 with
    | free => exact .inl rfl
    | neg => exact (c.2.1 he).elim
    | pos => exact .inr (by simp [vertexPunctureLeftProjection, coordinateFix])
  · exact .inr (Function.update_of_ne hv _ _)

theorem vertexPunctureLeftProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ vertexPunctureLeftPole :=
  coordinateFix_face_mono 0 CubeCoord.pos fun _ => .inl rfl

theorem vertexPunctureLeftProjection_monotone : Monotone vertexPunctureLeftProjection :=
  fun _ _ h => coordinateFix_face_mono 0 CubeCoord.pos h

theorem vertexPunctureLeft_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  simplyConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole
    fun h => vertexPunctureLeftProjection_monotone h

theorem vertexPunctureLeft_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  isConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole

theorem vertexPuncture_positive_mem_left (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : vertexPunctureLeft c :=
  ⟨by rw [hc]; decide, fun h => by
    have := congrFun h 0; simp [vertexPunctureCornerEdge, coordinateFix, hc] at this⟩

theorem vertexPuncture_cover (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∨ vertexPunctureRight c :=
  if hc : c.1 0 = CubeCoord.pos then .inl (vertexPuncture_positive_mem_left c hc) else .inr hc

theorem vertexPuncture_unmixed (c d : VertexPuncturedCube) (h : c ≤ d) :
    (vertexPunctureLeft c ∧ vertexPunctureLeft d) ∨
      (vertexPunctureRight c ∧ vertexPunctureRight d) := by
  cases hd : d.1 0 with
  | pos =>
    have hc : c.1 0 = CubeCoord.pos := by
      have hh := h 0; rw [hd] at hh; rcases hh with hh | hh <;> [cases hh; exact hh]
    exact .inl ⟨vertexPuncture_positive_mem_left c hc, vertexPuncture_positive_mem_left d hd⟩
  | neg =>
    have hc : c.1 0 = CubeCoord.neg := by
      have hh := h 0; rw [hd] at hh; rcases hh with hh | hh <;> [cases hh; exact hh]
    exact .inr ⟨by change c.1 0 ≠ _; rw [hc]; decide, by change d.1 0 ≠ _; rw [hd]; decide⟩
  | free =>
    have hdr : vertexPunctureRight d := by change d.1 0 ≠ _; rw [hd]; decide
    by_cases hcr : vertexPunctureRight c
    · exact .inr ⟨hcr, hdr⟩
    · have hc : c.1 0 = CubeCoord.pos := not_ne_iff.mp hcr
      refine .inl ⟨vertexPuncture_positive_mem_left c hc, by rw [hd]; decide, fun he => c.2.2 ?_⟩
      funext v
      by_cases hv : v = 0
      · subst v; exact hc
      · have hh := h v; rw [he] at hh
        simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv] at hh
        rcases hh with hh | hh <;> [cases hh; exact hh]

theorem vertexPuncture_intersection_iff (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∧ vertexPunctureRight c ↔
      c.1 0 = CubeCoord.free ∧ c.1 ≠ vertexPunctureCornerEdge :=
  ⟨fun ⟨⟨hn, he⟩, hp⟩ => ⟨by
      cases hc : c.1 0 with
      | free => rfl
      | pos => exact (hp hc).elim
      | neg => exact (hn hc).elim, he⟩,
   fun ⟨hf, he⟩ => ⟨⟨by rw [hf]; decide, he⟩, by change c.1 0 ≠ _; rw [hf]; decide⟩⟩

end FiniteChains.Davis
