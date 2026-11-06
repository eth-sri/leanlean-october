import RequestProject.PresConeLinkOrderIso


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem tCirc_strict_of_lt_relation (h : TCirc.lt w x y) : x < y := by
  apply lt_of_le_of_ne (by tauto)
  intro he
  have hl := TCirc.lt_left_tag w h
  have hr := TCirc.lt_right_tag w h
  grind

def relatorCirclePoint (k : Fin (w j).length) (s : CPos) : RelatorCircle w j :=
  ⟨TCirc.pt w j k s, rfl, k.isLt⟩

def relatorCircleNext (k : Fin (w j).length) : Fin (w j).length :=
  ⟨TCirc.csucc w j k, Nat.mod_lt _ (by have := k.isLt; omega)⟩

def relatorCircleEdge0 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cor, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, by aesop⟩⟩

def relatorCircleEdge1 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, by aesop⟩⟩

def relatorCircleEdge2 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, by aesop⟩⟩

def relatorCircleEdge3 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor,
      relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, by aesop⟩⟩

def relatorCircleEdgeForget (e : StrictOrdEdge (RelatorCircle w j)) : StrictOrdEdge (TCirc w) :=
  ⟨(e.1.1.1, e.1.2.1), e.2⟩

theorem relatorCircleEdgeForget_injective : Function.Injective (relatorCircleEdgeForget w j) := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (·.1.1) h
  · exact congrArg (·.1.2) h

/-- The four explicit incidences exhaust the actual valid attaching-circle edges. -/
theorem relatorCircle_edge_cases e :
    ∃ k, e = relatorCircleEdge0 w j k ∨
      e = relatorCircleEdge1 w j k ∨ e = relatorCircleEdge2 w j k ∨
      e = relatorCircleEdge3 w j k := by
  let e' := relatorCircleEdgeForget w j e
  obtain ⟨j', k, hk, he⟩ := tCirc_strict_edge_cases w e'
  have hj' : e'.1.2.1 = j' := by
    aesop
  have hj := hj'.symm.trans e.1.2.2.1
  rw [hj] at hk he
  refine ⟨⟨k, hk⟩, ?_⟩
  rcases he with he | he | he | he
  · left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; right; left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; right; right
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
