module

public import RequestProject.PresConeLinkOrderIso

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem tCirc_strict_of_lt_relation {x y : TCirc w} (h : TCirc.lt w x y) : x < y := by
  apply lt_of_le_of_ne (show x ≤ y from Or.inr h)
  have hl := TCirc.lt_left_tag w h
  grind [TCirc.lt_right_tag]

variable (k : Fin (w j).length)

def relatorCirclePoint (s : CPos) : RelatorCircle w j :=
  ⟨TCirc.pt w j k s, rfl, k.isLt⟩

def relatorCircleNext : Fin (w j).length :=
  ⟨TCirc.csucc w j k, Nat.mod_lt _ (by have := k.isLt; omega)⟩

def relatorCircleEdge0 : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cor, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩

def relatorCircleEdge1 : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩⟩

def relatorCircleEdge2 : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdge3 : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor,
      relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdgeForget (e : StrictOrdEdge (RelatorCircle w j)) : StrictOrdEdge (TCirc w) :=
  ⟨(e.1.1.1, e.1.2.1), e.2⟩

theorem relatorCircleEdgeForget_injective : Function.Injective (relatorCircleEdgeForget w j) := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun e : StrictOrdEdge (TCirc w) => e.1.1) h
  · exact congrArg (fun e : StrictOrdEdge (TCirc w) => e.1.2) h

/-- The four explicit incidences exhaust the actual valid attaching-circle edges. -/
theorem relatorCircle_edge_cases (e : StrictOrdEdge (RelatorCircle w j)) :
    ∃ k : Fin _, e = relatorCircleEdge0 w j k ∨
      e = relatorCircleEdge1 w j k ∨ e = relatorCircleEdge2 w j k ∨
      e = relatorCircleEdge3 w j k := by
  let e' := relatorCircleEdgeForget w j e
  obtain ⟨j', k, hk, he⟩ := tCirc_strict_edge_cases w e'
  have hj' : e'.1.2.1 = j' := by
    aesop
  rw [(hj'.symm.trans e.1.2.2.1)] at hk he
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

end FiniteChains.PresModel
