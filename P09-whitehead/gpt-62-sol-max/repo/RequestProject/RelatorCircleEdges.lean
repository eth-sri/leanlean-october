module

public import RequestProject.PresConeLinkOrderIso

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem tCirc_strict_of_lt_relation {x y : TCirc w} (h : TCirc.lt w x y) : x < y := by
  apply lt_of_le_of_ne (Or.inr h)
  intro he
  have hl := TCirc.lt_left_tag w h
  have hr := TCirc.lt_right_tag w h
  grind

def relatorCirclePoint (k : Fin (w j).length) (s : CPos) : RelatorCircle w j :=
  ⟨TCirc.pt w j k s, rfl, k.isLt⟩

def relatorCircleNext (k : Fin (w j).length) : Fin (w j).length :=
  ⟨TCirc.csucc w j k, Nat.mod_lt _ (by have := k.isLt; omega)⟩

/-- Successor acts cyclically on the positions of a relator word. -/
theorem relatorCircleNext_injective : Function.Injective (relatorCircleNext w j) := by
  intro k l h
  letI := NeZero.of_pos k.pos
  apply add_right_cancel (b := (1 : Fin (w j).length))
  apply Fin.ext
  simp_all [Fin.val_add, Nat.add_mod_mod, relatorCircleNext, TCirc.csucc]

theorem relatorCircle_successor_invariant_constant {B : Type*}
    (a : Fin (w j).length → B)
    (ha : ∀ k, a (relatorCircleNext w j k) = a k)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    a k = a ⟨0, hpos⟩ := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < (w j).length := by omega
    have hnext : relatorCircleNext w j ⟨n, hlt⟩ = ⟨n + 1, hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)
    exact (hnext ▸ ha ⟨n, hlt⟩).trans (ih hlt)

def relatorCircleEdge0 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cor, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩

def relatorCircleEdge1 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩⟩

def relatorCircleEdge2 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdge3 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor,
      relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdgeForget (e : StrictOrdEdge (RelatorCircle w j)) : StrictOrdEdge (TCirc w) :=
  ⟨(e.1.1.1, e.1.2.1), e.2⟩

theorem relatorCircleEdgeForget_injective : Function.Injective (relatorCircleEdgeForget w j) := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (·.1.1) h
  · exact congrArg (·.1.2) h

/-- The four explicit incidences exhaust the actual valid attaching-circle edges. -/
theorem relatorCircle_edge_cases (e : StrictOrdEdge (RelatorCircle w j)) :
    ∃ k : Fin (w j).length, e = relatorCircleEdge0 w j k ∨
      e = relatorCircleEdge1 w j k ∨ e = relatorCircleEdge2 w j k ∨
      e = relatorCircleEdge3 w j k := by
  let e' := relatorCircleEdgeForget w j e
  obtain ⟨j', k, hk, he⟩ := tCirc_strict_edge_cases w e'
  have hj' : e'.1.2.1 = j' := by
    rcases he with he | he | he | he <;> rw [he] <;> rfl
  have hj  := hj'.symm.trans e.1.2.2.1
  rw [hj] at hk he
  refine ⟨⟨k, hk⟩, ?_⟩
  rcases he with he | he | he | he
  · exact Or.inl (relatorCircleEdgeForget_injective w j (Subtype.ext he))
  · exact Or.inr (Or.inl (relatorCircleEdgeForget_injective w j (Subtype.ext he)))
  · exact Or.inr (Or.inr (Or.inl (relatorCircleEdgeForget_injective w j (Subtype.ext he))))
  · exact Or.inr (Or.inr (Or.inr (relatorCircleEdgeForget_injective w j (Subtype.ext he))))

end FiniteChains.PresModel
