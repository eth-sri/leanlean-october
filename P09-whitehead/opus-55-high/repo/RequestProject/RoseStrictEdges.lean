import RequestProject.PresPosetPartialOrder
import RequestProject.StrictOrderComplex


namespace FiniteChains.PresModel
open Comb
variable {α : Type u}

def roseBaseEdge (i : α) (b : Bool) : StrictOrdEdge (Rose α) :=
  ⟨(Rose.base, Rose.edg i b), by tauto⟩

def roseMidEdge (i : α) (b : Bool) : StrictOrdEdge (Rose α) :=
  ⟨(Rose.mid i, Rose.edg i b), by tauto⟩

/-- The actual strict rose edges are exactly the two half-incidences for each generator end. -/
theorem rose_strict_edge_cases (e : StrictOrdEdge (Rose α)) :
    ∃ i b, e = roseBaseEdge i b ∨ e = roseMidEdge i b := by
  rcases e with ⟨⟨a, b⟩, h⟩
  have hl := h.le
  have hn := h.ne
  cases a with
  | base =>
    cases b with
    | base => simp_all
    | mid i => exact hl.elim
    | edg i b => tauto
  | mid i =>
    cases b with
    | base => exact hl.elim
    | mid k =>
      change i = k at hl
      simp_all
    | edg k b =>
      subst k
      exact ⟨i, b, Or.inr (Subtype.ext rfl)⟩
  | edg i s =>
    cases b with
    | base => exact hl.elim
    | mid k => exact hl.elim
    | edg k c =>
      change i = k ∧ s = c at hl
      simp_all
