import RequestProject.PosetCoverStrictEdgeLift
import RequestProject.RoseStrictEdges


namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Exactly the two actual lifted incidences enter each actual rose edge-end vertex. -/
theorem roseCover_incoming_edge_cases q i b (hq : f q = Rose.edg i b)
    e (ht : e.1.2 = q) :
    e = hf.strictEdgeLiftTo (roseBaseEdge i b) q hq ∨
      e = hf.strictEdgeLiftTo (roseMidEdge i b) q hq := by
  obtain ⟨k, s, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he
  · have hp :=
      (congrArg (·.1.2) he).symm.trans
        ((congrArg f ht).trans hq)
    cases' Rose.edg.inj hp with hk hs
    subst k
    subst s
    exact Or.inl (hf.strictEdgeLiftTo_unique _ q hq e he ht)
  · have hp :=
      (congrArg (·.1.2) he).symm.trans
        ((congrArg f ht).trans hq)
    cases' Rose.edg.inj hp with hk hs
    subst k
    subst s
    exact Or.inr (hf.strictEdgeLiftTo_unique _ q hq e he ht)

/-- Exactly the two actual lifted midpoint incidences leave an actual midpoint vertex. -/
theorem roseCover_mid_outgoing_edge_cases v i (hv : f v = Rose.mid i)
    e (hs : e.1.1 = v) :
    e = hf.strictEdgeLiftFrom (roseMidEdge i false) v hv ∨
      e = hf.strictEdgeLiftFrom (roseMidEdge i true) v hv := by
  obtain ⟨k, b, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he
  · have hp :=
      (congrArg (·.1.1) he).symm.trans
        ((congrArg f hs).trans hv)
    cases hp
  · have hp :=
      (congrArg (·.1.1) he).symm.trans
        ((congrArg f hs).trans hv)
    have hk := Rose.mid.inj hp
    subst k
    have hl := hf.strictEdgeLiftFrom_unique _ v hv e he hs
    cases b
    · exact Or.inl hl
    simp_all

include hf in
/-- No actual strict edge enters a lifted rose midpoint. -/
theorem roseCover_mid_no_incoming (v : P) (i : α) (hv : f v = Rose.mid i)
    (e : StrictOrdEdge P) : e.1.2 ≠ v := by
  intro ht
  obtain ⟨k, b, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he <;>
    have hp := (congrArg (·.1.2) he).symm.trans
      ((congrArg f ht).trans hv) <;> cases hp

include hf in
/-- No actual strict edge leaves a lifted rose edge-end. -/
theorem roseCover_end_no_outgoing (q : P) (i : α) (b : Bool)
    (hq : f q = Rose.edg i b) (e : StrictOrdEdge P) : e.1.1 ≠ q := by
  intro hs
  obtain ⟨k, s, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he <;>
    have hp := (congrArg (·.1.1) he).symm.trans
      ((congrArg f hs).trans hq) <;> cases hp
