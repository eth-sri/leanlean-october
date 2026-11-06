module

public import RequestProject.Oriented

public import RequestProject.RoseCoverIncidences

@[expose] public section

backwardOptions




namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- The midpoint boundary equation for the actual finite chain complex of a rose cover. -/
theorem roseCover_boundary_mid (v : P) (i : α) (hv : f v = Rose.mid i)
    (c : StrictOrdEdge P →₀ ℤ) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) c v =
      -c (hf.strictEdgeLiftFrom (roseMidEdge i false) v hv) -
        c (hf.strictEdgeLiftFrom (roseMidEdge i true) v hv) := by
  classical
  let l := hf.strictEdgeLiftFrom (roseMidEdge i false) v hv
  let r := hf.strictEdgeLiftFrom (roseMidEdge i true) v hv
  have hl : l.1.1 = v := rfl
  have hr : r.1.1 = v := rfl
  have hne : l ≠ r := by
    intro h
    have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
    rw [hf.strictEdgeLiftFrom_projection, hf.strictEdgeLiftFrom_projection] at hp
    have hb := congrArg (fun e : StrictOrdEdge (Rose α) => e.1.2) hp
    cases hb
  change FiniteChains.Comb.bdry1 (strictOrderCx P) c v = -c l - c r
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    rw [bdry1_single (X := strictOrderCx P)]
    have ht := roseCover_mid_no_incoming f hf v i hv e
    by_cases he : e = l
    · subst e
      simp [strictOrderCx, ht, hl, hne.symm]
    · by_cases her : e = r
      · subst e
        simp [strictOrderCx, ht, hr, hne]
      · have hs : e.1.1 ≠ v := by
          intro h
          exact (roseCover_mid_outgoing_edge_cases f hf v i hv e h).elim he her
        simp [strictOrderCx, ht, hs, he, her]

/-- The edge-end boundary equation for the actual finite chain complex of a rose cover. -/
theorem roseCover_boundary_end (q : P) (i : α) (b : Bool) (hq : f q = Rose.edg i b)
    (c : StrictOrdEdge P →₀ ℤ) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) c q =
      c (hf.strictEdgeLiftTo (roseBaseEdge i b) q hq) +
        c (hf.strictEdgeLiftTo (roseMidEdge i b) q hq) := by
  classical
  let l := hf.strictEdgeLiftTo (roseBaseEdge i b) q hq
  let r := hf.strictEdgeLiftTo (roseMidEdge i b) q hq
  have hl : l.1.2 = q := rfl
  have hr : r.1.2 = q := rfl
  have hne : l ≠ r := by
    intro h
    have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
    rw [hf.strictEdgeLiftTo_projection, hf.strictEdgeLiftTo_projection] at hp
    have hb := congrArg (fun e : StrictOrdEdge (Rose α) => e.1.1) hp
    cases hb
  change FiniteChains.Comb.bdry1 (strictOrderCx P) c q = c l + c r
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    rw [bdry1_single (X := strictOrderCx P)]
    have hs := roseCover_end_no_outgoing f hf q i b hq e
    by_cases he : e = l
    · subst e
      simp [strictOrderCx, hs, hl, hne.symm]
    · by_cases her : e = r
      · subst e
        simp [strictOrderCx, hs, hr, hne]
      · have ht : e.1.2 ≠ q := by
          intro h
          exact (roseCover_incoming_edge_cases f hf q i b hq e h).elim he her
        simp [strictOrderCx, ht, hs, he, her]

end FiniteChains.PresModel
