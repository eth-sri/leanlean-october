module

public import RequestProject.RoseCoverIncidences
public import RequestProject.CellularBoundaryCoefficients

@[expose] public section

set_option backward.isDefEq.respectTransparency false

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
  refine bdry1_pair_source (X := strictOrderCx P) ?_ (fun e => ⟨
    roseCover_mid_outgoing_edge_cases f hf v i hv e, by rintro (rfl | rfl) <;> rfl⟩)
    (roseCover_mid_no_incoming f hf v i hv) c
  intro h
  have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
  simp only [hf.strictEdgeLiftFrom_projection] at hp
  cases congrArg (·.1.2) hp

/-- The edge-end boundary equation for the actual finite chain complex of a rose cover. -/
theorem roseCover_boundary_end (q : P) (i : α) (b : Bool) (hq : f q = Rose.edg i b)
    (c : StrictOrdEdge P →₀ ℤ) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) c q =
      c (hf.strictEdgeLiftTo (roseBaseEdge i b) q hq) +
        c (hf.strictEdgeLiftTo (roseMidEdge i b) q hq) := by
  refine bdry1_pair_target (X := strictOrderCx P) ?_ (fun e => ⟨
    roseCover_incoming_edge_cases f hf q i b hq e, by rintro (rfl | rfl) <;> rfl⟩)
    (roseCover_end_no_outgoing f hf q i b hq) c
  intro h
  have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
  simp only [hf.strictEdgeLiftTo_projection] at hp
  cases congrArg (·.1.1) hp

end FiniteChains.PresModel
