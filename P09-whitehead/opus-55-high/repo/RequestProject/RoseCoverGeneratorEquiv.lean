import RequestProject.RoseCoverCycleCoordinates
noncomputable section


set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Actual lifted midpoint vertices, with their actual generator label. -/
def roseCoverMidpoints := {p : P × α // f p.1 = Rose.mid p.2}

/-- The actual positive selected incidence leaving a lifted midpoint. -/
def roseCoverMidpointEdge (p : roseCoverMidpoints f) :
    roseCoverGeneratorEdges f hf :=
  ⟨hf.strictEdgeLiftFrom (roseMidEdge p.val.2 true) p.val.1 p.property,
    p.val.2, hf.strictEdgeLiftFrom_projection _ _ _⟩

theorem roseCoverMidpointEdge_injective : Function.Injective (roseCoverMidpointEdge f hf) := by
  intro p q h
  have he := congrArg Subtype.val h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (·.val.1) he
  · have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) he
    change (strictOrderCxMap f hf.strictMono).onE
      (hf.strictEdgeLiftFrom (roseMidEdge p.val.2 true) p.val.1 p.property) =
      (strictOrderCxMap f hf.strictMono).onE
        (hf.strictEdgeLiftFrom (roseMidEdge q.val.2 true) q.val.1 q.property) at hp
    rw [hf.strictEdgeLiftFrom_projection, hf.strictEdgeLiftFrom_projection] at hp
    exact Rose.mid.inj (congrArg (·.val.1) hp)

theorem roseCoverMidpointEdge_surjective : Function.Surjective (roseCoverMidpointEdge f hf) := by
  rintro ⟨e, i, he⟩
  have hv :=
    congrArg (·.val.1) he
  refine ⟨⟨(e.val.1, i), hv⟩, ?_⟩
  apply Subtype.ext
  exact (hf.strictEdgeLiftFrom_unique _ e.val.1 hv e he rfl).symm

/-- A proved equivalence between actual midpoint vertices and selected actual incidence edges. -/
def roseCoverMidpointEdgeEquiv :=
  Equiv.ofBijective _
    ⟨roseCoverMidpointEdge_injective f hf, roseCoverMidpointEdge_surjective f hf⟩
