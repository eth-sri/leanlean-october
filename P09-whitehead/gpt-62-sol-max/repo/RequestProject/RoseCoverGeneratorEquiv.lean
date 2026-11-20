module

public import RequestProject.RoseCoverCycleCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Actual lifted midpoint vertices, with their actual generator label. -/
def roseCoverMidpoints := {p : P × α // f p.1 = Rose.mid p.2}

/-- The actual positive selected incidence leaving a lifted midpoint. -/
noncomputable def roseCoverMidpointEdge (p : roseCoverMidpoints f) :
    roseCoverGeneratorEdges f hf :=
  ⟨hf.strictEdgeLiftFrom (roseMidEdge p.val.2 true) p.val.1 p.property,
    p.val.2, hf.strictEdgeLiftFrom_projection _ _ _⟩

theorem roseCoverMidpointEdge_injective : Function.Injective (roseCoverMidpointEdge f hf) := by
  intro p q h
  have he : p.val.1 = q.val.1 := congrArg (fun e => e.val.val.1) h
  exact Subtype.ext (Prod.ext he (Rose.mid.inj (p.property.symm.trans ((congrArg f he).trans q.property))))

theorem roseCoverMidpointEdge_surjective : Function.Surjective (roseCoverMidpointEdge f hf) := by
  rintro ⟨e, i, he⟩
  have hv  :=
    congrArg (·.val.1) he
  refine ⟨⟨(e.val.1, i), hv⟩, ?_⟩
  apply Subtype.ext
  exact (hf.strictEdgeLiftFrom_unique (roseMidEdge i true) e.val.1 hv e he rfl).symm

/-- A proved equivalence between actual midpoint vertices and selected actual incidence edges. -/
noncomputable def roseCoverMidpointEdgeEquiv :
    roseCoverMidpoints f ≃ roseCoverGeneratorEdges f hf :=
  Equiv.ofBijective (roseCoverMidpointEdge f hf)
    ⟨roseCoverMidpointEdge_injective f hf, roseCoverMidpointEdge_surjective f hf⟩

end FiniteChains.PresModel
