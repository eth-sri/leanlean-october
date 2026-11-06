module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.LoopPhaseCrossings

/-! U at least r gives r distinct bottom-to-top clusters in the exact
seam-closed cylinder (`hUr_proved`). Positive loop phases retain every winding multiplicity. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC TorusLoops
variable {N M : ℕ}
noncomputable section

section

variable (hN : Even N) (hM : Even M) (hMp : 0 < M)
include hN hM hMp

/-- Every positive loop-phase slot supplies a distinct cylinder crossing
component. There are exactly U slots. -/
theorem exists_crossing_family_indexed_by_vertical_phases
     (A : RCConfig N M) :
    ∃ x : VerticalPhaseIndex hN hM ⟨0,hMp⟩ A → FaceVertex N M true,
      (∀ s, (x s).val.2.val=0 ∧ cylinderReachesTop hN hM A (x s)) ∧
      Function.Injective  fun s =>
        (diamondOpenGraph hN hM true (torusRCSeamClosed A)).connectedComponentMk (x s)  := by
  
  
  have hex (q :  positiveVerticalLoops hN hM ⟨0,hMp⟩ A ) := cylinder_crossings_of_positive_vertical_loop hN hM hMp ⟨0,hMp⟩ A q.val
    (Finset.mem_filter.1 q.property).2
  choose x hx using hex
  let X (s : VerticalPhaseIndex hN hM ⟨0,hMp⟩ A) := x s.1 s.2
  refine ⟨X,fun s => ⟨((hx s.1).1 s.2).1,((hx s.1).1 s.2).2.2⟩,?_⟩
  rintro ⟨q,i⟩ ⟨r,k⟩ he
  have hr  :=
    SimpleGraph.ConnectedComponent.eq.1 he
  
  have hqr  := positive_vertical_loops_primalCluster_injective hN hM ⟨0,hMp⟩ A
    (((hx q).1 i).2.1.symm.trans ((SimpleGraph.ConnectedComponent.sound (hr.mono (seamClosed_graph_le hN hM A))).trans ((hx r).1 k).2.1))
  subst r
  grind

/-- `U ≥ r` gives `r` distinct bottom-to-top clusters, on the exact cylinder event
`TorusRC.torusRCSeamClosedCylinderCrossings`. Only seam edges are closed; no additional
finite-energy modification or endpoint placement is assumed. -/
theorem seamClosedCylinderCrossings_of_le_U
     (r : ℕ) (A : RCConfig N M)
    (hr : r ≤ rcVerticalWinding hN hM ⟨0,hMp⟩ A) :
    torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A) := by
  
  obtain ⟨x,hx,hinj⟩ := exists_crossing_family_indexed_by_vertical_phases hN hM hMp A
  obtain ⟨e⟩ : Nonempty (Fin r ↪ VerticalPhaseIndex hN hM ⟨0,hMp⟩ A) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin,card_verticalPhaseIndex]; exact hr)
  refine ⟨fun i => x (e i),fun i => (hx (e i)).1,?_,?_⟩
  · intro i
    exact (hx (e i)).2
  · intro i j hij hreach
    exact hij (e.injective (hinj (SimpleGraph.ConnectedComponent.sound hreach)))

/-- The exact quantitative topology contract `TorusRC.hUr` is discharged for every r. -/
theorem hUr_proved  (r : ℕ) :
    hUr hN hM hMp r :=
  fun A hr => seamClosedCylinderCrossings_of_le_U hN hM hMp r A hr

end

end
end PottsDiscontinuity.TorusTopology
