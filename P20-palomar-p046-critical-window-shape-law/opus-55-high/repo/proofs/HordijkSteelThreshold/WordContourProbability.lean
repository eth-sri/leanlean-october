module

public import proofs.HordijkSteelThreshold.WordDetourSelection
public import proofs.HordijkSteelThreshold.DisjointDetourProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

/-- All w detours for every edge of the fixed contour fail. -/
def contourDetoursFailed {L N w : ℕ} {Ω : Type*} (hL : 2*w ≤ L)
    (C : Finset $ WordBasicEdge L N) (field : Reaction N → Ω → Prop) (ω : Ω) : Prop :=
  ∀ d ∈ wordContourDetours w C, detourFailed field (wordDetourSourceReactions hL d) ω

variable (N : ℕ) (a : I)

/-- The literal iid static reaction field; distinct split-position IDs are coordinates. -/
noncomputable def staticReactionMeasure  : Measure (Reaction N → Prop) :=
  Measure.pi $ fun _ => ambientCoordLaw a

noncomputable instance staticReactionMeasure_probability  :
    IsProbabilityMeasure (staticReactionMeasure N a) := by
  unfold staticReactionMeasure
  infer_instance

end HordijkSteelThreshold
