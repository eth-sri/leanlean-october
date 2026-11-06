module

public import NearlyMinimax.HighUnionSource
public import NearlyMinimax.HighFrameEvaluation

@[expose] public section

/-! Actual original-model legality of complete-row canonical raw histories.
The density is normalized by its true integrated mass, and the regression
uses the actual periodic polynomial field of the history's reset coefficients. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)

def highUnionSourceRegression η
    h
    x  :=
  highFrameField d k η (fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)) x

section
variable [∀ i, StandardBorelSpace (E i)] {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionSourceState_measurable  :
    Measurable (highUnionSourceState C R) :=
  historyMarkedRawState_measurable (fun i j => j ∈ highNeighborLabels d k i)
    (highUnionRawUpdate R (highCenterMix C))
    (fun j => highUnionRawUpdate_measurable R G.slope_measurable G.intercept_measurable
      G.vector_measurable G.time_measurable (highCenterMix C) j) highUnionVacuum

theorem highUnionSourceRegression_joint_measurable  η :
    Measurable (fun hx : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark E) × Covariate d => highUnionSourceRegression C R η hx.1 hx.2) :=
by
  let Ω := HistoryMarked (fun i j : HighWindowLabels d k => j ∈ highNeighborLabels d k i)
    (HighUnionMark E)
  have hcoef : Measurable (fun h : Ω => (highUnionSourceState C R h).2) :=
    measurable_snd.comp (highUnionSourceState_measurable C R G)
  exact highFrameField_joint_measurable (Ω := Ω) d k F η
    (fun h : Ω => (highUnionSourceState C R h).2) hcoef
end


end

end NearlyMinimax
