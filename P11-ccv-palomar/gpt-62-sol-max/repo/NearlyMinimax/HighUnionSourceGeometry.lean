module

public import NearlyMinimax.HighUnionSource

@[expose] public section

/-! Exact locality of the complete-row canonical source reset. -/
noncomputable section
open Set MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)]
  (R : HighUnionRowData d k F I E)

theorem highUnionRawUpdate_density_of_not_mem (δ : ℝ)
    (j : HighWindowLabels d k) (e : HighUnionMark E) (θ : HighRawState d k F)
    (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    (highUnionRawUpdate R δ j e θ).1 x = θ.1 x := by
  simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_right hx]

variable [NeZero k] [LinearOrder (HighWindowLabels d k)] (C : ModelConstants d)

section
variable (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E)
    (e : HighUnionMark E)

theorem highUnionSourceState_append :
    highUnionSourceState C R (historyMarkedAppend
      (highNeighbors d k)
      (highNeighbors_symm d k) j (h,e)) =
    highUnionRawUpdate R (highCenterMix C) j e (highUnionSourceState C R h) :=
  by apply highUnionMarkedState_append <;> assumption

/-- Appending a full source mark leaves every density value outside that
label's physical patch exactly unchanged. -/
theorem highUnionSourceDensity_append_of_not_mem (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    highUnionSourceDensity C R (historyMarkedAppend
      (highNeighbors d k)
      (highNeighbors_symm d k) j (h,e)) x =
    highUnionSourceDensity C R h x := by
  change (highUnionSourceState C R _).1 x = _
  rw [highUnionSourceState_append R C j h e]
  apply highUnionRawUpdate_density_of_not_mem <;> assumption

end

end
end NearlyMinimax
