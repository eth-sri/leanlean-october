module

public import NearlyMinimax.HighUnionLikelihoodScore
public import NearlyMinimax.HighUnionInvariantMass


@[expose] public section

/-! Genuine Borel reset primitives for the canonical full-union source. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)

section
variable (j : HighWindowLabels d k) (h : WindowHistory d k E) (e : HighUnionMark E)

/-- The actual density after appending the mark at the given window. -/
def highUnionSourceResetDensity (x : Covariate d) : ℝ :=
  highUnionSourceDensity C R (historyMarkedAppend j (h,e)) x

/-- The actual reset coefficient vector at the selected window. -/
def highUnionSourceResetCoefficient : HighFrameVector d D :=
  highUnionResponseReset R e ((highUnionSourceState C R h).2 j)

end

include G in
theorem highUnionSourceDensity_coarse_interval
    (h : WindowHistory d k E)
    (x : Covariate d) : C.densityLower ≤ highUnionSourceDensity C R h x ∧
      highUnionSourceDensity C R h x ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_interval C R G h x
  have hM : 0 < M := by linarith [(highCenterResolution_guards G.resolution).1]
  constructor <;> linarith [hb.1,hb.2,one_div_pos.mpr hM]

include G in
theorem highUnionSourceResetDensity_measurable (j : HighWindowLabels d k)
    (h : WindowHistory d k E) :
    Measurable (Function.uncurry (highUnionSourceResetDensity C R j h)) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  exact (highUnionSourceDensity_joint_measurable C R G).comp (((historyMarkedAppend_measurable j).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)

include G in
theorem highUnionSourceResetDensity_abs_le (j : HighWindowLabels d k)
    (h : WindowHistory d k E)
    (e : HighUnionMark E) (x : Covariate d) :
    |highUnionSourceResetDensity C R j h e x| ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_coarse_interval C R G
    (historyMarkedAppend j (h,e)) x
  rw [highUnionSourceResetDensity,abs_of_nonneg (C.densityLower_pos.le.trans hb.1)]
  exact hb.2

include G in
theorem highUnionSourceResetCoefficient_measurable (j : HighWindowLabels d k)
    (h : WindowHistory d k E)
    (γ : HighFrameIndex d D) :
    Measurable (fun e => highUnionSourceResetCoefficient C R j h e γ) := (measurable_const.sub (highUnionResponseTime_measurable R G.time_measurable)).mul
    measurable_const |>.add ((highUnionResponseTime_measurable R G.time_measurable).mul
      (highUnionResponseVector_measurable R G.vector_measurable γ))

theorem highUnionSourceResetDensity_outside (j : HighWindowLabels d k)
    (h : WindowHistory d k E)
    (e : HighUnionMark E) (x : Covariate d) (hx : x ∉ highTorusPatch j) :
    highUnionSourceResetDensity C R j h e x = highUnionSourceDensity C R h x :=
  highUnionSourceDensity_append_of_not_mem R C h e hx

end NearlyMinimax
