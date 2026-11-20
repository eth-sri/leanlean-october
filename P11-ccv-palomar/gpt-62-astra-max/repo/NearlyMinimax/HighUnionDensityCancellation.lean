module

public import NearlyMinimax.FinePairUnionMassAnnihilation


@[expose] public section

/-! Response-coordinate elimination for arbitrary finite complete-row
unions. The structural assumptions concern the uncentered primitive row
packet and its density-mark projection, and are discharged by actual
finite response rules in the concrete source family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- Every bounded measurable functional of the appended density has zero
activation integral if each row annihilates its projected density observables. -/
theorem highUnionSource_density_action_zero
    {d k F : ℕ} [NeZero k] [LinearOrder (HighWindowLabels d k)]
    {I : Type*} [Fintype I] {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    [∀ i, StandardBorelSpace (E i)] {C : ModelConstants d}
    {R : HighUnionRowData d k F I E} {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    {D : I → Type*} [∀ i, MeasurableSpace (D i)]
    {project : (i : I) → E i → D i} {lift : (i : I) → D i → E i}
    (hlift : ∀ i, Measurable (lift i))
    (hSlope : ∀ j i e x, R.rowSlope j i e x = R.rowSlope j i (lift i (project i e)) x)
    (hIntercept : ∀ i e, R.rowIntercept i e = R.rowIntercept i (lift i (project i e)))
    (hRowZero : ∀ i, ∀ H : D i → ℝ, Measurable H → ∀ L : ℝ,
      (∀ z, ‖H z‖ ≤ L) → (∫ e, R.rowActivation i e * H (project i e) ∂(R.rowLaw i)) = 0)
    (j : HighWindowLabels d k)
    (h : WindowHistory d k E)
    (T : (Covariate d → ℝ) → ℝ) (L : ℝ) :
    let Fobs := fun e => T (highUnionSourceDensity C R (historyMarkedAppend j (h,e)))
    Measurable Fobs → (∀ e, ‖Fobs e‖ ≤ L) →
      (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C)) = 0 := by
  intro Fobs hF hFb
  rw [highUnionSource_bounded_action G hpos hF hFb]
  apply Finset.sum_eq_zero
  intro i _
  let Hi := fun z => Fobs (Sum.inl ⟨i,lift i z⟩)
  have he (e : E i) : Fobs (Sum.inl ⟨i,e⟩) = Hi (project i e) := by
    apply congrArg T
    funext x
    change (highUnionSourceState C R _).1 x = (highUnionSourceState C R _).1 x
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if x ∈ highTorusPatch j then R.rowSlope j i e x * _ + R.rowIntercept i e else _) =
      (if x ∈ highTorusPatch j then R.rowSlope j i (lift i (project i e)) x * _ + R.rowIntercept i (lift i (project i e)) else _)
    grind
  calc
    _ = _ :=
      integral_congr_ae (.of_forall fun e => congrArg _ (he e))
    _ = 0 := hRowZero i Hi (hF.comp (measurable_inl.comp ((measurable_sigma_mk_actual i).comp (hlift i))))
      L (fun _ => hFb _)

end NearlyMinimax
