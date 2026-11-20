module

public import NearlyMinimax.FinePairUnionMassAnnihilation
public import NearlyMinimax.HighUnionScorePrimitives


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

attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

section
variable {d k F : ℕ} [NeZero k] [LinearOrder (HighWindowLabels d k)]
    {I : Type*} [Fintype I] {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    [∀ i, StandardBorelSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

/-- Any bounded measurable observable of the reset density loses the
response coordinates, so its signed action vanishes. -/
theorem highUnionSource_reset_observable_zero
    (hpos : ∀ i, 0 < R.rowMass i)
    (D : I → Type*) [∀ i, MeasurableSpace (D i)]
    (project : (i : I) → E i → D i) (lift : (i : I) → D i → E i)
    (hlift : ∀ i, Measurable (lift i))
    (hRowZero : ∀ i, ∀ H : D i → ℝ, Measurable H → ∀ L : ℝ,
      (∀ z, ‖H z‖ ≤ L) → (∫ e, R.rowActivation i e * H (project i e) ∂(R.rowLaw i)) = 0)
    (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E)
    (hProject : ∀ i (e : E i) x,
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i, e⟩) x =
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i, lift i (project i e)⟩) x)
    (Φ : (Covariate d → ℝ) → ℝ)
    (hΦ : Measurable (fun e => Φ (highUnionSourceResetDensity C R j h e)))
    (B : ℝ) (hB : ∀ e, ‖Φ (highUnionSourceResetDensity C R j h e)‖ ≤ B) :
    (∫ e, highUnionActivation R (highCenterMix C) e *
      Φ (highUnionSourceResetDensity C R j h e) ∂highUnionLaw R (highCenterMix C)) = 0 := by
  let Fobs := fun e => Φ (highUnionSourceResetDensity C R j h e)
  rw [highUnionSource_bounded_action C R G hpos Fobs hΦ B hB]
  apply Finset.sum_eq_zero
  intro i _
  let Hi := fun z => Fobs (Sum.inl ⟨i, lift i z⟩)
  have hHi := hΦ.comp (measurable_inl.comp ((measurable_sigma_mk_actual i).comp (hlift i)))
  refine (integral_congr_ae (.of_forall fun e => ?_)).trans (hRowZero i Hi hHi B (fun _ => hB _))
  exact congrArg (fun v => R.rowActivation i e * Φ v) (funext fun x => hProject i e x)

end

end NearlyMinimax
