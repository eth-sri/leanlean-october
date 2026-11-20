module

public import NearlyMinimax.HighUnionScorePrimitives
public import NearlyMinimax.HighFrameDesignEnergy


@[expose] public section

/-! Genuine canonical-source Fisher integrability and spatial factorial
energy from actual local numerator envelopes under the original sample law. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)

def highUnionSourceRawNumerator (r : ℕ) (a V η : ℝ)
    (h : HighUnionHistory d k E)
    (j : HighWindowLabels d k) (x : Fin r → Covariate d) (y : Fin r → Fin 3) : ℝ :=
  highMarkedSampleNumerator r (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) a V η (highUnionSourceDensity C R h)
    (highUnionSourceResetDensity C R j h) (highUnionSourceResetCoefficient C R j h)
    (highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
    ((highUnionSourceState C R h).2 j) x y

end NearlyMinimax
