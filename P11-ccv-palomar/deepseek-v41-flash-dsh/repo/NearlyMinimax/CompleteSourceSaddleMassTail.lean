module

public import NearlyMinimax.CompleteSourceInvariantMass
public import NearlyMinimax.HighUnionTiltedTail
public import NearlyMinimax.HighMassTailScale

@[expose] public section

/-! Genuine exceptional-mass tails of the complete singleton/pair/higher
row prior, specialized to the actual rounded lower saddle. The deterministic
envelope is fixed before the extension domain and all source times. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable

section Pointwise
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ell N mu : ℝ) (hCfr : 1 ≤ Cfr) (hell : 0 < ell) (hellN : ell < N)
include hD hq hM hCfr hell hellN

/-- Every time of the actual complete-row source has the genuine tilted
exceptional bound. All mass-law and local cancellation premises are
discharged by the true complete packet construction. -/
theorem completeSourceMass_prior_tilted_tail (hk : 2 ≤ k) (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T*(highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass /
      highCenterMix C)/historyReferenceRho (3^d) ≤ 1/(2+8*((3^d:ℕ):ℝ)^2))
    (n : ℕ) (epsilon : ℝ)
    (hepsilon : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ epsilon)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C)))
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu)) n).real
      {h | epsilon < |highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu) h-1|} ≤
      2*Real.exp (-epsilon^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _ (highUnionSourceMass_measurable C _ G) n
    (completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht) epsilon]
  exact highUnionSourceMass_reference_tilted_tail C _ G hk n epsilon hepsilon

end Pointwise

variable {d : ℕ}

/-- The fixed canonical source coefficient; it depends only on model constants. -/
def highCompleteSourceSaddleCoefficient (C : ModelConstants d) : ℝ :=
  lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

def highCompleteSourceSaddleTheta (C : ModelConstants d) : ℝ :=
  lowerSaddleTheta C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

/-- The actual geometric envelope for the complete-row tilted bad mass. -/
def highCompleteSourceSaddleTail (C : ModelConstants d) (Cω cm : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleExceptionalTail d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
    (cm^2/(8*highHistoryMassMomentConstant d C.densityLower C.densityUpper)) n

end NearlyMinimax
