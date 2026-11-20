module

public import NearlyMinimax.LowerActivityHierarchy
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
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
theorem completeSourceMass_prior_tilted_tail (hk : 2 ≤ k) (T : ℝ)
    (hsmall : T*(highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass /
      highCenterMix C)/historyReferenceRho (3^d) ≤ 1/(2+8*((3^d:ℕ):ℝ)^2))
    (n : ℕ) (epsilon : ℝ)
    (hepsilon : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ epsilon)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (massPowerTilt
      (historyMarkedPrior (highNeighbors d k) (3^d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C)))
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu)) n).real
      {h | epsilon < |highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu) h-1|} ≤
      2*Real.exp (-epsilon^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  have G := (completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN).1
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _ (highUnionSourceMass_measurable C _ G) n
    (completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hsmall t ht) epsilon]
  apply highUnionSourceMass_reference_tilted_tail <;> assumption

end Pointwise

/-- The fixed canonical source coefficient; it depends only on model constants. -/
def highCompleteSourceSaddleCoefficient {d : ℕ} (C : ModelConstants d) : ℝ :=
  lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

def highCompleteSourceSaddleTheta {d : ℕ} (C : ModelConstants d) : ℝ :=
  lowerSaddleTheta C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

/-- Parameters of the rounded saddle for the complete row family. -/
abbrev completeSaddleGrid {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x

abbrev completeSaddleM {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleM (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleD d (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleN {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleN C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleMu {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x
abbrev completeSaddleEta {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) :=
  lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf x
abbrev completeSaddleC0 {d : ℕ} (C : ModelConstants d) :=
  densityIntervalExponent C.densityLower C.densityUpper+1
abbrev completeSaddleEll {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (completeSaddleC0 C)
    (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleTau {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  shrunkDensityExponent C.densityLower C.densityUpper (completeSaddleM C x)
abbrev completeSaddleAD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityLower+1/(completeSaddleM C x : ℝ)
abbrev completeSaddleBD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityUpper-1/(completeSaddleM C x : ℝ)

abbrev completeSaddleActivityScale {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleActivity C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x

/-- The actual geometric envelope for the complete-row tilted bad mass. -/
def highCompleteSourceSaddleTail {d : ℕ} (C : ModelConstants d) (Cω cm : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleExceptionalTail d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
    (cm^2/(8*highHistoryMassMomentConstant d C.densityLower C.densityUpper)) n

end NearlyMinimax
