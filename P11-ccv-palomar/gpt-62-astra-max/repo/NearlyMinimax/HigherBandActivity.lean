module

public import NearlyMinimax.HigherBandRows

@[expose] public section

/-! Activity bounds derived from the actual separated cardinal row
measures and finite density/response atom weights. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable (d r m D q : ℕ) (hr : 2 ≤ r) (a b : ℝ) (hD : 1 ≤ D) (C lam L T : ℝ)

def higherBandInterpolationCap : ℝ :=
  2 * (r : ℝ) * (1024 * |lam| * (d : ℝ)^2)^(r-1) * T^2 * (1+Real.log T)^(r-2)

include hr in
theorem higherBandCarrier_cost_integral_le (hT : 1 ≤ T) (hLT : L ≤ T) (fine : Bool) :
    (∫ ζ, separatedMatrixCost (higherBandCarrierAmplitude d r D lam fine) ζ
      ∂higherBandCarrierMeasure d r L T fine) ≤ higherBandInterpolationCap d r lam T := by
  cases fine
  · have h := cardinal_separated_cost_integral_le (d := d) (D := D) hr lam hT
    have hb : 0 ≤ (r : ℝ) * (1024 * |lam| * (d : ℝ)^2)^(r-1) * T^2 * (1+Real.log T)^(r-2) := by
      bound
    exact h.trans (by dsimp [higherBandInterpolationCap]; nlinarith)
  · exact cardinal_band_cost_integral_le hr lam L hT hLT

def ordinaryDensityActivityBase : ℝ :=
  Real.exp (1 + intervalExteriorTau a b) * |b / densityMargin a b 0|

def higherBandRowActivityCap : ℝ :=
  (ordinaryDensityActivityBase a b)^r * (D : ℝ)^r *
    Real.exp ((m : ℝ) * intervalExteriorTau a b) *
    responseVariation q * (2*C^2) * higherBandInterpolationCap d r lam T

include hr hD in
/-- The bound on the actual activation mass follows from actual atom
variation and genuine positive separated-representation cost. -/
theorem higherBandRowMass_le_activityCap
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (C lam L T : ℝ)
    (hT : 1 ≤ T) (hLT : L ≤ T) (fine : Bool) :
    higherBandRowMass d r m D q a b C lam L T fine ≤ higherBandRowActivityCap d r m D q a b C lam T := by
  letI := higherBandCarrierMeasure_finite d r L hT fine
  rw [higherBandRowMass_eq_variation d r m D q a b C lam L T hT fine]
  have h := highPacketSignedMeasure_exponential_cost ha hab m r D q (by omega) hD C
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L hT fine)
  apply h.trans
  apply mul_le_mul_of_nonneg_left
  · solve_by_elim [higherBandCarrier_cost_integral_le]
  · positivity

end NearlyMinimax
