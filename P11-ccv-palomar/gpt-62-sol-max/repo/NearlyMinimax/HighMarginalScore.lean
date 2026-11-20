module

public import NearlyMinimax.HighMarginalLikelihood
public import NearlyMinimax.HighResponseDecoding
public import NearlyMinimax.WeightedScoreContraction


@[expose] public section

/-! The actual observed-data score: the averaged genuine likelihood derivative
 divided by the averaged genuine likelihood. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

def highMarginalLikelihoodDerivative {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : TernarySample d n) : ℝ :=
  ∫ ω, highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z ∂ν

def highMarginalIndexScore {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : TernarySample d n) : ℝ :=
  highMarginalLikelihoodDerivative dependent hsymm ν π activation n a V η p F z /
    highMarginalRawLikelihood ν n a V p F z

def highMarginalRealScore {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : ObservedSample d n) : ℝ :=
  highMarginalIndexScore dependent hsymm ν π activation n a V η p F (decodeDesignResponse a z)

@[simp] theorem highMarginalRealScore_encode {E : Type*} [MeasurableSpace E] {d n : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    {a V η : ℝ} (ha : 0 < a) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : TernarySample d n) :
    highMarginalRealScore dependent hsymm ν π activation n a V η p F (encodeDesignResponse a z) =
      highMarginalIndexScore dependent hsymm ν π activation n a V η p F z := by
  simp [highMarginalRealScore, decodeDesignResponse_encode a ha]

section
variable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E))

section
variable [SFinite ν] (π : Measure E) [SFinite π]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
include ham hp hF

theorem highMarginalIndexScore_measurable :
    Measurable (highMarginalIndexScore dependent hsymm ν π activation n a V η p F) := by
  exact (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF).stronglyMeasurable.integral_prod_left'.measurable.div
    (highMarginalRawLikelihood_measurable ν n a V p F hp hF)

theorem highMarginalRealScore_measurable :
    Measurable (highMarginalRealScore dependent hsymm ν π activation n a V η p F) :=
  (highMarginalIndexScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF).comp
    (decodeDesignResponse_measurable a)

end

end

end NearlyMinimax
