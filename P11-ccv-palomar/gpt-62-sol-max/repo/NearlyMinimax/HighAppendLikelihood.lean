module

public import NearlyMinimax.HighLikelihoodDerivative
public import NearlyMinimax.HistoryPriorWeakTransport


@[expose] public section

/-! The genuine append likelihood action and its Fubini observable bridge. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Activation-weighted raw likelihood after the actual canonical marked append. -/
def highAppendLikelihoodAction {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ) (j : J)
    (ω : HistoryMarked dependent E) (z : TernarySample d n) : ℝ :=
  ∫ e, activation e * highRawSampleLikelihood n a V
    (p (historyMarkedAppend dependent hsymm j (ω,e)))
    (F (historyMarkedAppend dependent hsymm j (ω,e))) z ∂π

theorem highAppendLikelihoodAction_params_measurable
    {E X : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace X] {d n : ℕ}
    {dependent : J → J → Prop} (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] {activation : E → ℝ} (ha : Measurable activation) (a : ℝ)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    {ω : X → HistoryMarked dependent E} {z : X → TernarySample d n} {V : X → ℝ}
    (hω : Measurable ω) (hz : Measurable z) (hV : Measurable V) (j : J) :
    Measurable (fun x => highAppendLikelihoodAction dependent hsymm π activation n a (V x) p F j (ω x) (z x)) := by
  have hm := (historyMarkedAppend_measurable dependent hsymm j).comp
    ((hω.comp (measurable_fst : Measurable (Prod.fst : X × E → X))).prodMk measurable_snd)
  exact ((ha.comp measurable_snd).mul
    (highRawSampleLikelihood_params_measurable a hp hF hm (hz.comp measurable_fst)
      (hV.comp measurable_fst))).stronglyMeasurable.integral_prod_right'.measurable

theorem highAppendLikelihoodAction_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ha : Measurable activation) (n : ℕ) (a V : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) (j : J) :
    Measurable (fun z : HistoryMarked dependent E × TernarySample d n =>
      highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2) :=
  highAppendLikelihoodAction_params_measurable hsymm π ha a hp hF measurable_fst measurable_snd measurable_const j

theorem highAppendLikelihoodAction_abs_le {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P) (ha : a ≠ 0)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (j : J) (ω : HistoryMarked dependent E) (z : TernarySample d n) :
    |highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| ≤ Ba * P^n := by
  rw [highAppendLikelihoodAction, ← Real.norm_eq_abs]
  have hb : ∀ e, ‖activation e * highRawSampleLikelihood n a V
      (p (historyMarkedAppend dependent hsymm j (ω,e)))
      (F (historyMarkedAppend dependent hsymm j (ω,e))) z‖ ≤ Ba * P^n := by
    intro e
    simpa using mul_le_mul (habound e) (highRawSampleLikelihood_abs_le n a V P
          (p (historyMarkedAppend dependent hsymm j (ω,e)))
          (F (historyMarkedAppend dependent hsymm j (ω,e)))
          (hp _) ha (hq _) z) (abs_nonneg _) hBa
  simpa using norm_integral_le_of_norm_le_const (μ := π) (Eventually.of_forall hb)

end NearlyMinimax
