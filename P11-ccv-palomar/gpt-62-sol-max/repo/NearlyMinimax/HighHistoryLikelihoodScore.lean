module

public import NearlyMinimax.HighAppendLikelihood

@[expose] public section

/-! The genuine likelihood score of the constructed marked-history experiment.
The derivative numerator uses actual append likelihood actions and one variance
heat correction. This module does not assume a score derivative identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

def highHistoryLikelihoodDerivative {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : TernarySample d n) : ℝ :=
  (∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z) -
    η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z

/-- A true score: the actual derivative numerator divided by the raw likelihood. -/
def highHistoryLikelihoodScore {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : TernarySample d n) : ℝ :=
  highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z /
    highRawSampleLikelihood n a V (p ω) (F ω) z

theorem highHistoryLikelihoodDerivative_params_measurable {E X : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] [MeasurableSpace X] {d n : ℕ}
    {dependent : J → J → Prop} (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] {activation : E → ℝ} (ham : Measurable activation)
    (a η : ℝ) {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    {ω : X → HistoryMarked dependent E} {z : X → TernarySample d n} {V : X → ℝ}
    (hω : Measurable ω) (hz : Measurable z) (hV : Measurable V) :
    Measurable (fun x => highHistoryLikelihoodDerivative dependent hsymm π activation n a (V x) η p F (ω x) (z x)) :=
  (Finset.measurable_sum _ (fun j _ => highAppendLikelihoodAction_params_measurable hsymm π ham a hp hF hω hz hV j)).sub
    ((highRawSampleVarianceDerivative_params_measurable n a hp hF hω hz hV).const_mul (η^2))

theorem highHistoryLikelihoodDerivative_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : HistoryMarked dependent E × TernarySample d n =>
      highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2) :=
  highHistoryLikelihoodDerivative_params_measurable hsymm π ham a η hp hF measurable_fst measurable_snd measurable_const

theorem highRawSampleLikelihood_pos {Ω : Type*} {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : ∀ ω x, 0 < p ω x)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (ω : Ω) (z : TernarySample d n) :
    0 < highRawSampleLikelihood n a V (p ω) (F ω) z :=
  Finset.prod_pos (fun i _ => mul_pos (hp ω _) (hq ω _ _))

section
variable {E : Type*} [MeasurableSpace E]

theorem highHistoryLikelihoodDerivative_abs_le
    (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P : ℝ) (hP : 0 ≤ P) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (ω : HistoryMarked dependent E) (z : TernarySample d n) :
    |highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z| ≤
      (Fintype.card J : ℝ) * (Ba * P^n) + η^2 * (P^n * ((n : ℝ)/a^2)) := by
  unfold highHistoryLikelihoodDerivative
  calc
    _ ≤ |∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| +
        |η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z| := by
      grind
    _ ≤ (Fintype.card J : ℝ) * (Ba * P^n) + η^2 * (P^n * ((n : ℝ)/a^2)) := by
      apply add_le_add
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc
          _ ≤ ∑ j : J, Ba * P^n := Finset.sum_le_sum (fun j _ =>
            highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa habound n a V P hP
              ha.ne' p F hpb hq j ω z)
          _ = _ := by simp
      · rw [abs_mul, abs_of_nonneg (sq_nonneg η)]
        exact mul_le_mul_of_nonneg_left (highRawSampleVarianceDerivative_abs_le n a V P ha hP
          (p ω) (F ω) (hpb ω) (hq ω) z) (sq_nonneg η)

end

end NearlyMinimax
