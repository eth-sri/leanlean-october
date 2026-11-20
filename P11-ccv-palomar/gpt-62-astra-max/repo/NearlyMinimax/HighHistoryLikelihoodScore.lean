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

section
variable {E : Type*} [MeasurableSpace E] {d : ℕ} {dependent : J → J → Prop} [Std.Symm dependent]
    (π : Measure E) (activation : E → ℝ)

def highHistoryLikelihoodDerivative {n : ℕ} (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : IndexedSample d n) : ℝ :=
  (∑ j, highAppendLikelihoodAction π activation a V p F j ω z) -
    η^2 * highRawSampleVarianceDerivative a V (p ω) (F ω) z

/-- A true score: the actual derivative numerator divided by the raw likelihood. -/
def highHistoryLikelihoodScore (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : IndexedSample d n) : ℝ :=
  highHistoryLikelihoodDerivative π activation a V η p F ω z /
    highRawSampleLikelihood a V (p ω) (F ω) z

theorem highHistoryLikelihoodDerivative_measurable
    [StandardBorelSpace E] {d : ℕ}
    {dependent : J → J → Prop} [Std.Symm dependent]
    (π : Measure E) [SFinite π] {activation : E → ℝ} (ham : Measurable activation)
    (n : ℕ) (a V η : ℝ) {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : HistoryMarked dependent E × (IndexedSample d n) =>
      highHistoryLikelihoodDerivative π activation a V η p F z.1 z.2) := (Finset.measurable_sum _ (fun j _ =>
    highAppendLikelihoodAction_measurable π ham n a V hp hF j)).sub
      ((highRawSampleVarianceDerivative_joint_measurable n a V hp hF).const_mul (η^2))

end

variable {E Ω : Type*}

theorem highRawSampleLikelihood_pos {d n : ℕ} {a V : ℝ}
    (p F : Ω → Covariate d → ℝ) (hp : ∀ ω x, 0 < p ω x)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (ω : Ω) (z : IndexedSample d n) :
    0 < highRawSampleLikelihood a V (p ω) (F ω) z :=
  Finset.prod_pos (fun i _ => mul_pos (hp ω _) (hq ω _ _))

/-- Integrability and Fubini for the actual score numerator derive from
bounded primitive likelihoods, including all reset states. -/
theorem highHistoryLikelihoodDerivative_observable [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    {dependent : J → J → Prop} [Std.Symm dependent]
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    {activation : E → ℝ} (ham : Measurable activation)
    {Ba : ℝ} (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    {n : ℕ} {a V : ℝ} (η P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : 0 < a)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z,
      H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative π activation a V η p F z.1 z.2
      ∂ν.prod (highSampleReference d n)) =
      (-η^2 * ∫ ω, highRawObservableVarianceDerivative a V (p ω) (F ω) H ∂ν) +
        ∑ j, ∫ z,
          highRawObservable a V (p (historyMarkedAppend j z))
            (F (historyMarkedAppend j z)) H * activation z.2 ∂ν.prod π := by
  let Q := HistoryMarked dependent E × (IndexedSample d n)
  let μ  := ν.prod (highSampleReference d n)
  let test : Q → ℝ := fun z => H (encodeDesignResponse a z.2)
  let A : J → Q → ℝ := fun j z =>
    highAppendLikelihoodAction π activation a V p F j z.1 z.2
  let D : Q → ℝ := fun z => highRawSampleVarianceDerivative a V (p z.1) (F z.1) z.2
  have htest : Measurable test := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hiA j : Integrable (fun z => test z * A j z) μ := by
    apply Integrable.of_bound (htest.mul
      (highAppendLikelihoodAction_measurable π ham n a V hp hF j)).aestronglyMeasurable
      (B * (Ba * P^n))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) *
        highAppendLikelihoodAction π activation a V p F j z.1 z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      bound [highAppendLikelihoodAction_abs_le π hBa habound hP ha.ne' hpb hq j z.1 z.2]
  have hiD : Integrable (fun z => test z * D z) μ := by
    apply Integrable.of_bound (htest.mul
      (highRawSampleVarianceDerivative_joint_measurable n a V hp hF)).aestronglyMeasurable
      (B * (P^n * (n/a^2)))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) * highRawSampleVarianceDerivative a V (p z.1) (F z.1) z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleVarianceDerivative_abs_le ha hP (hpb _) (hq _) _)
        (abs_nonneg _) hB
  have heD : (∫ z, test z * D z ∂μ) =
      ∫ ω, highRawObservableVarianceDerivative a V (p ω) (F ω) H ∂ν := MeasureTheory.integral_prod _ hiD
  calc
    _ = ∫ z, ((∑ j, test z * A j z) - η^2 * (test z * D z)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp [highHistoryLikelihoodDerivative]
        rw [mul_sub, Finset.mul_sum]
        ring
    _ = _ := by
      rw [integral_sub (integrable_finsetSum _ (fun j _ => hiA j)) (hiD.const_mul _),
        integral_finsetSum _ (fun j _ => hiA j), integral_const_mul]
    _ = _ := by
      rw [heD]
      have heA j := highAppendLikelihoodAction_prior_observable π ν ham hBa habound hP hB ha.ne' hp hF hpb hq hH hHb j
      have hs : (∑ j, ∫ z, test z * A j z ∂μ) =
          ∑ j, ∫ z,
            highRawObservable a V (p (historyMarkedAppend j z))
              (F (historyMarkedAppend j z)) H * activation z.2 ∂ν.prod π := by
        apply Finset.sum_congr rfl
        intro j _
        exact (heA j).symm
      rw [hs]
      ring

theorem highHistoryLikelihoodDerivative_abs_le [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    {dependent : J → J → Prop} [Std.Symm dependent]
    {activation : E → ℝ} {Ba : ℝ} (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    {n : ℕ} (a V η : ℝ) {P : ℝ} (hP : 0 ≤ P) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (ω : HistoryMarked dependent E) (z : IndexedSample d n) :
    |highHistoryLikelihoodDerivative π activation a V η p F ω z| ≤
      (Fintype.card J) * (Ba * P^n) + η^2 * (P^n * (n/a^2)) := by
  unfold highHistoryLikelihoodDerivative
  calc
    _ ≤ |∑ j, highAppendLikelihoodAction π activation a V p F j ω z| +
        |η^2 * highRawSampleVarianceDerivative a V (p ω) (F ω) z| := by
      grind [highAppendLikelihoodAction]
    _ ≤ _ := by
      apply add_le_add
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc
          _ ≤ _ := Finset.sum_le_sum (fun j _ =>
            highAppendLikelihoodAction_abs_le π hBa habound hP
              ha.ne' hpb hq j ω z)
          _ = _ := by simp
      · rw [abs_mul]
        bound [highRawSampleVarianceDerivative_abs_le ha hP (hpb ω) (hq ω) z]

end NearlyMinimax
