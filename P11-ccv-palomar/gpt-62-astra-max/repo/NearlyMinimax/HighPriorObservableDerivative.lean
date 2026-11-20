module

public import NearlyMinimax.HighRawObservableDerivative


@[expose] public section

/-! Actual high-prior observable derivative: signed append generator plus variance heat. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_rawObservable_hasDerivAt {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hlabels : DegreeAtMost dependent Δ)
    {T Ba t : ℝ} (ht : 0 < t) (htT : t < T) (hBa : 0 ≤ Ba)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {activation : E → ℝ} (hactivation : Measurable activation)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {d n : ℕ} (a v η P B : ℝ) (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Ioo 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    HasDerivAt (fun u => ∫ ω, highRawObservable a (v - η ^ 2 * u) (p ω) (F ω) H
      ∂historyMarkedPrior dependent Δ u π activation)
      ((-η ^ 2 * ∫ ω, highRawObservableVarianceDerivative a (v - η ^ 2 * t) (p ω) (F ω) H
        ∂historyMarkedPrior dependent Δ t π activation) +
        historyMarkedPriorGenerator Δ t π activation
          (fun ω => highRawObservable a (v - η ^ 2 * t) (p ω) (F ω) H)) t := by
  let G  := fun u ω =>
    highRawObservable a (v - η ^ 2 * u) (p ω) (F ω) H
  let G'  := fun u ω =>
    -η ^ 2 * highRawObservableVarianceDerivative a (v - η ^ 2 * u) (p ω) (F ω) H
  let M'  := η ^ 2 * (B * (P ^ n * (n / a ^ 2)) * (highSampleReference d n).real Set.univ)
  have hGM u  := highRawObservable_measurable a (v - η ^ 2 * u) hp hF hH
  have hG'M u  :=
    ((by have h := ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul (highRawSampleVarianceDerivative_joint_measurable n a (v - η ^ 2 * u) hp hF); exact h.stronglyMeasurable.integral_prod_right'.measurable : Measurable fun ω => highRawObservableVarianceDerivative a (v - η ^ 2 * u) (p ω) (F ω) H)).const_mul (-η ^ 2)
  have hGb u hu ω  :=
    highRawObservable_abs_le hP hB (hpb ω)
      ha.ne' (hq u hu ω) hHb
  have hG'b u (hu : u ∈ Ioo 0 T) ω : |G' u ω| ≤ M' := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    bound [highRawObservableVarianceDerivative_abs_le ha hP hB (hpb ω) (hq u hu ω) hHb]
  have hGD ω u (hu : u ∈ Ioo 0 T)  :=
    highRawObservable_hasDerivAt_path ha hu.1 hu.2 hP hp hF hpb hq hH hHb ω
  have h := historyMarkedPrior_observable_product_rule hΔ hlabels ht htT hBa π hactivation habound hsmall (by positivity) ⟨⟨hGM, hGb⟩, ⟨hG'M, hG'b⟩, hGD⟩
  simpa only [  integral_const_mul] using h

end NearlyMinimax
