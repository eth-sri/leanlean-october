module

public import NearlyMinimax.HighRawObservableDerivative
public import NearlyMinimax.HighObservableRegularity


@[expose] public section

/-! Closed-interval absolute continuity for the actual high-prior data observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem highRawObservable_lipschitzOn {d n : ℕ} {a v η T P B : ℝ}
    (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) (ω : Ω) :
    LipschitzOnWith
      ⟨B * (η ^ 2 * (P ^ n * (n / a ^ 2))) * (highSampleReference d n).real Set.univ, by positivity⟩
      (fun u => highRawObservable a (v - η ^ 2 * u) (p ω) (F ω) H) (Icc 0 T) := by
  have path := highObservableIntegrandPath ha hP hp.of_uncurry_left hF.of_uncurry_left (hpb ω)
    (fun u hu => hq u hu ω) hH hHb
  exact path.family.integral_lipschitz _ (path.lipschitz (convex_Icc ..) (by positivity))

variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_rawObservable_exists_lipschitz {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hlabels : DegreeAtMost dependent Δ)
    {T Ba : ℝ} (hBa : 0 ≤ Ba) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {activation : E → ℝ} (hactivation : Measurable activation)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {d n : ℕ} {a v η P B : ℝ} (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    ∃ K : NNReal, LipschitzOnWith K
      (fun u => ∫ ω, highRawObservable a (v - η ^ 2 * u) (p ω) (F ω) H
        ∂historyMarkedPrior dependent Δ u π activation) (Icc 0 T) := by
  have hGM u  := highRawObservable_measurable a (v - η ^ 2 * u) hp hF hH
  have hM : 0 ≤ (B * P ^ n * (highSampleReference d n).real Set.univ) := by positivity
  have hGb u hu ω  :=
    highRawObservable_abs_le hP hB (hpb ω) ha.ne' (hq u hu ω) hHb
  have hGlip ω  :=
    highRawObservable_lipschitzOn ha hP hB hp hF hpb hq hH hHb ω
  exact ⟨_, historyMarkedPrior_variable_observable_lipschitz hΔ hlabels hBa π hactivation habound hsmall hM ⟨hGM, hGb⟩ hGlip⟩

end NearlyMinimax
