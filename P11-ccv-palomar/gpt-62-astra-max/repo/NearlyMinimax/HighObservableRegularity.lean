module

public import NearlyMinimax.HighObservableProductRule
public import NearlyMinimax.HistoryExpectationRegularity

@[expose] public section

/-! Endpoint regularity of genuine time-dependent marked-prior observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_variable_observable_lipschitz {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hlabels : DegreeAtMost dependent Δ)
    {T B : ℝ} (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {a : E → ℝ} (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {G : ℝ → HistoryMarked dependent E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : BoundedFamily (Icc 0 T) G M)
    {K : NNReal} (hGlip : ∀ h, LipschitzOnWith K (fun u => G u h) (Icc 0 T)) :
    LipschitzOnWith
      ⟨K * (3 / 2) ^ Fintype.card J +
        M * ((historyReferenceRho Δ)⁻¹ * (Fintype.card J) * B * (3 / 2) ^ Fintype.card J),
        by have hρ := historyReferenceRho_pos Δ; positivity⟩
      (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a) (Icc 0 T) := by
  let μ := historyMarkedReference dependent Δ π
  let _  := historyMarkedReference_probability hΔ hlabels π
  have hρ := historyReferenceRho_pos Δ
  have hd := historyDensityPath hlabels hρ hB ha habound hsmall Subset.rfl
  have hl := (hf.mul hd.family).integral_lipschitz μ (hf.lipschitz_mul hd.family hGlip
    (hd.lipschitz (convex_Icc ..) (by positivity)) hM (by positivity))
  simp at hl
  have he u (hu : u ∈ Icc 0 T) := historyMarkedPrior_integral_eq_expectation hlabels hu.1 hB π ha habound
    (historyActivity_mono hu.2 hB hρ.le hsmall) (G u)
  intro u hu v hv
  dsimp
  rw [he u hu, he v hv]
  exact hl hu hv

end NearlyMinimax
