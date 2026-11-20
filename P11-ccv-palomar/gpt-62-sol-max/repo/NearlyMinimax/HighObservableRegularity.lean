module

public import NearlyMinimax.HighObservableProductRule

@[expose] public section

/-! Endpoint regularity of genuine time-dependent marked-prior observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_variable_observable_lipschitz {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    {G : ℝ → HistoryMarked dependent E → ℝ} {M : ℝ} {K : NNReal}
    (hG : BoundedPath (Icc 0 T) G M) (hGlip : ∀ h, LipschitzOnWith K (fun u => G u h) (Icc 0 T)) :
    LipschitzOnWith
      ⟨(K : ℝ) * (3 / 2 : ℝ) ^ Fintype.card J +
        M * ((historyReferenceRho Δ)⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J),
        by have hρ := historyReferenceRho_pos Δ; have := hG.nonneg; have := P.bound_nonneg; positivity⟩
      (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a) (Icc 0 T) := by
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := P.reference_probability
  obtain ⟨hφ, hφ'⟩ := P.density_path_bounds (Subset.rfl : Icc 0 T ⊆ Icc 0 T)
  have hL := (hG.mul hφ).lipschitzIntegral_prob (ν := μ)
    (hG.lipschitzMul hφ hGlip (hφ'.lipschitzOnWith (convex_Icc 0 T)
      (fun u _ h => historyMarkedDensity_hasDerivAt dependent _ u a h)))
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [P.integral_eq_density hu, P.integral_eq_density hv]
  exact hL.dist_le_mul u hu v hv

end NearlyMinimax
