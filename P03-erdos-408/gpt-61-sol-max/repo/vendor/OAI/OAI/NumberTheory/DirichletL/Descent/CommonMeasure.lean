module

public import OAI.NumberTheory.DirichletL.Descent.SlotProducts

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open MeasureTheory CanonicalQuadraticSieve CompletedGauss



theorem common_measure_energy {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (b : Ω → ℂ) (φ : κ → Ω → ℂ)  E  (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖) μ)
    (hφ : ∀ k, Integrable (fun t => b t * φ k t) μ)
    (hbound : ∀ t, (∑ k, ‖φ k t‖ ^ 2) ≤ E) :
    (∑ k, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) ≤ E * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : Ω → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t * φ k t)
  have hF (t : Ω) : ‖F t‖ ≤ ‖b t‖ * Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE]
    change (∑ k, ‖b t * φ k t‖ ^ 2) ≤ ‖b t‖ ^ 2 * E
    simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫ t, F t ∂μ) = e.symm (fun k => ∫ t, b t * φ k t ∂μ) := by
    rw [show F = (fun t => e.symm (fun k => b t * φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t, b t * φ k t ∂μ)‖ ≤
      (∫ t, ‖b t‖ ∂μ) * Real.sqrt E := by
    rw [← he, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE] at hs
  simpa [e, mul_comm] using hs


end SevenEighths.InverseMoment

end OAI
