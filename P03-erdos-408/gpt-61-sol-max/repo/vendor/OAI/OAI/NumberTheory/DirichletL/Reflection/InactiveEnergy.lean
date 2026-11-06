module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.InactiveAggregation

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve



section
variable {ι κ : Type*} (L : Finset ι) (rows : Finset κ) (w : ι→ℂ) (f : ι→κ→ℂ)

lemma weighted_finite_row_energy      
        :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤
      (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*(∑ k∈rows, ‖f i k‖^2) := by
  calc
    _ ≤ ∑ k∈rows, (∑ i∈L, ‖w i‖*‖f i k‖^2)*(∑ i∈L, ‖w i‖) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [star_one,mul_one,norm_one,one_pow] using
        DescentWeightedCauchy.weighted_cauchy_sq L w (fun i => f i k) (fun _ => 1)
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      ring

lemma weighted_finite_row_energy_uniform      
         B 
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤(∑ i∈L, ‖w i‖)^2*B := by
  apply (weighted_finite_row_energy L rows w f).trans
  calc
    _ ≤ (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      bound
    _ = _ := by rw [← Finset.sum_mul]; ring

end


end SevenEighths.InverseReflectedPhase

end OAI
