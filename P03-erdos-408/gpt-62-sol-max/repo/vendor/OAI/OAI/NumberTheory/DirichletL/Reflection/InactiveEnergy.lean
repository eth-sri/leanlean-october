module

public import OAI.NumberTheory.DirichletL.Reflection.InactiveAggregation
public import OAI.NumberTheory.DirichletL.Reflection.ShapeWeights

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve
noncomputable section

lemma weighted_finite_row_energy {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) :
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

lemma weighted_finite_row_energy_uniform {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) (B : ℝ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤(∑ i∈L, ‖w i‖)^2*B := by
  apply (weighted_finite_row_energy L rows w f).trans
  calc
    _ ≤ (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring


/-- Sum a uniform dyadic estimate over the six units and the retained dyads. -/
lemma retained_sum_energy {ι κ : Type*} [Fintype κ] (D : Finset ι)
    (f : ActualEisensteinCubic.Oˣ → ι → κ → ℂ) (B : ℝ)
    (hf : ∀ u i, i ∈ D → (∑ k, ‖f u i k‖^2) ≤ B) :
    (∑ k, ‖∑' u : ActualEisensteinCubic.Oˣ, ∑ i ∈ D, f u i k‖^2) ≤
      36 * (D.card:ℝ)^2 * B := by
  let : Finite ActualEisensteinCubic.Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype ActualEisensteinCubic.Oˣ := Fintype.ofFinite _
  have hh := weighted_finite_row_energy_uniform
    (Finset.univ ×ˢ D) Finset.univ (fun _ => (1:ℂ)) (fun ui k => f ui.1 ui.2 k) B
    (fun ui hui => hf ui.1 ui.2 (Finset.mem_product.mp hui).2)
  have hcard : Fintype.card ActualEisensteinCubic.Oˣ = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [one_mul, norm_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_product, Finset.card_univ, hcard, Finset.sum_product, tsum_fintype] at hh ⊢
  refine hh.trans_eq ?_
  push_cast
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
