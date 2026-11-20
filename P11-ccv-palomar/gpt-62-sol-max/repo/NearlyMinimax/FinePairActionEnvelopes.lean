module

public import NearlyMinimax.FinePairResponseBounds
public import NearlyMinimax.HighFrameLocalBounds


@[expose] public section

/-! Bounds on the actual pair alias and even-field remainder. The response
cap follows from the genuine finite response packet and chart frame. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem fine_pair_filtered_sum_abs_bound {I : Type*} (s : Finset I) (P : I → Prop) [DecidablePred P]
    (c H : I → ℝ) (R B K : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ s, |c i| ≤ B) (hR : |R| ≤ K) :
    |∑ i ∈ s, c i * (if P i then 1 else 0) * H i * R| ≤
      B*K * ∑ i ∈ s, if P i then |H i| else 0 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hP : P i
  · simp only [if_pos hP, mul_one]
    calc
      _ = (|c i| * |R|) * |H i| := by grind [abs_mul]
      _ ≤ (B*K) * |H i| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hc i hi) hR (abs_nonneg _) hB) (abs_nonneg _)
  · simp [hP]

section
variable {d n F : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (U : Fin n → Covariate d)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (H : ResponseGuards C a V η ρ g w (fun i => highFrameFeature (D := F) (U i)))
include haD hab hn hpD hc H

theorem finePairSelectedAction_abs_le (y : Fin n → Fin 3) :
    |finePairSelectedAction P ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
      finePairActionCap d n M q ad bd C a ρ η *
        ∑ W ∈ ((Finset.univ : Finset (Fin n)).powerset).filter (fun W => P W.card),
          |finePairTimeSubsetMoment T0 N U W| := by
  rw [Finset.sum_filter]
  exact fine_pair_filtered_sum_abs_bound _ (fun W => P W.card)
    (fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i)
    (fun W => finePairTimeSubsetMoment T0 N U W) _ _ _
    (finePairDensityCoefficientBudget_nonneg ad bd (haD.trans hab).le M n)
    (fun W _ => finePairCountCoefficient_product_bound ad bd haD hab M p hpD W)
    (finePairDistance_response_all_count_bound q hn C a V η ρ U g w c y H hc)

end
end NearlyMinimax
