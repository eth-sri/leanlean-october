module

public import NearlyMinimax.HighUnionScore
public import NearlyMinimax.HighSelectedScoreEnergy


@[expose] public section

/-! Exact reduction of the complete marked score to observations inside
its true patch. Density resets and regression windows are unchanged
outside the selected coordinates, so their likelihood factors cancel. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

@[to_additive]
private theorem prod_eq_prod_embedding {I J M : Type*} [Fintype I] [Fintype J] [CommMonoid M]
    (e : I ↪ J) (f : J → M) (h : ∀ j, j ∉ Finset.univ.map e → f j = 1) :
    (∏ j, f j) = ∏ i, f (e i) := by
  rw [← Finset.prod_map]
  exact (Finset.prod_subset (Finset.subset_univ _) (fun j _ => h j)).symm

section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

theorem high_marked_local_score_selected {n r : ℕ} (e : Fin r ↪ Fin n)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
        cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) := by
  rw [high_marked_local_score_ratio π activation a V η p pReset cReset g w φ c y hpd hp,
    high_marked_local_score_ratio π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) (fun l => hpd (e l))
      (fun l b => hp (e l) b)]
  have hprod (z : E) :
      (∏ i, pReset z i / p i) *
          ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
            ternaryMass a (coefficientRegression η g w φ c i) V (y i) =
      (∏ l : Fin r, pReset z (e l) / p (e l)) *
          ∏ l : Fin r, ternaryMass a (coefficientRegression η g w φ (cReset z) (e l)) V (y (e l)) /
            ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply prod_eq_prod_embedding e
    intro i hi
    grind [coefficientRegression, ternaryMass]
  have hsum : (∑ i, (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
      ternaryMass a (coefficientRegression η g w φ c i) V (y i))) =
      ∑ l : Fin r, (w (e l)) ^ 2 * (ternaryVarianceDerivative a (y (e l)) /
        ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l))) := sum_eq_sum_embedding e _ (fun i hi => by simp [hw i hi])
  simp_rw [mul_assoc, hprod, hsum]
  rfl

end
end NearlyMinimax
