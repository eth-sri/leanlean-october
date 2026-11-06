module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory

theorem measure_pool_deficit_le {Ω X : Type*} [Fintype Ω] [Fintype X]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [DecidableEq X]
    (μ : Measure Ω) (bad pool : Ω → Finset X) (root : X)
    (hcover : ∀ ω, root ∉ bad ω → ∀ x, x ∉ bad ω → x ∈ pool ω)
    (δ : ENNReal) (hbad : ∀ x, μ {ω | x ∈ bad ω} ≤ δ)
    (k : ℕ) (hk : 0 < k) :
    μ {ω | (pool ω).card + k ≤ Fintype.card X} ≤
      δ + (Fintype.card X : ENNReal) * δ / k := by
  classical
  have hsub : {ω | (pool ω).card + k ≤ Fintype.card X} ⊆
      {ω | root ∈ bad ω} ∪ {ω | k ≤ (bad ω).card} := fun ω (hω : (pool ω).card + k ≤ _) =>
    if hr : root ∈ bad ω then Or.inl hr
    else Or.inr <| by
      change k ≤ (bad ω).card
      have hcard : Fintype.card X ≤ (bad ω).card + (pool ω).card := by
        rw [← Finset.card_univ, ← Finset.eq_univ_of_forall fun x =>
          if hx : x ∈ bad ω then Finset.mem_union_left _ hx else Finset.mem_union_right _ (hcover ω hr x hx)]
        exact Finset.card_union_le _ _
      omega
  have hlint : (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) = ∑ x : X, μ {ω | x ∈ bad ω} := by
    simp_rw [show ∀ ω, ((bad ω).card : ENNReal) = ∑ x : X, Set.indicator {ω | x ∈ bad ω} 1 ω by
      intro ω; simp [Set.indicator_apply]]
    rw [lintegral_finsetSum Finset.univ fun _ _ => measurable_of_finite _]
    exact Finset.sum_congr rfl fun x _ => lintegral_indicator_one (Set.toFinite _).measurableSet
  have hmark := meas_ge_le_lintegral_div (μ := μ) (f := fun ω => ((bad ω).card : ENNReal))
    (measurable_of_finite _).aemeasurable (ε := (k : ENNReal)) (by exact_mod_cast hk.ne') (by simp)
  simp only [Nat.cast_le, hlint] at hmark
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (hbad root)
    (hmark.trans (ENNReal.div_le_div_right ?_ _))))
  exact (Finset.sum_le_sum (g := fun _ => δ) fun x _ => hbad x).trans_eq (by simp)

end HordijkSteelThreshold
