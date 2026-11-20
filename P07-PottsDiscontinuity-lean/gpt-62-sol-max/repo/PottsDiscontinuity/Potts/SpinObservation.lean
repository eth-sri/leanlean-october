module

public import PottsDiscontinuity.Potts.PottsWeakLimit

/-! Finite observations of the actual Potts box measures. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

variable {A : Type*} [Fintype A]

/-- Transfer asymptotics of a finite observation sum to the extended spin laws. -/
theorem tendsto_pottsBox_observed
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1))
    (v : A → ℤ × ℤ) (ξ : A → Set.Icc 1 q) {a : ℕ → ℝ} {m : ℝ}
    (ha : Tendsto a atTop (𝓝 m))
    (he : ∀ n, 0 < n → ∀ hv : ∀ b, v b ∈ box n,
      (∑ σ : SpinConfiguration q (box n),
        if ∀ b, σ ⟨v b, hv b⟩ = ξ b then pottsProb q (box n) β i σ else 0) = a n) :
    Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real
      (spinObservationEvent q v ξ)) atTop (𝓝 m) := by
  apply ha.congr'
  filter_upwards [eventually_gt_atTop 0, eventually_all.mpr fun b => FK.eventually_mem_box (v b)] with n hn hv
  rw [pottsBoxProbabilityMeasure_observed q hq β hβ i n v hv ξ, he n hn hv]

end
end PottsDiscontinuity.Potts
