
import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
import proofs.HordijkSteelThreshold.WordEffectiveClosure


namespace HordijkSteelThreshold
open MeasureTheory RAF.Polymer RAF.Concrete

variable {Ω : Type*} [MeasurableSpace Ω]

variable (N L m : ℕ) (μ : Measure Ω) (A : Ω → Finset (Reaction N))

theorem food_seed_mass_bound  :
    μ {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (A ω)} ≤
      μ {ω | NearFull m (temporaryReactionClosure 2 (A ω))} +
      μ {ω | MassDeficit m (temporaryReactionClosure L (A ω))} := by
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hseed
  by_cases hb : MassDeficit m (temporaryReactionClosure L (A ω))
  · exact Or.inr hb
  · left
    
    exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card (by
      apply temporaryReactionClosure_induction (A ω) (fun y => y ∈ temporaryReactionClosure 2 (A ω)) ?_
        (fun r hr => (temporaryReactionClosure_rules (A ω) r hr).1)
        fun r hr => (temporaryReactionClosure_rules (A ω) r hr).2
      grind [cases Bool, binaryFood])))


end HordijkSteelThreshold
