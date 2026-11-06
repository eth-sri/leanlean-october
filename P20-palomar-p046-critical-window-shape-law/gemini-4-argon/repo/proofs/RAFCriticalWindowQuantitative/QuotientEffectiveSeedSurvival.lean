module

public import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveBulk
public import proofs.RAFReactionQuotient.SeedApproximation
public import proofs.RAFCriticalWindowQuantitative.EffectiveSeedSurvival

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem effective_quotient_seed_survival (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    ∀ b : I, rationalParameter q hq.le hq1 ≤ b →
      quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ quotientSurvival b + (m : ENNReal)⁻¹ := by
  dsimp only
  have hbulk := effective_quotient_bulk q hq hq1 m (by omega)
  intro b hb
  refine ge_of_tendsto' ((quotient_escape_tendsto b).add_const (m : ENNReal)⁻¹) fun K => ?_
  apply le_of_tendsto (quotient_finite_seed_tendsto 2 b (actualBinaryWords _))
  filter_upwards [(tendsto_atTop.mp card_molecule_tendsto_atTop)
    (m*Fintype.card (Molecule (K+2))+1), eventually_ge_atTop 1] with N hlarge hN
  refine (quotient_same_field_seed_mass N _ m b).trans (add_le_add ?_ (hbulk b hb N hN))
  rw [quotient_escape_measure_eq]
  exact (measure_mono fun ω hω => exists_gt_of_card_ge hm hlarge hω).trans (quotient_capped_escape_le N K b)

end RAFCriticalWindowQuantitative
