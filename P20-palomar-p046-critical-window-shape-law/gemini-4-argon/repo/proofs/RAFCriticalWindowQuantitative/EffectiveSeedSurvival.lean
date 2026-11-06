module

public import proofs.RAFCriticalWindowQuantitative.EffectiveBulk
public import proofs.HordijkSteelThreshold.SeedSurvivalApproximation

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical Filter MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem exists_gt_of_card_ge {N K m : ℕ} {C : Finset (Molecule N)} (hm : 2 ≤ m)
    (hlarge : m * Fintype.card (Molecule (K+2)) + 1 ≤ Fintype.card (Molecule N))
    (hC : (m-1) * Fintype.card (Molecule N) ≤ m * C.card) :
    ∃ x ∈ C, K+2 < molLength x := by
  by_contra h
  have hs : C ⊆ binaryFood N (K+2) := fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt fun hl => h ⟨x, hx, hl⟩⟩
  have hc := (Finset.card_le_card hs).trans (binaryFood_card_le_cutoff N (K+2))
  have hmult : Fintype.card (Molecule N) ≤ (m-1)*Fintype.card (Molecule N) := by
    simpa using Nat.mul_le_mul_right (Fintype.card (Molecule N)) (show 1 ≤ m-1 by omega)
  nlinarith

theorem effective_seed_probability_le_survival (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) :
    let b0 := rationalParameter q hq.le hq1
    let L := 10 * seedIndex q hq hq1 m
    ∀ b : I, b0 ≤ b →
      infiniteStaticMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ staticSurvival b + (m : ENNReal)⁻¹ := by
  dsimp only
  let L := 10 * seedIndex q hq hq1 m
  have hbulk := effective_static_bulk q hq hq1 m (by omega)
  intro b hb
  refine ge_of_tendsto' ((finite_static_escape_probability_tendsto b).add_const (m : ENNReal)⁻¹) fun K => ?_
  apply le_of_tendsto (finite_static_seed_probability_tendsto 2 b (actualBinaryWords L))
  filter_upwards [(tendsto_atTop.mp card_molecule_tendsto_atTop)
    (m*Fintype.card (Molecule (K+2))+1), eventually_ge_atTop 1] with N hlarge hN
  refine (same_field_seed_mass_bound N L m b).trans (add_le_add ?_ ?_)
  · rw [finite_static_escape_measure_eq]
    exact (measure_mono fun ω hω => exists_gt_of_card_ge hm hlarge hω).trans (static_capped_escape_le N K b)
  · exact (static_decreasing_event_mono N hb _ fun S T hST hT =>
      (Nat.mul_le_mul_left m (Finset.card_le_card (temporaryReactionClosure_mono hST))).trans_lt hT).trans (hbulk N hN)

end RAFCriticalWindowQuantitative
