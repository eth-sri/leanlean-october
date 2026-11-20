module

public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.Potts.ColourKernelPartitions
public import PottsDiscontinuity.Potts.GhostConnectionLaw
public import PottsDiscontinuity.Potts.FinitePartitionLimits
public import PottsDiscontinuity.Potts.GhostCylinder

/-! Exact literal Potts cylinders as expectations of marked connection partitions. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

variable {A : Type*} [Fintype A]

omit [Fintype A] in
private theorem restored_observedWiredPartition (n : ℕ) (hn : 0 < n)
    (v : A → ℤ × ℤ) (hv : ∀ a, v a ∈ box n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    observedWiredPartition (Option.map v) n
      (openExtension (box (n + 1)) (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η))) =
    (ghostOpenGraph (box n) ω).reachableSetoid.comap
      (markedMap (fun a => some (⟨v a, hv a⟩ : ↥(box n : Set (ℤ × ℤ)))) none) := by
  rw [observedWiredPartition, localWiredSetoid, ← wiredObservationGraph_eq,
    boxObservation_openExtension_self, restored_wiredObservation_reachableSetoid,
    ← Setoid.comap_comp, ← Setoid.comap_comp]
  congr 1
  funext a
  simp only [Function.comp_apply, collapseOuterGhost_projection]
  cases a with
  | none => rfl
  | some a => simp [boxGhostProjection, hv a, markedMap]

theorem potts_ghost_cylinder_eq_partitionExpectation
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (n : ℕ) (hn : 0 < n) (v : A → ℤ × ℤ) (hv : ∀ a, v a ∈ box n) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q (box n),
      if ∀ a, σ ⟨v a, hv a⟩ = ξ a then pottsProb q (box n) β i σ else 0) =
    partitionExpectation (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure
      (observedWiredPartition (Option.map v) n)
      (fun R => pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) := by
  let vf : A → ↥(box n : Set (ℤ × ℤ)) := fun a => ⟨v a, hv a⟩
  refine Eq.trans ?_ ((pottsProb_ghost_cylinder q hq (box n) β i hi vf ξ).trans ?_)
  · apply Finset.sum_congr
    · rfl
    grind
  symm
  change partitionExpectation (((conditionedOuterLaw (fkParameters q hq β hβ) n).map
    (openExtension (box (n + 1)))).toMeasure) (observedWiredPartition (Option.map v) n) _ = _
  rw [partitionExpectation_map _ _ measurable_from_top _ _ (by
    intro a b
    simpa only [wiredDataEvent, Finset.mem_singleton, forall_eq] using!
      (wiredDataEvent_isClopen (n + 1) {(Option.map v a, Option.map v b)}).isOpen.measurableSet)]
  let G (ω : LiteralBond (box n) → Bool) :=
    (ghostOpenGraph (box n) ω).reachableSetoid.comap (markedMap (some ∘ vf) none)
  unfold partitionExpectation
  have h (R : Setoid (Option A)) := conditionedOuterLaw_event_eq_ghost q hq β hβ n hn
    {C | observedWiredPartition (Option.map v) n (openExtension (box (n + 1)) C) = R}
    {ω | G ω = R} (fun ω η => by
      simp only [Set.mem_ofPred_eq, restored_observedWiredPartition n hn v hv]
      rfl)
  simp_rw [Function.comp_apply, h, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr
  · ext ω; simp
  · intro ω _
    rw [Finset.sum_eq_single (G ω)]
    · simpa using congrArg (fun c : ℝ => ghostRCProbability q (box n) β ω * c)
        (pinnedClusterCylinderProbability_factor (ghostOpenGraph (box n) ω).reachableSetoid
          (some ∘ vf) ξ none (boundaryColor q i hi)).symm
    · intro R _ hR
      simp [hR.symm]
    · simp

end
end PottsDiscontinuity.Potts
