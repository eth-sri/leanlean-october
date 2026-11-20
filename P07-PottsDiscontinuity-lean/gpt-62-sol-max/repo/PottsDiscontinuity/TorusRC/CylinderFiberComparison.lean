module

public import PottsDiscontinuity.TorusRC.CylinderFiberBridge
public import PottsDiscontinuity.FK.VolumeComparison
public import PottsDiscontinuity.TorusRC.Association
public import PottsDiscontinuity.FK.PositiveAssociation

/-! # Conditional comparison and association on a torus edge fiber -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

noncomputable local instance torusFiberComparisonRemainingFintype
    (hN : Even N) (hM : Even M)
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM) R) := Fintype.ofFinite _

noncomputable section

/-- Event probability of a PMF, expressed as its real expectation. -/
def torusRCFiberEventProbability {α : Type*} [Fintype α] (p : PMF α) (E : Set α) : ℝ :=
  FK.FiniteProbability.expectation p (E.indicator (fun _ => (1 : ℝ)))

/-- On a fixed exterior-edge fiber, any increasing event has probability at
least its free-boundary probability on the same retained edge set. -/
theorem torusRCFiberEventProbability_ge_free (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
    (E : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R))
    (hE : IsUpperSet E) :
    torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) E ≥
      torusRCFiberEventProbability
        (FK.remainingLaw (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
          (FK.BoundaryCondition.free ∅) R) E := by
  rw [torusRCFiberLaw_eq_remainingLaw]
  exact FK.remainingLaw_boundary_comparison (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
    (FK.BoundaryCondition.free ∅) _ (FK.boundary_le_frozenBoundary _ H.val) R _
    (Set.indicator_nonneg fun _ _ => zero_le_one) (FK.event_indicator_monotone hE)

theorem torusRCFiberEventProbability_nonneg {α : Type*} [Fintype α]
    (p : PMF α) (E : Set α) : 0 ≤ torusRCFiberEventProbability p E := by
  apply FK.FiniteProbability.expectation_nonneg
  grind [Set.indicator]

theorem torusRCFiberEventProbability_mono {α : Type*} [Fintype α]
    (p : PMF α) {E F : Set α} (h : E ⊆ F) :
    torusRCFiberEventProbability p E ≤ torusRCFiberEventProbability p F :=
  FK.FiniteProbability.expectation_mono _ _ _ fun _ =>
    Set.indicator_le_indicator_apply_of_subset h zero_le_one

theorem torusRCFiberEventProbability_inter_ge_mul
    (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (q : Set.Ici (1 : ℝ)) (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
    (E F : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R))
    (hE : IsUpperSet E) (hF : IsUpperSet F) :
    torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) E *
      torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) F ≤
    torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) (E ∩ F) := by
  rw [torusRCFiberLaw_eq_remainingLaw]
  have h := FK.remainingLaw_positive_association (fullDiamondGraph hN hM)
    (torusRCBridgeParameters q) (FK.frozenBoundary (FK.BoundaryCondition.free ∅) H.val) R
    (E.indicator fun _ => (1 : ℝ)) (F.indicator fun _ => (1 : ℝ))
    (Set.indicator_nonneg fun _ _ => zero_le_one) (Set.indicator_nonneg fun _ _ => zero_le_one)
    (FK.event_indicator_monotone hE) (FK.event_indicator_monotone hF)
  simpa only [torusRCFiberEventProbability, FK.FiniteProbability.expectation, ← Set.inter_indicator_mul, one_mul] using h

/-- FKG iterated over a finite family of increasing events on a fixed
conditioned torus fiber. Each factor can be replaced by a lower bound for its
free-boundary probability on the same retained edge set. -/
theorem torusRCFiberEventProbability_finset_inter_ge_prod
    {ι : Type*} [DecidableEq ι] (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
    (s : Finset ι)
    (E : ι → Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R))
    (p : ι → ℝ)
    (hE : ∀ i, IsUpperSet (E i))
    (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp : ∀ i ∈ s, p i ≤ torusRCFiberEventProbability
      (FK.remainingLaw (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) R) (E i)) :
    (∏ i ∈ s, p i) ≤
      torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
        {A | ∀ i ∈ s, A ∈ E i} := by
  let P := torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
  have h₁ : P Set.univ = 1 := by simp [P, torusRCFiberEventProbability, FK.FiniteProbability.expectation_const]
  refine (Finset.prod_le_prod₀ hp0 ?_).trans
    (event_product_le_inter P h₁ (torusRCFiberEventProbability_nonneg _)
      (torusRCFiberEventProbability_inter_ge_mul hN hM hN4 hM4 q R H) s E hE)
  exact fun i hi => (hp i hi).trans (torusRCFiberEventProbability_ge_free hN hM hN4 hM4 q R H _ (hE i))

end

end PottsDiscontinuity.TorusRC
