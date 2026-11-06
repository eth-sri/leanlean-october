module
public import Mathlib

public import PottsDiscontinuity.TorusRC.CylinderFiberBridge
public import PottsDiscontinuity.FK.VolumeComparison

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

section

variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ)) (R : FK.Configuration (fullDiamondGraph hN hM)) (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
include hN4 hM4 q H

/-- For every fixed state of the removed torus edges, the conditional law on
the remaining edges dominates the free-boundary remaining law on that same
edge set for nonnegative increasing observables. -/
theorem torusRCFiberLaw_expectation_ge_free 
    (f : FK.RemainingConfiguration (fullDiamondGraph hN hM) R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    FK.FiniteProbability.expectation
        (torusRCFiberLaw hN hM hN4 hM4 q R H) f ≥
      FK.FiniteProbability.expectation
        (FK.remainingLaw (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
          (FK.BoundaryCondition.free ∅) R) f := by
  rw [torusRCFiberLaw_eq_remainingLaw hN hM hN4 hM4 q R H]
  exact FK.remainingLaw_boundary_comparison (fullDiamondGraph hN hM)
    (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅)
    (FK.frozenBoundary (FK.BoundaryCondition.free ∅) H.val)
    (FK.boundary_le_frozenBoundary (FK.BoundaryCondition.free ∅) H.val)
    R f hf0 hf

/-- A fixed torus fiber has positive association for nonnegative increasing
observables, inherited from its exact FK remaining-edge law. -/
theorem torusRCFiberLaw_positive_association 
    (f g : FK.RemainingConfiguration (fullDiamondGraph hN hM) R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) :
    FK.FiniteProbability.expectation
        (torusRCFiberLaw hN hM hN4 hM4 q R H) f *
      FK.FiniteProbability.expectation
        (torusRCFiberLaw hN hM hN4 hM4 q R H) g ≤
      FK.FiniteProbability.expectation
        (torusRCFiberLaw hN hM hN4 hM4 q R H)  fun A => f A * g A  := by
  rw [torusRCFiberLaw_eq_remainingLaw hN hM hN4 hM4 q R H]
  exact FK.remainingLaw_positive_association (fullDiamondGraph hN hM)
    (torusRCBridgeParameters q) (FK.frozenBoundary (FK.BoundaryCondition.free ∅) H.val)
    R f g hf0 hg0 hf hg

end

/-- Event probability of a PMF, expressed as its real expectation. -/
def torusRCFiberEventProbability {α : Type*} [Fintype α]
    (p : PMF α) (E : Set α)  :=
  FK.FiniteProbability.expectation p (E.indicator  fun _ => (1 : ℝ) )

private theorem expectation_indicator_mul_indicator {α : Type*} [Fintype α]
    (p : PMF α) (E F : Set α) :
    FK.FiniteProbability.expectation p
        (fun A => E.indicator (fun _ => (1 : ℝ)) A *
          F.indicator (fun _ => (1 : ℝ)) A) =
      torusRCFiberEventProbability p (E ∩ F) := by
  
  congr 1
  funext A
  by_cases hE : A ∈ E <;> by_cases hF : A ∈ F <;>
    simp [hE, hF]

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
  apply torusRCFiberLaw_expectation_ge_free hN hM hN4 hM4 q R H
  · intro A
    by_cases hA : A ∈ E <;> simp [hA]
  · intro A B hAB
    by_cases hA : A ∈ E
    · simp [hA, hE hAB hA]
    · by_cases hB : B ∈ E <;> simp [hA, hB]

theorem torusRCFiberEventProbability_nonneg {α : Type*} [Fintype α]
    (p : PMF α) (E : Set α) : 0 ≤ torusRCFiberEventProbability p E := by
  apply FK.FiniteProbability.expectation_nonneg
  intro A
  by_cases hA : A ∈ E <;> simp [hA]

theorem torusRCFiberEventProbability_inter_ge_mul
    (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (q : Set.Ici (1 : ℝ)) (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
    (E F : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R))
    (hE : IsUpperSet E) (hF : IsUpperSet F) :
    torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) E *
      torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) F ≤
    torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) (E ∩ F) := by
  have hindicator (S : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R))
      (hS : IsUpperSet S) :
      Monotone (S.indicator  fun _ => (1 : ℝ) ) := by
    intro A B hAB
    by_cases hA : A ∈ S
    · simp [hA, hS hAB hA]
    · by_cases hB : B ∈ S <;> simp [hA, hB]
  
  
  rw [← expectation_indicator_mul_indicator]
  exact torusRCFiberLaw_positive_association hN hM hN4 hM4 q R H
    (E.indicator  fun _ => 1 ) (F.indicator  fun _ => 1 )
    (by
       intro A
       by_cases hA : A ∈ E <;> simp [hA]) (by
           intro A
           by_cases hA : A ∈ F <;> simp [hA]) (hindicator E hE) (hindicator F hF)

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
     ∏ i ∈ s, p i  ≤
      torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
        {A | ∀ i ∈ s, A ∈ E i} := by
  
  induction s using Finset.induction_on with
  | empty =>
      simp [torusRCFiberEventProbability, FK.FiniteProbability.expectation_const]
  | @insert i s his ih =>
      have hiF : p i ≤ torusRCFiberEventProbability
          (torusRCFiberLaw hN hM hN4 hM4 q R H) (E i) := by
        grind [torusRCFiberEventProbability_ge_free]
      have hs0 : ∀ j ∈ s, 0 ≤ p j := by
        simp_all
      
      
      have hmul := mul_le_mul hiF (ih hs0 (by
                                                         simp_all))
        (Finset.prod_nonneg hs0)
        (torusRCFiberEventProbability_nonneg _ (E i))
      
      
      have hset :  {A : FK.RemainingConfiguration (fullDiamondGraph hN hM) R |
          ∀ j ∈ insert i s, A ∈ E j}  =
           E i ∩ {A | ∀ j ∈ s, A ∈ E j}  := by
        ext A
        all_goals simp_all
      rw [Finset.prod_insert his]
      calc
        p i *  ∏ j ∈ s, p j  ≤
            torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
              (E i) * torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
                {A | ∀ j ∈ s, A ∈ E j} := hmul
        _ ≤ torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
              (E i ∩ {A | ∀ j ∈ s, A ∈ E j}) :=  torusRCFiberEventProbability_inter_ge_mul
                                                   hN hM hN4 hM4 q R H (E i)
                                                   {A | ∀ j ∈ s, A ∈ E j} (hE i) (by
                                                                                    intro A B hAB hA j hj
                                                                                    exact hE j hAB (hA j hj)) 
        _ = torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
              {A | ∀ j ∈ insert i s, A ∈ E j} := by rw [hset]

end

end PottsDiscontinuity.TorusRC
