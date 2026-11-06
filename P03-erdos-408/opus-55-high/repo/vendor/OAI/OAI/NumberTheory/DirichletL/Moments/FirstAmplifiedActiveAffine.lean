module

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedActiveCapacitySource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstAmplifiedActiveAffine
open HeckeFamily
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput
open CenteredMomentFirstAnnularInput CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem active_error_slot_logs_le (s : Input ι) (C R : Ideal HeckeFamily.O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal HeckeFamily.O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      ∑i,Real.logb Z (s.P i) := by
  have hp : ∀i,1≤(activeInput (child s C R B τ t)).P i := fun i=>hP i.val
  have hs := common_slot_logs_le (activeInput (child s C R B τ t)) (Q^k) Bp Z hZ hp
  exact hs.trans (common_slot_logs_le s C B Z hZ hP)

theorem active_error_parent_affine (s : Input ι) (C R : Ideal HeckeFamily.O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal HeckeFamily.O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z κ M : ℝ) (hZ : 1<Z) (hκ : 1/6≤κ) (hP : ∀i,1≤s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M) :
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤M := by
  have hh := input_affine_capacity s Z κ M hZ hcap
  have hs := active_error_slot_logs_le s C R B τ t Q k Bp υ v Z hZ hP
  nlinarith

end SevenEighths.CenteredMomentFirstAmplifiedActiveAffine

end

end OAI
