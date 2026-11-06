module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedActiveCapacitySource

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedActiveAffine
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentFirstAnnularInput CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAmplifiedActiveCapacitySource CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands

variable {ι : Type*} [Fintype ι]


theorem active_error_slot_logs_le (s : Input ι)  C R 
     B   τ   t 
     Q   k 
     Bp 
     υ   v Z  (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      ∑i,Real.logb Z (s.P i) := LE.le.trans (OAI.SevenEighths.CenteredMomentAllocatedChildCapacity.common_slot_logs_le (OAI.SevenEighths.CenteredMomentFirstAnnularInput.activeInput (OAI.SevenEighths.CenteredMomentAmplificationChildInput.child s C R B τ t)) (Q ^ k) Bp Z hZ fun i => hP ↑i) (OAI.SevenEighths.CenteredMomentAllocatedChildCapacity.common_slot_logs_le s C B Z hZ hP)

theorem active_error_parent_affine (s : Input ι)  C R 
     B   τ   t 
     Q   k 
     Bp 
     υ   v Z κ M  (hZ : 1<Z) (hκ : 1/6≤κ) (hP : ∀i,1≤s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M) :
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤M := by
  have hh := input_affine_capacity s Z κ M hZ hcap
  have hs := active_error_slot_logs_le s C R B τ t Q k Bp υ v Z hZ hP
  have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0≤6*κ-1)
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedActiveAffine

end

end OAI
