module
public import OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw CenteredMomentDivisorAllocation CenteredMomentDivisorRetained CenteredMomentEligibleEnergy CenteredMomentLiveCapacity CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem formal_reduction_pays_slots (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z:ℝ)(hZ:1<Z)(P:ι→ℝ)(hP:∀i,1≤P i):
    (∑i,Real.logb Z (P i))-remainingLogs D a Z P≤
      Real.logb Z (formalReductionFactor D a P) := by
  have hp:∀i,0<P i:=fun i=>zero_lt_one.trans_le (hP i)
  have hs:=congrArg (Real.logb Z) (split_slot_product D a P)
  rw [Real.logb_mul (Finset.prod_pos (fun i _=>hp i)).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne')] at hs
  rw [formalReductionFactor,Real.logb_mul (selectedNorm_pos D a).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne')]
  have hn:=Real.logb_nonneg hZ (selectedNorm_ge_one D a)
  dsimp only [remainingLogs]
  linarith

theorem affine_reduction_le_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z κ:ℝ)(hZ:1<Z)(hκ:0≤κ)(P:ι→ℝ)(hP:∀i,1≤P i):
    -Real.logb Z (formalReductionFactor D a P)+(6*κ-1)*remainingLogs D a Z P≤
      (6*κ-1)*(∑i,Real.logb Z (P i)) := by
  have hred:=formal_reduction_pays_slots D a Z hZ P hP
  have hrem:=remainingLogs_le D a Z hZ P hP
  nlinarith
