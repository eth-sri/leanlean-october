module
public import OAI.NumberTheory.DirichletL.Moments.CommonRadialData

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialSource
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 def sourceEnergy (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O) : ℝ :=
  let Q:=finiteColumns (Fintype.piFinset s.pools)
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
    (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
    (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)

 def commonCost (s:Input ι) (C:Ideal O) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*
    (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ))

 theorem live_source_eq (s:Input ι) (r:Radial) (C R L:Ideal O) (B:actualAllocations s.pools C) :
    sourceRestrictedEnergy r.keep
      (finiteColumns (liveBox s.pools B.val (alloc_ne s C B)))
      (finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
        (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff s.η s.t) r.profile r.scale/remainingRaw B.val (s.X₁*s.X₂) s.P=
      energy (commonData s C R B) r L := by
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hcov₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hcov₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hcov₁ hcov₂
  have hh:=CenteredMomentRadialSourceDictionary.actual_source_energy (commonData s C R B) r
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) s.X₁ s.X₂ s.Y₁ s.Y₂
    rfl rfl rfl rfl rfl rfl hcov₁ hcov₂
  refine Eq.trans ?_ hh
  apply congrArg₂ (fun x y : ℝ => x / y)
  · simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  · dsimp only [remainingRaw,plainNorm,commonData]
    ring

end SevenEighths.CenteredMomentCommonRadialSource

end

end OAI
