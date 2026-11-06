module
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSource
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedCanonical
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSector
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→ Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

section
variable (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1) (x:Source (ι:=ι) 0) (hdiv:x.divisor⊆x.common) (u:Eisˣ) (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u) (pool:Finset ι) (Ψ:Eis→*ℂ) (j:Eis) (slots:Finset σ) (lists:σ→ Finset ι) (a:σ→ι→ℂ) (W:ℝ→ℂ) (Z D B v:ℝ)
include hpr x hdiv u hu pool Ψ j slots lists a W Z D B v
theorem markedModeColumn_sector :
    markedModeColumn p hp hcop hg hpr pool Ψ j x.frequency x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z ^(columnCenter D B v))
          (initialChild (toTuple p (sectorSource u x))) := by
  pm_3809 markedModeColumn hu J hJ
  pm_94 child initialChild toTuple sectorSource sourceTuple
  rw [source_quotient p hp x.common x.divisor hdiv]
  rfl

theorem markedModeColumn_negative_sector :
    markedModeColumn p hp hcop hg hpr pool Ψ j (-x.frequency) x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z ^(columnCenter D B v))
          (negativeChild (initialChild (toTuple p (sectorSource u x)))) := by
  pm_3809 markedModeColumn hu J hJ
  pm_382 child negativeChild initialChild toTuple sectorSource sourceTuple
  rw [source_quotient p hp x.common x.divisor hdiv]
  simp only [quotient,sourcePoint,mul_neg]
end

end SevenEighths.InverseInitialEnergyCallerSector

end

end OAI
