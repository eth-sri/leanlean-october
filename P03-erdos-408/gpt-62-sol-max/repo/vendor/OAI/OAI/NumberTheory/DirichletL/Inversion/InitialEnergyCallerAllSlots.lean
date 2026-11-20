module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerBranch
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerMass

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerAllSlots
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [OAI.PrincipalFamily.Maximal p]
  (hcop:OAI.PrincipalFamily.Coprime p)
  (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

theorem rowMode_sum_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(u:Eisˣ)
    (hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(w:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z)=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  calc
    _=∑x∈S,∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [rowMode_eq_allocations p hp hcop hg hpr x (hdiv x hx) u (hu x hx)]
      simp only [Finset.mul_sum]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      exact Finset.sum_comm


end SevenEighths.InverseInitialEnergyCallerAllSlots

end

end OAI
