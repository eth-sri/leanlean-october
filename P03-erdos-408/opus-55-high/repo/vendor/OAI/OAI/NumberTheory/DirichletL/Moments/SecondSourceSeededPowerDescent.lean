module

public import OAI.NumberTheory.DirichletL.Moments.SecondSourcePowerDescent
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailSeed
public import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalLiveSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourceSeededPowerDescent
open HeckeFamily
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _




open CenteredMomentSecondSourcePowerDescent

def seededFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo seedNorm : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  let a:=physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W
  ![a 0,a 1,a 2,a 3/seedNorm]

end SevenEighths.CenteredMomentSecondSourceSeededPowerDescent

end

end OAI
