module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.Active

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentPrimitive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

def primitiveCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal ActualEisensteinCubic.O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) :
    MulChar (Residue (finitePrimeModulus P)) ℂ :=
  crtCharacter ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
    (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => actualSextic (P i) (hg i) ^ j i)

section
variable {ι : Type*} [Fintype ι] (P : ι → Ideal ActualEisensteinCubic.O) [∀ i, (P i).IsMaximal] (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ)
include ι P hcop hg j



@[simp] theorem primitiveCharacter_mk    
       
     
         x  :
    primitiveCharacter P hcop hg j (Ideal.Quotient.mk _ x) =
      finiteSexticRow P hg j x := by
  rfl

end

lemma sqrt_absNorm  r  :
    Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) = ‖eisEmbedding r‖ := by
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

end SevenEighths.CenteredMomentPrimitive
end

end OAI
