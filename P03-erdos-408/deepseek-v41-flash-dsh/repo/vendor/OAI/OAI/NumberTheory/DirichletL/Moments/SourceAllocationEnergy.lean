module

public import OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn
public import OAI.NumberTheory.DirichletL.Moments.GaussEnergy

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentSourceAllocationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

 theorem gaussPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*gaussPolynomial S a ha (d B) z := by
  simp only [gaussPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentSourceAllocationEnergy

end

end OAI
