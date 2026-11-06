module

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerCanonical

@[expose] public section

namespace OAI

noncomputable section


open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns SevenEighths.InverseInitialEnergyCallerCanonical
namespace SevenEighths.InverseInitialEnergyCallerOpposite
local notation "Eis" => ActualEisensteinCubic.O

def negativeChild (c : InitialChild) : InitialChild := (c.1,c.2.1,-c.2.2)

theorem energy_neg_rows (T labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hneg : ∀ k∈rows,-k∈rows) (J : ℕ) (F : InitialChild→ℂ) :
    (∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (negativeChild (t,f,k))‖^2) =
    ∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (t,f,k)‖^2 := by
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  congr 1
  apply Finset.sum_bij (fun k _=>-k)
  · exact hneg
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,hneg b hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialEnergyCallerOpposite

end

end OAI
