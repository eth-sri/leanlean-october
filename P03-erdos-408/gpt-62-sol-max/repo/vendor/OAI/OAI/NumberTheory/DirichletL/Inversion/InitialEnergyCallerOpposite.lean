module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerCanonical

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum SevenEighths.InverseMoment
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialQuotientGeometry
open SevenEighths.InverseInitialClippedColumns SevenEighths.InverseInitialEnergyCallerCanonical
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
  · simp
  · intro b hb
    exact ⟨-b,hneg b hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [OAI.PrincipalFamily.Maximal p]
  (hcop : OAI.PrincipalFamily.Coprime p)
  (hg : OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

end SevenEighths.InverseInitialEnergyCallerOpposite

end

end OAI
