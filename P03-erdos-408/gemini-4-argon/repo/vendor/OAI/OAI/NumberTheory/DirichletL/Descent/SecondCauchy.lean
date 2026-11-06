module

public import OAI.NumberTheory.DirichletL.Descent.TripleMass
public import OAI.NumberTheory.DirichletL.Descent.Canonical

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondLabelEnergy (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : ℝ :=
  ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(9+4*K) *
    ∑ k ∈ rows, ‖F (γ,f,k)‖^2

lemma secondLabelEnergy_nonneg (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : 0 ≤ secondLabelEnergy K labels rows F γ := by
  unfold secondLabelEnergy; positivity

def secondCanonicalPolynomial {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

end
end SevenEighths.InverseMoment

end OAI
