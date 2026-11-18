module
public import OAI.NumberTheory.DirichletL.Descent.SecondWholeKernel
public import OAI.NumberTheory.DirichletL.Descent.SecondPass

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem secondChildKernelPair_separated_marked {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)*W₁ (primeProductNorm p S/X₁)) *
        (primeMark slots₂ lists₂ a₂ (A₂ ∪ T)*W₂ (primeProductNorm p T/X₂))) =
      star (canonicalMarkedSplit p hp hcop hg F V A₁ Ψ₁ m r c d e k₁ slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ Ψ₂ m r c d e k₂ slots₂ lists₂ a₂ W₂ X₂ := by
  have hs (Ψ : Eis →* ℂ) (A : Finset ι) (k : Eis) (slots : Finset σ)
      (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :=
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ m r c d e k slots lists a W X
  unfold canonicalMarkedSplit
  rw [← hs Ψ₁ A₁ k₁ slots₁ lists₁ a₁ W₁ X₁, ← hs Ψ₂ A₂ k₂ slots₂ lists₂ a₂ W₂ X₂]
  unfold secondChildKernelPair secondChildSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  simp only [secondChildColumn,star_mul,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI
