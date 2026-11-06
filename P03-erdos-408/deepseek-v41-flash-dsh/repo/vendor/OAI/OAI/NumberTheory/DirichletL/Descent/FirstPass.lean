module

public import OAI.NumberTheory.DirichletL.Descent.SecondPass

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_marked_priority
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (r : FirstCoreIndex) (t : ℝ) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (fun U => primeMark slots lists a (A ∪ U) * H U) V y c d r t z =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ D) *
      firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (fun U => primeMark (slots \ J) (fun i => lists i \ (A ∪ D)) a U * H U)
        V y c d r t z := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have he := primeMark_priority slots lists a (A ∪ D) U
  simp only [primeMark_residual_lists] at he
  have hset : (D ∪ U) \ (A ∪ D) = U \ (A ∪ D) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp only [secondInputCoefficient, firstCoreTest, ← Finset.union_assoc]
  rw [he]
  simp only [Finset.sum_mul, Finset.mul_sum, ← primeMark_residual_lists, hset]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

end
end SevenEighths.InverseMoment

end OAI
