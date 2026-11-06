module

public import OAI.NumberTheory.DirichletL.Descent.SecondWholeTail

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_whole_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal] (G E S T : Finset ι)
    (hEG : E ⊆ G) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤ L^2 := by
  have hE := primeProductNorm_mono p hp hEG
  have hE0 := (primeProductNorm_pos p hp E).le
  have hS0 := (primeProductNorm_pos p hp S).le
  have hT0 := (primeProductNorm_pos p hp T).le
  rw [primeProductNorm_union p G S hGS] at hS
  rw [primeProductNorm_union p G T hGT] at hT
  calc
    _ ≤ (primeProductNorm p G)^2 * (primeProductNorm p S * primeProductNorm p T) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE0 hE 2) (mul_nonneg hS0 hT0)
    _ = (primeProductNorm p G * primeProductNorm p S) *
      (primeProductNorm p G * primeProductNorm p T) := by ring
    _ ≤ L*L := mul_le_mul hS hT (mul_nonneg (primeProductNorm_pos p hp G).le hT0) hL
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
