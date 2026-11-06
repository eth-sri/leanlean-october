module

public import OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment
public import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem secondInputCoefficient_old_divisor_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m c d : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondInputCoefficient p hg Ψ (m*d) c d H S = secondInputCoefficient p hg Ψ m c d H S := by
  rw [secondInputCoefficient_fixed_mask p hg Ψ m d c d H S]
  have hd := row_power_mul_mask_power (fun i => Ideal.span {p i}) hg S d 1 1 (by decide)
  simp only [pow_one] at hd
  unfold secondInputCoefficient
  grind

theorem inputConjugateRow_old_divisor_mask (F : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m c d : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (k : ActualEisensteinCubic.O) :
    inputConjugateRow p hg F Ψ (m*d) c d H k = inputConjugateRow p hg F Ψ m c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient_old_divisor_mask]

theorem inputConjugateRow_puncture_span (F : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m₁ m₂ c d : ActualEisensteinCubic.O)
    (hspan : Ideal.span {m₁} = (Ideal.span {m₂} : Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (k : ActualEisensteinCubic.O) :
    inputConjugateRow p hg F Ψ m₁ c d H k = inputConjugateRow p hg F Ψ m₂ c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient,
    rowCoprimeMask_eq_of_span_eq (fun i => Ideal.span {p i}) _ hspan]

theorem fresh_input_parent_mask {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (F D : Finset ι) (hq : parent.quotient = sourceIdeal p D)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (H : Finset ι → ℂ) (k : ActualEisensteinCubic.O) :
    inputConjugateRow p hg F Ψ
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k := by
  rw [←inputConjugateRow_old_divisor_mask]
  apply inputConjugateRow_puncture_span
  let b := b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit
  let d := secondParentDivisor p parent
  change Ideal.span {((m*b)*(∏ i∈D,p i))*d} =
    (Ideal.span {(m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d} : Ideal ActualEisensteinCubic.O)
  rw [show ((m*b)*(∏ i∈D,p i))*d = (m*b*d)*(∏ i∈D,p i) by ring,
    show (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d =
      (m*b*d)*ConcretePrimeRowBridge.idealGenerator parent.quotient by ring]
  simp only [←Ideal.span_singleton_mul_span_singleton,
    ConcretePrimeRowBridge.span_idealGenerator,hq,sourceIdeal]

end
end SevenEighths.InverseMoment

end OAI
