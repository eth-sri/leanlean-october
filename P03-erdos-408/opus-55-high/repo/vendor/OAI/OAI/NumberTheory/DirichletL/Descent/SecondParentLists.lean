module

public import OAI.NumberTheory.DirichletL.Descent.SecondPuncture

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped Classical
open FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def actualSecondRawInheritedPuncture {Jo Jn : ℕ} (m : ActualEisensteinCubic.O) (x : MarkedSecondSource ι Jo Jn) : ActualEisensteinCubic.O :=
  ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*b0Label p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    secondExpansionQuotient p x.second

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_parent_deleted_prime_killed {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (_hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (m : ActualEisensteinCubic.O) (i : ι)
    (hi : i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal ActualEisensteinCubic.O)∣x.quotient) :
    actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x∈Ideal.span {p i} := by
  rcases hi with hi|hi
  · have hv : ∀ j∈x.cube.support,0<x.cube.leftExponent j+x.cube.rightExponent j := by
      intro j hj
      simp only [CubeCoordinates.support,Finset.mem_union,Finsupp.mem_support_iff] at hj
      omega
    have hk := actual_second_extracted_support_killed p
      x.cube.support x.firstCommon x.second.sourceCommon x.second.divisor x.second.overlap
      (x.cube.support∪x.firstCommon) hE Finset.subset_union_left
      (fun j=>x.cube.leftExponent j+x.cube.rightExponent j) x.cube.leftBit x.cube.rightBit hv
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) i hi
    simpa only [actualSecondRawInheritedPuncture,actualSecondRawLabel,
      secondExpansionQuotient_of_subset p x.second hE] using hk
  · have hq : ConcretePrimeRowBridge.idealGenerator x.quotient∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp hi)
      have hmem : ConcretePrimeRowBridge.idealGenerator x.quotient∈
          Ideal.span {ConcretePrimeRowBridge.idealGenerator x.quotient} := by simp
      simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hmem
    unfold actualSecondRawInheritedPuncture
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq)))

end
end SevenEighths.InverseMoment

end OAI
