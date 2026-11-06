module
public import OAI.NumberTheory.DirichletL.Descent.WholePriorityPrincipal

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open FirstPassCubeLabels SecondPassArithmetic

theorem first_whole_extracted_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι) (hb:b.Admissible) (C extra:Finset ι) (he:extra⊆b.support)
    (negative:Bool) (B:ℝ) (hB:0≤B)
    (h₁:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (h₂:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))≤
      B^2*primeProductNorm p C := by
  have hbits:(if negative then b.rightDivisor else b.leftDivisor)⊆b.support:=by
    cases negative
    · exact hb.1
    · exact hb.2
  have hs:extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)⊆b.support∪C:=by
    exact Finset.union_subset (he.trans Finset.subset_union_left)
      (Finset.union_subset_union hbits (Finset.Subset.refl C))
  apply (primeProductNorm_mono p hp hs).trans
  apply (primeProductNorm_union_le_mul p hp b.support C).trans
  exact mul_le_mul_of_nonneg_right (cubeCoordinates_radical_bound p hp b B hB h₁ h₂)
    (primeProductNorm_pos p hp C).le
