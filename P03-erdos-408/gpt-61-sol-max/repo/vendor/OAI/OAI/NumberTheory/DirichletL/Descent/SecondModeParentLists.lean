module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.SecondParentLists
public import OAI.NumberTheory.DirichletL.Descent.SecondModeCanonical

@[expose] public section

namespace OAI


open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseInitialArithmetic CompletedGauss InverseSecondFibers JointLogSeparation

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
section
variable (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible) (hE : x.second.divisor⊆x.second.sourceCommon) (u v : ActualEisensteinCubic.Oˣ) (deleted : Finset ι) (hdeleted : ∀ i∈deleted,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal ActualEisensteinCubic.O)∣x.quotient) (deleted₁ deleted₂ : Finset ι) (hd₁ : ∀ i∈deleted₁,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal ActualEisensteinCubic.O)∣x.quotient) (hd₂ : ∀ i∈deleted₂,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal ActualEisensteinCubic.O)∣x.quotient) (pool : Finset ι)


include hpr in
theorem actual_second_canonical_label_span
     
          :
    Ideal.span {actualSecondRawLabel p x}=
      Ideal.span {primaryGenerator (actualSecondChild p u v x).2.1} := by
  obtain ⟨u₀,v₀,hl,hv⟩ := actual_second_generator_sectors p hp hpr x
  rw [hl,←Ideal.span_singleton_mul_span_singleton]
  simp only [Ideal.span_singleton_eq_top.mpr (Units.isUnit u₀),Ideal.top_mul]
  rfl

include hpr hb hE hdeleted in
theorem secondCanonicalPolynomial_parent_lists_restore
     
         
       
     
     
      (Ψ : OuterTriple→ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (slots : Finset σ)  lists   a 
     W   X   k  :
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots (fun j=>lists j\deleted) a W X ((actualSecondChild p u v x).1,
        (actualSecondChild p u v x).2.1,k) =
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots lists a W X ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,k) := by
  apply finiteCanonicalMarkedRow_restore_lists p hp hcop hg
  intro i hi
  have hk := actual_parent_deleted_prime_killed p x hb hE m i (hdeleted i hi)
  have he : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}=
      Ideal.span {(actualSecondInheritedPuncture m (actualSecondChild p u v x).1*
        primaryGenerator (actualSecondChild p u v x).2.1)} := by
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      actual_second_canonical_label_span p hp hpr x u v]
    congr 1
    exact actual_second_puncture_span p hp hpr x hE u v
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient)
  have hk' : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}≤Ideal.span {p i} :=
    Ideal.span_le.mpr (by simp_all)
  simp_all

include hpr hb hE hd₁ hd₂ in
theorem secondModeBranch_parent_lists_restore
     
         
       
     
     
     
      (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ)  lists₁ lists₂   a₁ a₂ 
     ω₁ ω₂   G E V B X   t  :
    secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂
      (fun i=>lists₁ i\deleted₁) (fun i=>lists₂ i\deleted₂) a₁ a₂ ω₁ ω₂ G E V B X t =
    secondModeOuter p x Ψ m z G E V B X t *
      (star (primeMark J₁ (fun i=>lists₁ i\deleted₁) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (fun i=>lists₂ i\deleted₂) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
      secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x) := by
  unfold secondModeBranch secondModeLeft secondModeRight
  rw [secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₁ hd₁,
    secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₂ hd₂]

end

end SevenEighths.InverseMoment



end OAI
