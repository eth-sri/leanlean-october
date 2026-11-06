module

public import OAI.NumberTheory.DirichletL.Descent.CompletePool
public import OAI.NumberTheory.DirichletL.Descent.ReopenedMarks

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels


def indexedIdealMark {ι σ } [DecidableEq ι] [DecidableEq σ]
    (primes : ι→Ideal ActualEisensteinCubic.O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (I : Ideal ActualEisensteinCubic.O)  :=
  ∏j∈slots,∑i∈lists j,if primes i∣I then a j i else 0

section
variable {σ : Type*} [DecidableEq σ]

theorem complete_pool_mark    
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ)  lists   a 
     T  :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val) =
      primeMark slots lists a T := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T 0
  simp only [Finsupp.support_zero,Finset.union_empty,primeProduct,Finset.prod_empty,
    Ideal.span_singleton_one,←Ideal.one_eq_top,one_pow,mul_one] at he
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem finiteCanonicalMarkedRow_complete_global    
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ→ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
     lists 
     a  :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X =
    ∑' I:Ideal ActualEisensteinCubic.O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a I*W ((Ideal.absNorm I:ℝ)/X) := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b X hX hW hD
    (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)
  dsimp only at he
  have hmark : (fun T:Finset (primePool F)=>W (primeProductNorm (poolPrimary F) T/X)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val)) =
      (fun T=>primeMark slots lists a T*W (primeProductNorm (poolPrimary F) T/X)) := by
    funext T
    rw [complete_pool_mark F hF slots lists a T,mul_comm]
  rw [hmark] at he
  unfold finiteCanonicalMarkedRow
  calc
    _ = _ := he
    _ = _ := tsum_congr (fun I=>by ring)

end

end
end SevenEighths.InverseMoment

end OAI
