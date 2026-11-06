module

public import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceOverlap
public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedFourier

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open InverseInitialConjugateEnergy InverseInitialPoissonBridge
open UniqueFactorizationMonoid ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem remaining_injective (L:ι→Finset (Ideal HeckeFamily.O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) : Function.Injective (fun i=>(y i).val) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val) hij)
    (y i).property (by simp_all)

theorem remaining_moebius (L:ι→Finset (Ideal HeckeFamily.O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) :
    (moebius (remainingIdeal L J y):ℂ)=(-1:ℂ)^Fintype.card {i:ι // i∉J} := by
  let:∀i:{i:ι // i∉J},((y i).val).IsMaximal:=fun i=>
    (Ideal.isPrime_of_prime (by grind)).isMaximal
      (hprime i.val _ (by simp)).ne_zero
  simpa only [remainingIdeal,Finset.card_univ] using prime_product_moebius
    (fun i=>(y i).val) (by grind)
    (remaining_injective L hdis J y) Finset.univ

def remainingPolynomial (S:Finset (Ideal HeckeFamily.O))(L:ι→Finset (Ideal HeckeFamily.O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal HeckeFamily.O→ℂ)(η:Ideal HeckeFamily.O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:HeckeFamily.O) : ℂ :=
  ∑y:Remaining L J,(∏i:{i:ι // i∉J},star (coeff i.val (y i).val))*
    residualNormalizedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
      (fun v=>star (W v)) Z r z G u

theorem remainingResidual_eq_polynomial (S:Finset (Ideal HeckeFamily.O))
    (L:ι→Finset (Ideal HeckeFamily.O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal HeckeFamily.O→ℂ)(η:Ideal HeckeFamily.O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:HeckeFamily.O) :
    remainingResidual S L J x coeff η (fun _=>1) W Z r z G u=
      (-1:ℂ)^Fintype.card {i:ι // i∉J}*
      remainingPolynomial S L J x coeff η W Z r z G u := by
  unfold remainingResidual remainingPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [remaining_moebius L hprime hdis]
  simp only [star_mul,star_prod,star_pow,star_neg,star_one,conjugatedResidual]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
