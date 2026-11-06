module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceCoefficients
public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial

@[expose] public section

namespace OAI



open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
open InverseInitialConjugateEnergy InverseInitialPoissonBridge

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem tuple_product_squarefree (P:ι→Ideal HeckeFamily.O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Squarefree (∏i,P i) := by
  have hs:∀Q∈Finset.univ.image P,Prime Q := by
    simp_all
  have he:(∏Q∈Finset.univ.image P,Q)=∏i,P i :=
    Finset.prod_image (fun i hi j hj h=>hinj h)
  rw [←he]
  exact InverseInitialExcludedPolynomial.prime_product_squarefree _ hs

omit [DecidableEq ι] in
theorem tuple_product_support (P:ι→Ideal HeckeFamily.O)(hP:∀i,Prime (P i))
    (_hinj:Function.Injective P) : primeSupport (∏i,P i)=Finset.univ.image P := by
  have hn:(∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>(hP i).ne_zero)
  ext Q
  rw [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hn,Finset.mem_image]
  constructor
  · rintro ⟨hQ,hd⟩
    obtain ⟨i,hi,hd⟩:=(hQ.dvd_finsetProd_iff P).mp hd
    have he:Q=P i:=associated_iff_eq.mp (hQ.associated_of_dvd (hP i) hd)
    exact ⟨i,hi,he.symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hP i,Finset.dvd_prod_of_mem P hi⟩

omit [DecidableEq ι] in
theorem tuple_divisors_eq_subsets (P:ι→Ideal HeckeFamily.O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) :
    idealDivisors (∏i,P i)=Finset.univ.powerset.image (fun J:Finset ι=>∏i∈J,P i) := by
  have hs:=tuple_product_squarefree P hP hinj
  have hf:(idealDivisors (∏i,P i)).filter Squarefree=idealDivisors (∏i,P i) := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    exact hs.squarefree_of_dvd ((mem_idealDivisors hs.ne_zero).mp hJ)
  rw [←hf,squarefree_divisors_eq_image _ hs.ne_zero,tuple_product_support P hP hinj,
    Finset.powerset_image,Finset.image_image]
  congr 1
  funext J
  exact Finset.prod_image (fun i hi j hj h=>hinj h)

omit [Fintype ι] in
theorem tuple_subset_product_injective (P:ι→Ideal HeckeFamily.O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Function.Injective (fun J:Finset ι=>∏i∈J,P i) := by
  let:∀i,(P i).IsMaximal:=fun i=>(Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  exact FirstCauchyArithmetic.family_product_injective P hinj

section
variable (S : Finset (Ideal HeckeFamily.O)) (P : ι→Ideal HeckeFamily.O) (hP : ∀i,Prime (P i)) (hinj : Function.Injective P)

include hP hinj in
theorem sum_tuple_divisors   
     (f:Ideal HeckeFamily.O→ℂ) :
    (∑j∈idealDivisors (∏i,P i),f j)=∑J∈Finset.univ.powerset,f (∏i∈J,P i) := by
  simp_all [tuple_divisors_eq_subsets, K, tuple_subset_product_injective]

include hP hinj in
theorem originalTotal_slot_subsets  
       
    (η:Ideal HeckeFamily.O→*ℂ)(a:Ideal HeckeFamily.O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:HeckeFamily.O) :
    originalTotalPolynomial S (∏i,P i) η a W Z r z u=
      ∑J∈Finset.univ.powerset,
        originalFixedPolynomial S (∏i,P i) (∏i∈J,P i) η a W Z r z u := by
  rw [originalTotalPolynomial_eq_sectors S (tuple_product_squarefree P hP hinj)
    η a W hZ r z (fun _=>0),sum_tuple_divisors P hP hinj]

end

end SevenEighths.DetectorDictionaryInverseMarkedReference



end OAI
