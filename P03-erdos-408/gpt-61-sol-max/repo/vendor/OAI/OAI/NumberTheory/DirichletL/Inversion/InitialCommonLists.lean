module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialCommonTuples
public import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonLists
open InverseMoment

variable {σ:Type*} [DecidableEq σ]

def poolList (F)(L:Finset (Ideal ActualEisensteinCubic.O)) : Finset (primePool F) :=
  Finset.univ.filter (fun i=>i.val∈L)

section
variable (F L : Finset (Ideal ActualEisensteinCubic.O)) (hL : ∀P∈L,Prime P) (a : Ideal ActualEisensteinCubic.O→ℂ) (A : Finset (primePool F))


include hL in
theorem dividing_list_image   
       :
    ((poolList F L).filter (fun i=>i∈A)).image Subtype.val=
      L.filter (fun P=>P∣∏i∈A,i.val) := by
  ext P
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hiL,hiA⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiL).2,Finset.dvd_prod_of_mem _ hiA⟩
  · intro h
    obtain ⟨hPL,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨i,hi,hd⟩ := (hL P hPL).dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
    have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    have he := (prime_dvd_prime_iff_eq (hL P hPL) hip).mp hd
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨?_,hi⟩,he.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hPL⟩

include hL in
theorem original_ideal_slot   
        :
    (∑P∈L,if P∣∏i∈A,i.val then a P else 0)=
      primeSlot (poolList F L) (fun i=>a i.val) A := by
  rw [←Finset.sum_filter,←dividing_list_image F L hL A,
    Finset.sum_image (fun i _ j _ h=>Subtype.val_injective h)]
  simp only [primeSlot,←Finset.sum_filter]

theorem original_ideal_mark  (I:Finset σ)
     L (hL:∀i∈I,∀P∈L i,Prime P)
     a  A  :
    indexedIdealMark id I L a (∏i∈A,i.val)=
      primeMark I (fun i=>poolList F (L i)) (fun i q=>a i q.val) A := by
  unfold indexedIdealMark primeMark
  apply Finset.prod_congr rfl
  solve_by_elim [original_ideal_slot]

end

end SevenEighths.InverseInitialCommonLists

end

end OAI
