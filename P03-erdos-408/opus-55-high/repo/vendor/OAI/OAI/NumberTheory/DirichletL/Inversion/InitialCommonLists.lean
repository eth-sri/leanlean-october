module

public import OAI.NumberTheory.DirichletL.Inversion.InitialCommonTuples
public import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
open ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonLists
open InverseMoment
variable {σ:Type*} [DecidableEq σ]

def poolList (F:Finset (Ideal ActualEisensteinCubic.O))(L:Finset (Ideal ActualEisensteinCubic.O)) : Finset (primePool F) :=
  Finset.univ.filter (fun i=>i.val∈L)

theorem dividing_list_image (F:Finset (Ideal ActualEisensteinCubic.O))(L:Finset (Ideal ActualEisensteinCubic.O))
    (hL:∀P∈L,Prime P)(A:Finset (primePool F)) :
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
    have hip := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    have he := (prime_dvd_prime_iff_eq (by grind) hip).mp hd
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨?_,hi⟩,he.symm⟩
    exact Finset.mem_filter.mpr (by grind)

theorem original_ideal_slot (F:Finset (Ideal ActualEisensteinCubic.O))(L:Finset (Ideal ActualEisensteinCubic.O))
    (hL:∀P∈L,Prime P)(a:Ideal ActualEisensteinCubic.O→ℂ)(A:Finset (primePool F)) :
    (∑P∈L,if P∣∏i∈A,i.val then a P else 0)=
      primeSlot (poolList F L) (fun i=>a i.val) A := by
  rw [←Finset.sum_filter,←dividing_list_image F L hL A,
    Finset.sum_image (by simp)]
  simp only [primeSlot,←Finset.sum_filter]

theorem original_ideal_mark (F:Finset (Ideal ActualEisensteinCubic.O))(I:Finset σ)
    (L:σ→Finset (Ideal ActualEisensteinCubic.O))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal ActualEisensteinCubic.O→ℂ)(A:Finset (primePool F)) :
    indexedIdealMark id I L a (∏i∈A,i.val)=
      primeMark I (fun i=>poolList F (L i)) (fun i q=>a i q.val) A := by
  unfold indexedIdealMark primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact original_ideal_slot F (L i) (by grind) (a i) A

end SevenEighths.InverseInitialCommonLists

end

end OAI
