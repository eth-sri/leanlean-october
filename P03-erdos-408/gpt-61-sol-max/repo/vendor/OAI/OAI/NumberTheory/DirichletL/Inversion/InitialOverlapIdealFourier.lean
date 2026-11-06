module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
public import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic
namespace SevenEighths.InverseInitialOverlapIdealFourier
open InverseMoment InverseInitialOverlapFourier

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def activeIndices (primes : ι→Ideal ActualEisensteinCubic.O) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal ActualEisensteinCubic.O)  := (I.biUnion L).filter (fun p=>primes p∣c)

omit [DecidableEq σ] in
theorem activeIndices_mem (primes : ι→Ideal ActualEisensteinCubic.O) (I : Finset σ) (L : σ→Finset ι)
     c  {i : σ} (hi : i∈I)  {p}  (hp : p∈L i) :
    p∈activeIndices primes I L c ↔ primes p∣c := by
  grind [activeIndices]

theorem indexed_mark_active (primes : ι→Ideal ActualEisensteinCubic.O) (I : Finset σ)  L 
     a   c  :
    indexedIdealMark primes I L a c=primeMark I L a (activeIndices primes I L c) := by
  unfold indexedIdealMark primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  grind [activeIndices_mem]

omit [DecidableEq σ] [DecidableEq ι] in
theorem tuple_gate_product (primes : ι→Ideal ActualEisensteinCubic.O) (I : Finset σ)
    (a : σ→ι→ℂ) (p : ∀i∈I,ι)  c 
    (hc : Pairwise (Function.onFun IsCoprime (fun i:I=>primes (p i.val i.property)))) :
    (∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)=
      if (∏i∈I.attach,primes (p i.val i.property))∣c then
        ∏i∈I.attach,a i.val (p i.val i.property) else 0 := by
  by_cases h : (∏i∈I.attach,primes (p i.val i.property))∣c
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_left ((Finset.dvd_prod_of_mem (fun i:I=>primes (p i.val i.property)) hi).trans h)
  · rw [ite_eq_right h]
    have hn : ∃i:I,¬primes (p i.val i.property)∣c := by
      by_contra hn
      push Not at hn
      apply h
      exact Finset.prod_dvd_of_coprime (hc.set_pairwise _) (fun i _=>hn i)
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_attach _ i) (ite_eq_right hi)

end SevenEighths.InverseInitialOverlapIdealFourier

end

end OAI
