module

public import OAI.NumberTheory.PrimeGaps.FourierNormalization
public import Mathlib.Data.Nat.GCD.Prime

@[expose] public section

namespace OAI

namespace LargePrimeGaps















noncomputable def choiceSubset {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) : Finset ι := by
  classical
  exact if hp : p∈c.1 then (c.2 ⟨p,hp⟩).val else ∅

@[simp] theorem choiceSubset_of_mem {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∈c.1) :
    choiceSubset c p = (c.2 ⟨p,hp⟩).val := by simp [choiceSubset, hp]

@[simp] theorem choiceSubset_of_not_mem {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∉c.1) :
    choiceSubset c p = ∅ := by simp [choiceSubset, hp]

noncomputable def tuplePrimeSubset {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => (p:ℕ)∣d i

@[simp] theorem mem_tuplePrimeSubset {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) (i : ι) : i∈tuplePrimeSubset d p ↔ (p:ℕ)∣d i := by
  classical
  simp [tuplePrimeSubset]



end LargePrimeGaps

end OAI
