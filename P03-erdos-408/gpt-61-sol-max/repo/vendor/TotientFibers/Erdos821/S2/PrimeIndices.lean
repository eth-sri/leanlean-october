module
public import Mathlib.Tactic

public import Erdos821.S2.SpanLifecycle

/-! Prime lookup in a memory with no repeated prime values. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

section
variable {g : P.Group} (z : P.Memory g)

theorem pendingPrimes_enumeration     :
    pendingPrimes z = (Finset.univ : Finset (Fin z.card)).val.map (fun i => (memoryEntry z i).1) := by
  have he := congrArg pendingPrimes (memoryEntry_enumeration z)
  simpa only [pendingPrimes, Multiset.map_map, Function.comp_def] using he.symm

theorem memoryEntry_mem     (i : Fin z.card) : memoryEntry z i ∈ z := Eq.mp (congrArg (fun _a => Erdos821.S2Core.memoryEntry z i ∈ _a) (Erdos821.S2Core.memoryEntry_enumeration z)) (Multiset.mem_map.mpr (Exists.intro i ⟨Finset.mem_univ i, rfl⟩))

theorem pendingPrime_mem_iff     (p : P.Prime g) :
    p ∈ pendingPrimes z ↔ ∃ i : Fin z.card, (memoryEntry z i).1 = p := by
  simp_all [pendingPrimes_enumeration]

theorem memoryEntry_prime_injective     (hz : (pendingPrimes z).Nodup) :
    Function.Injective (fun i : Fin z.card => (memoryEntry z i).1) := by
  rw [pendingPrimes_enumeration] at hz
  intro i j he
  exact Multiset.inj_on_of_nodup_map hz i (Finset.mem_univ i) j (Finset.mem_univ j) he

def primeIndex {g } (z ) (p : P.Prime g) (hp : p ∈ pendingPrimes z)  :=
  Classical.choose ((pendingPrime_mem_iff z p).mp hp)

theorem primeIndex_spec     (p : P.Prime g) (hp : p ∈ pendingPrimes z) :
    (memoryEntry z (primeIndex z p hp)).1 = p :=
  Classical.choose_spec ((pendingPrime_mem_iff z p).mp hp)

theorem primeIndex_unique     (hz : (pendingPrimes z).Nodup)
    (p : P.Prime g) (hp : p ∈ pendingPrimes z) (i : Fin z.card) (hi : (memoryEntry z i).1 = p) :
    primeIndex z p hp = i :=
  memoryEntry_prime_injective z hz ((primeIndex_spec z p hp).trans hi.symm)

theorem deleteMemoryIndices_filter     (R : P.Particle g → Prop) :
    deleteMemoryIndices z (Finset.univ.filter (fun i => R (memoryEntry z i))) =
      z.filter (fun u => ¬ R u) := by
  have hs : (Finset.univ : Finset (Fin z.card)) \ Finset.univ.filter (fun i => R (memoryEntry z i)) =
      Finset.univ.filter (fun i => ¬ R (memoryEntry z i)) := by
    ext i
    simp
  rw [deleteMemoryIndices_eq_map, hs]
  calc
    _ = ((Finset.univ : Finset (Fin z.card)).val.map (memoryEntry z)).filter (fun u => ¬ R u) := by
      rw [Multiset.filter_map]
      rfl
    _ = _ := by rw [memoryEntry_enumeration]

end

end Erdos821.S2Core
