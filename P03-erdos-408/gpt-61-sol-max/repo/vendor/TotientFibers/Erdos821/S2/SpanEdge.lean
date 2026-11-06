module
public import Mathlib.Tactic

public import Erdos821.S2.SpanGhost
public import Erdos821.S2.PhysicalCompatibility

/-! Transfer masks and old-index injections reconstructed from prime lifespans. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def storeSlots (S : LifespanAssignment P n) (i : Fin n) (g : P.BigGroup)  :=
  Finset.univ.filter (fun j => ¬ (A.pattern (Q.pattern i)).shared g.val j ∧
    Q.pendingBefore g (Q.source i g.val j) (S g (Q.source i g.val j)) i.succ)

def promotionSlots (S : LifespanAssignment P n) (i : Fin n) (g : P.BigGroup)  :=
  Finset.univ.filter (fun j => ¬ (A.pattern (Q.pattern i)).shared g.val j ∧
    Q.target i g.val j ∈ Q.pendingAfterPrimes S i.castSucc g)

theorem promotion_prime_mem (S : LifespanAssignment P n) (i : Fin n) (g : P.BigGroup)
    (j : {j : Fin (J + F.ell) // j ∈ Q.promotionSlots S i g}) :
    Q.target i g.val j.val ∈ pendingPrimes (Q.memoryAfter S i.castSucc g) := by
  rw [pendingPrimes_memoryAfter]
  exact (Finset.mem_filter.mp j.property).2.2

def promotionIndex (S ) (i ) (g )
    (j : {j : Fin (J + F.ell) // j ∈ Q.promotionSlots S i g})  :=
  primeIndex (Q.memoryAfter S i.castSucc g) (Q.target i g.val j.val) (Q.promotion_prime_mem S i g j)

section
variable (S : LifespanAssignment P n) (hq : Q.Valid) (i : Fin n) (g : P.BigGroup)


theorem promotionIndex_spec      
     j  :
    (memoryEntry (Q.memoryAfter S i.castSucc g) (Q.promotionIndex S i g j)).1 = Q.target i g.val j.val :=
  primeIndex_spec _ _ _

include hq in
theorem target_injective      g  : Function.Injective (Q.target i g) :=
  (hq.1 i.succ g).comp (Q.targetPerm i g).injective

include hq in
theorem source_injective      g  : Function.Injective (Q.source i g) :=
  (hq.1 i.castSucc g).comp (Q.sourcePerm i g).injective

include hq in
theorem promotionIndex_injective         :
    Function.Injective (Q.promotionIndex S i g) := by
  intro j k he
  apply Subtype.ext
  apply Q.target_injective hq i g.val
  grind [memoryEntry, Erdos821.S2Core.ResiduePath.promotionIndex_spec]

end

def reconstructedTransferChoice (S ) (y ) (i : Fin n) :
    TransferChoice (Q.stateAfter S y i.castSucc) :=
  ⟨Q.storeSlots S i, ⟨Q.promotionSlots S i, Q.promotionIndex S i⟩⟩

section
variable (S : LifespanAssignment P n) (hq : Q.Valid) (hS : Q.lifespanValid S) (i : Fin n) (g : P.BigGroup) (j : Fin (J + F.ell))


include hq in
theorem store_slot_allowed    
          (hj : j ∈ Q.storeSlots S i g) :
    ¬ (A.pattern (Q.pattern i)).shared g.val j ∧
      ¬ (Q.source i g.val j).val ∣ (A.pattern (Q.pattern i)).D (Q.source i) (Q.free i) := by
  have hs := (Finset.mem_filter.mp hj).2.1
  refine ⟨hs, ?_⟩
  intro hd
  exact hs ((source_label_dvd_D_iff (A.pattern (Q.pattern i)) (Q.source i) (Q.target i) (Q.free i)
    (Q.source_injective hq i) (hq.2 i).2 g.val j).mp hd)

include hq in
theorem promotion_slot_allowed    
        (j : {j : Fin (J + F.ell) // j ∈ Q.promotionSlots S i g}) :
    ¬ (A.pattern (Q.pattern i)).shared g.val j.val ∧
      ¬ (Q.target i g.val j.val).val ∣ (A.pattern (Q.pattern i)).D (Q.source i) (Q.free i) := by
  have hs := (Finset.mem_filter.mp j.property).2.1
  refine ⟨hs, ?_⟩
  intro hd
  exact hs ((target_label_dvd_D_iff (A.pattern (Q.pattern i)) (Q.source i) (Q.target i) (Q.free i)
    (Q.target_injective hq i) (hq.2 i).1 (hq.2 i).2 g.val j.val).mp hd)

theorem memoryAfter_member_form    i   g 
     z  (hz : z ∈ Q.memoryAfter S i g) :
    ∃ p ∈ Q.pendingAfterPrimes S i g,
      z = (⟨p, ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val)⟩ : P.Particle g.val) := by
  have he := Q.memoryAfter_eq_map S i g
  have hm := Eq.mp (congrArg (fun m : P.Memory g.val => z ∈ m) he) hz
  obtain ⟨p, hp, he⟩ := Multiset.mem_map.mp hm
  exact ⟨p, hp, he.symm⟩

theorem source_activeVisit       :
    i.castSucc ∈ Q.activeVisits g (Q.source i g.val j) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, ⟨Q.sourcePerm i g.val j, rfl⟩⟩

theorem target_activeVisit       :
    i.succ ∈ Q.activeVisits g (Q.target i g.val j) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, ⟨Q.targetPerm i g.val j, rfl⟩⟩

include hS in
theorem span_active_hit    
     i   g   p  (hi : i ∈ Q.activeVisits g p) :
    ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val) = 0 := by
  have hs := hS g p
  rcases he : S g p with _ | ⟨birth, stop⟩
  · rw [he] at hs
    rw [hs] at hi
    exact False.elim (Finset.notMem_empty i hi)
  · rw [he] at hs
    exact hs.2.2.2.2 i hi

include hS in
theorem promotion_translated_zero    
         j  :
    let z := memoryEntry (Q.memoryAfter S i.castSucc g) (Q.promotionIndex S i g j)
    z.2 + (Q.step i : ZMod z.1.val) = 0 := by
  have hm := Q.memoryAfter_member_form S i.castSucc g _
    (memoryEntry_mem (Q.memoryAfter S i.castSucc g) (Q.promotionIndex S i g j))
  obtain ⟨p, _, he⟩ := hm
  have hp : p = Q.target i g.val j.val := by
    have hspec := Q.promotionIndex_spec S i g j
    rw [he] at hspec
    exact hspec
  subst p
  dsimp only
  rw [he]
  have hh := Q.span_active_hit S hS i.succ g (Q.target i g.val j.val) (Q.target_activeVisit i g j.val)
  rw [residuePath_offset_succ] at hh
  simp only [Int.cast_sub, Int.cast_add] at hh ⊢
  linear_combination hh

end

end ResiduePath


end Erdos821.S2Core
