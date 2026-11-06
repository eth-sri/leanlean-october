module
public import Mathlib.Tactic

public import Erdos821.S2.LiveGrowth
public import Erdos821.S2.ResiduePaths

/-! Forgetting a distinct memory history gives a compatible physical label path. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

section
variable {M : ℕ} (delta epsilon : ℤ) (y : P.SmallResidues)


theorem smallPhysical_act_iff     (π : P.Permutations M) (a : P.Labels M) :
    P.smallPhysical y (P.act π a) ↔ P.smallPhysical y a := by
  constructor
  · intro hs g
    constructor
    · intro i j he
      have he' : (P.act π a) g.val ((π g.val).symm i) = (P.act π a) g.val ((π g.val).symm j) := by
        simpa only [PrimeGroups.act, Equiv.apply_symm_apply] using he
      exact (π g.val).symm.injective ((hs g).1 he')
    · intro i
      have he : (P.act π a) g.val ((π g.val).symm i) = a g.val i := by
        simp [PrimeGroups.act]
      exact Eq.mp (congrArg (fun p : P.Prime g.val => y g p = 0) he)
        ((hs g).2 ((π g.val).symm i))
  · intro hs g
    exact ⟨(hs g).1.comp (π g.val).injective, fun i => (hs g).2 (π g.val i)⟩

theorem translateSmallResidues_zero   : translateSmallResidues 0 y = y := by
  funext g p
  simp [translateSmallResidues]

theorem translateSmallResidues_add     :
    translateSmallResidues (delta + epsilon) y =
      translateSmallResidues epsilon (translateSmallResidues delta y) := by
  funext g p
  simp only [translateSmallResidues, Int.cast_add, add_assoc]

end

theorem residuePath_offset_succ {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)  i  :
    Q.offset i.succ = Q.offset i.castSucc + Q.step i := by
  simpa only [ResiduePath.offset, Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff] using
    sum_fin_through n Q.step i

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

def toResiduePath : ResiduePath A n where
  labels := fun i => (H.before i).2.1
  sourcePerm := fun i => (H.edge i).1
  targetPerm := fun i => (H.edge i).2.1
  pattern := fun i => (H.edge i).2.2.1
  free := fun i => (H.edge i).2.2.2.1

section
variable (hTask : EdgeLiveConservationTask) (hn : 0 < n) (hH : H.Valid) (i : Fin (n + 1)) (hd : H.DistinctBirths)


include hn hH in
theorem smallPhysical_before       :
    P.smallPhysical (H.before i).1 (H.before i).2.1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · let e : Fin n := ⟨0, hn⟩
    have hs := (hH.2.2.2 e).1.1
    have hp : P.smallPhysical (H.after 0).1 (H.after 0).2.1 :=
      (smallPhysical_act_iff (H.after 0).1 (H.edge e).1 (H.after 0).2.1).mp hs
    rw [(hH.2.2.1 0).1, (hH.2.2.1 0).2.1]
    exact hp
  · have hs := (hH.2.2.2 j).1.2.1
    exact (smallPhysical_act_iff (H.before j.succ).1 (H.edge j).2.1 (H.before j.succ).2.1).mp hs

include hTask hn hH hd in
theorem toResiduePath_valid    
        : H.toResiduePath.Valid := by
  constructor
  · intro i g
    by_cases hg : P.big g = true
    · exact (H.big_active_injective hTask hH hd i ⟨g, hg⟩).1
    · have hs : P.big g = false := by cases he : P.big g <;> simp_all
      exact (H.smallPhysical_before hn hH i ⟨g, hs⟩).1
  · intro i
    dsimp only [toResiduePath, ResiduePath.source, ResiduePath.target]
    rw [(hH.2.2.1 i.castSucc).2.1]
    exact ⟨(hH.2.2.2 i).1.2.2.1, (hH.2.2.2 i).1.2.2.2.1⟩

include hn hH hd in
theorem toResiduePath_valid_of_distinct       :
    H.toResiduePath.Valid := H.toResiduePath_valid EdgeLiveConservationTask_proof hn hH hd

include hH in
theorem small_residue_step    i  :
    (H.before i.succ).1 = translateSmallResidues (H.toResiduePath.step i) (H.before i.castSucc).1 := by
  have he := (hH.2.2.2 i).1.2.2.2.2.1
  dsimp only [permuteActive] at he
  rw [← (hH.2.2.1 i.castSucc).1, ← (hH.2.2.1 i.castSucc).2.1] at he
  exact he

include hH in
theorem small_residue_translation     :
    (H.before i).1 = translateSmallResidues (H.toResiduePath.offset i) (H.before 0).1 := by
  induction i using Fin.induction with
  | zero => rw [ResiduePath.offset_zero, translateSmallResidues_zero]
  | succ i ih =>
      simp_all [translateSmallResidues, translateSmallResidues_add, residuePath_offset_succ, Erdos821.S2Core.MemoryHistory.small_residue_step]

end

end MemoryHistory


end Erdos821.S2Core
