module
public import Mathlib

public import PottsDiscontinuity.Torus.RibbonEuler

/-!
# Monotonicity of the attachment handle count

Extend any order of the old open edges by the newly open edges. Handle events
cannot be lost. Order independence transfers this to the coordinate-defined count.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

@[simp] theorem mem_openEdgeList_iff (A : RCConfig N M) (v : Fin N × Fin M) :
    v ∈ openEdgeList A ↔ A v = true := by
  simp_all [openEdgeList]

section

variable (hN : Even N) (hM : Even M)
include hN hM

theorem attachmentHandleCount_le_cons 
    (v : Fin N × Fin M) (L : List (Fin N × Fin M)) :
    attachmentHandleCount hN hM L ≤ attachmentHandleCount hN hM (v :: L) := Nat.le.intro rfl

theorem attachmentHandleCount_le_append 
    (L K : List (Fin N × Fin M)) :
    attachmentHandleCount hN hM K ≤ attachmentHandleCount hN hM (L ++ K) := by
  induction L with
  | nil => exact le_rfl
  | cons v L ih => grind [attachmentHandleCount_le_cons]

theorem attachmentHandleCount_eq_ribbonHandleCount 
    (L : List (Fin N × Fin M)) (hL : L.Nodup) :
    attachmentHandleCount hN hM L = ribbonHandleCount hN hM (configOfList L) := by
  apply attachmentHandleCount_order_independent hN hM L _ hL (openEdgeList_nodup _)
  rw [configOfList_openEdgeList]

/-- Opening additional indexed edges cannot decrease the number of handles. -/
theorem ribbonHandleCount_mono  (A B : RCConfig N M)
    (hAB : ∀ v, A v = true → B v = true) :
    ribbonHandleCount hN hM A ≤ ribbonHandleCount hN hM B := by
  let E  := fun v => B v && !A v
  let L := openEdgeList E
  let K := openEdgeList A
  
  
  have hcfg : configOfList (L ++ K) = B := by
    funext v
    
    change decide (v ∈ openEdgeList E ++ openEdgeList A) = B v
    simp only [List.mem_append, mem_openEdgeList_iff]
    change decide ((B v && Bool.not (A v)) = true ∨ A v = true) = B v
    cases ha : A v <;> cases hb : B v <;>
      simp_all only [Bool.not_false, Bool.and_true, Bool.false_eq_true, or_true, or_false, decide_true, decide_false]
  have hm := attachmentHandleCount_le_append hN hM L K
  rw [attachmentHandleCount_eq_ribbonHandleCount hN hM (L ++ K) ((openEdgeList_nodup E).append (openEdgeList_nodup A) (by
                                                                                                                           apply List.disjoint_left.mpr
                                                                                                                           all_goals aesop)), hcfg] at hm
  exact hm

end

end PottsDiscontinuity.Torus
