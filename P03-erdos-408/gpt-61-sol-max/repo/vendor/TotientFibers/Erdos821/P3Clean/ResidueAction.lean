module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Edge.ColReversal
import Erdos821.S2.HistoryProjection

public import Erdos821.P3Clean.CyclicAction
public import Erdos821.P3Clean.Truncation

/-! Uniform small residues and cutoff multiset memory carry a finite translation action. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups}

abbrev PendingState (P : PrimeGroups) := P.SmallResidues × ((g : P.BigGroup) → P.Memory g.val)

def pendingSize (s : PendingState P)  := ∑ g : P.BigGroup, (s.2 g).card

abbrev CutPendingState (P ) (B ) := {s : PendingState P // pendingSize s ≤ B}

instance finite_cutPendingState (P : PrimeGroups) (B : ℕ) : Finite (CutPendingState P B) := by
  let encode (s : CutPendingState P B) :
      P.SmallResidues × ((g : P.BigGroup) → {z : P.Memory g.val // z.card ≤ B}) :=
    (s.val.1, fun g => ⟨s.val.2 g, (Finset.single_le_sum (fun h _ => Nat.zero_le ((s.val.2 h).card))
        (Finset.mem_univ g)).trans s.property⟩)
  apply Finite.of_injective encode
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c => c.1) h
  · funext g
    exact congrArg (fun c => (c.2 g).val) h

section
variable (a b : ℤ) {g : P.Group} (z : P.Particle g) (y : P.SmallResidues)


theorem translateParticle_add       :
    translateParticle a (translateParticle b z) = translateParticle (a + b) z := by solve_by_elim [_root_.Erdos821.P3Edge.translateParticle_add]

alias translateParticle_zero := _root_.Erdos821.P3Edge.translateParticle_zero

theorem translateMemory_add     (z : P.Memory g) :
    translateMemory a (translateMemory b z) = translateMemory (a + b) z := by
  simp_all [translateMemory, translateParticle_add]

theorem translateMemory_zero   (z : P.Memory g) : translateMemory 0 z = z := by
  unfold translateMemory
  simpa only [translateParticle_zero] using Multiset.map_id' z

theorem translateSmallResidues_add     :
    translateSmallResidues a (translateSmallResidues b y) = translateSmallResidues (a + b) y := by
  funext g p
  simp only [translateSmallResidues]
  push_cast
  abel

alias translateSmallResidues_zero := _root_.Erdos821.S2Core.translateSmallResidues_zero

end

def translatePending (delta : ℤ) (s : PendingState P)  :=
  (translateSmallResidues delta s.1, fun g => translateMemory delta (s.2 g))

section
variable (delta a b : ℤ) (s : PendingState P)


theorem translatePending_size     :
    pendingSize (translatePending delta s) = pendingSize s := by
  simp only [pendingSize, translatePending, translateMemory_card]

theorem translatePending_add     :
    translatePending a (translatePending b s) = translatePending (a + b) s := by
  apply Prod.ext
  · exact translateSmallResidues_add a b s.1
  · funext g
    exact translateMemory_add a b (s.2 g)

theorem translatePending_zero   : translatePending 0 s = s := by
  apply Prod.ext
  · exact translateSmallResidues_zero s.1
  · funext g
    exact translateMemory_zero (s.2 g)

end

def pendingTranslationEquiv (B : ℕ) (delta : ℤ) : Equiv.Perm (CutPendingState P B) where
  toFun s := ⟨translatePending delta s.val, by simpa only [translatePending_size] using s.property⟩
  invFun s := ⟨translatePending (-delta) s.val, by simpa only [translatePending_size] using s.property⟩
  left_inv := by
    grind [translatePending_add, translatePending_zero]
  right_inv := by
    grind [translatePending_add, translatePending_zero]

section
variable (B : ℕ)


theorem pendingTranslationEquiv_add    a b  :
    pendingTranslationEquiv (P := P) B (a + b) =
      pendingTranslationEquiv B a * pendingTranslationEquiv B b := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  exact (translatePending_add a b s.val).symm

theorem pendingTranslationEquiv_zero   :
    pendingTranslationEquiv (P := P) B 0 = 1 := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  exact translatePending_zero s.val

end

def pendingTranslationHom (B : ℕ) : ℤ →+ Additive (Equiv.Perm (CutPendingState P B)) where
  toFun delta := Additive.ofMul (pendingTranslationEquiv B delta)
  map_zero' := congrArg Additive.ofMul (pendingTranslationEquiv_zero B)
  map_add' a b := congrArg Additive.ofMul (pendingTranslationEquiv_add B a b)

theorem pendingTranslationEquiv_zpow  B   delta  :
    pendingTranslationEquiv (P := P) B delta = pendingTranslationEquiv B 1 ^ delta := by
  have h := (pendingTranslationHom (P := P) B).map_zsmul delta 1
  aesop

def pendingMass (F : FixedData) (n : ℕ) (s : PendingState P)  :=
  (Fintype.card P.SmallResidues : ℝ)⁻¹ *
    ∏ g : P.BigGroup, P.groupMemoryMass F n g.val (s.2 g)

theorem pendingMass_translate  F   n   delta  (s : PendingState P) :
    pendingMass F n (translatePending delta s) = pendingMass F n s := by
  simp only [pendingMass, translatePending, translateMemory_groupMass]


end Erdos821.P3Clean
