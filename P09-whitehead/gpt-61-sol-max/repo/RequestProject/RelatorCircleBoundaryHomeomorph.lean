import Mathlib.Tactic

import RequestProject.RelatorCircleFinite
import RequestProject.RelatorCircleEdges
import RequestProject.PresPosetDimension
import RequestProject.FinitePosetCycleRealization
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual valid relator-circle realization is homeomorphic to the
normed-circle boundary. Its traversal visits cor, cedgL, cmid, cedgR for
each letter, in that order. Only word length and positions enter the
parametrization. Pending Lean verification. -/

noncomputable section



namespace FiniteChains.PresModel
open Comb RelativeAttachment

def cPosCyclicIndex : CPos ≃ Fin 4 where
  toFun
    | .cor => 0
    | .cedgL => 1
    | .cmid => 2
    | .cedgR => 3
  invFun i := ![CPos.cor, CPos.cedgL, CPos.cmid, CPos.cedgR] i
  left_inv t := by cases t <;> rfl
  right_inv i := by fin_cases i <;> rfl

variable {A J : Type} (w : J → List (A × Bool)) (j : J)

def relatorCircleProductEquiv : RelatorCircle w j ≃ Fin (w j).length × CPos where
  toFun x := (⟨x.val.2.1, x.property.2⟩, x.val.2.2)
  invFun x := relatorCirclePoint w j x.1 x.2
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext x.property.1.symm rfl
  right_inv _ := rfl

def relatorCircleIndexEquiv  :=
  (relatorCircleProductEquiv w j).trans
    ((Equiv.prodCongr (Equiv.refl _) cPosCyclicIndex).trans finProdFinEquiv)

variable (hn : 0 < (w j).length)

theorem relatorCircleIndex_symm_pair (k : Fin (w j).length) (t : Fin 4) :
    (relatorCircleIndexEquiv w j).symm (finProdFinEquiv (k, t)) =
      relatorCirclePoint w j k (cPosCyclicIndex.symm t) := by
  aesop (add simp [relatorCircleIndexEquiv, cPosCyclicIndex])

variable (x : RelatorCircle w j)
def relatorCircleSuccessor   :=
  let k : Fin (w j).length := ⟨x.val.2.1, x.property.2⟩
  match x.val.2.2 with
  | .cor => relatorCirclePoint w j k .cedgL
  | .cedgL => relatorCirclePoint w j k .cmid
  | .cmid => relatorCirclePoint w j k .cedgR
  | .cedgR => relatorCirclePoint w j
      ⟨(k.val + 1) % (w j).length, Nat.mod_lt _ hn⟩ .cor

theorem relatorCircleSuccessor_comparable  :
    x ≤ relatorCircleSuccessor w j hn x ∨ relatorCircleSuccessor w j hn x ≤ x := by
  rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
  dsimp at hj
  subst j'
  cases t
  · exact Or.inl (TCirc.cor_le_cedgL w hk)
  · exact Or.inl (TCirc.cmid_le_cedgR w hk)
  · exact Or.inr (TCirc.cmid_le_cedgL w hk)
  · exact Or.inr (TCirc.cor_csucc_le_cedgR w hk)

theorem relatorCircle_le_neighbors (a b : RelatorCircle w j) (hne : a ≠ b) (hab : a ≤ b) :
    relatorCircleSuccessor w j hn a = b ∨ relatorCircleSuccessor w j hn b = a := by
  
  rcases hab with he | he
  · exact (hne (Subtype.ext he)).elim
  rcases a with ⟨⟨ja, ka, ta⟩, hja, hka⟩
  rcases b with ⟨⟨jb, kb, tb⟩, hjb, hkb⟩
  dsimp at hja
  dsimp at hjb
  subst ja
  subst jb
  obtain ⟨_, _, ht⟩ := he
  rcases ht with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ |
    ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
  · subst kb
    exact Or.inl rfl
  · subst kb
    exact Or.inr rfl
  · subst kb
    exact Or.inl rfl
  · subst ka
    exact Or.inr rfl

theorem relatorCircle_neighbors (a b : RelatorCircle w j) (hne : a ≠ b)
    (hab : a ≤ b ∨ b ≤ a) :
    relatorCircleSuccessor w j hn a = b ∨ relatorCircleSuccessor w j hn b = a := by
  grind [relatorCircle_le_neighbors]

theorem relatorCircleSuccessor_index  :
    (relatorCircleIndexEquiv w j (relatorCircleSuccessor w j hn x)).val =
      if (relatorCircleIndexEquiv w j x).val + 1 < (w j).length * 4 then
        (relatorCircleIndexEquiv w j x).val + 1 else 0 := by
  rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
  change j' = j at hj
  subst j'
  change k < (w j).length at hk
  cases t
  · change 1 + 4 * k = if 0 + 4 * k + 1 < (w j).length * 4 then 0 + 4 * k + 1 else 0
    split_ifs <;> omega
  · change 3 + 4 * k = if 2 + 4 * k + 1 < (w j).length * 4 then 2 + 4 * k + 1 else 0
    split_ifs <;> omega
  · change 2 + 4 * k = if 1 + 4 * k + 1 < (w j).length * 4 then 1 + 4 * k + 1 else 0
    split_ifs <;> omega
  · change 0 + 4 * ((k + 1) % (w j).length) =
      if 3 + 4 * k + 1 < (w j).length * 4 then 3 + 4 * k + 1 else 0
    by_cases hnext : k + 1 < (w j).length
    · grind [Nat.mod_eq_of_lt]
    · grind [Nat.mod_self]

def relatorCircleSize  := (w j).length * 4 - 2

include hn in
theorem relatorCircleSize_add_two : relatorCircleSize w j + 2 = (w j).length * 4 := by
  dsimp [relatorCircleSize]
  omega

def relatorCircleEnumeration  :=
  (finCongr (relatorCircleSize_add_two w j hn)).trans (relatorCircleIndexEquiv w j).symm

theorem relatorCircleEnumeration_index (i : Fin (relatorCircleSize w j + 2)) :
    (relatorCircleIndexEquiv w j (relatorCircleEnumeration w j hn i)).val = i.val := by
  dsimp [FiniteChains.PresModel.relatorCircleEnumeration]
  rw [Equiv.apply_symm_apply]
  rfl

theorem relatorCircleEnumeration_next (i : Fin (relatorCircleSize w j + 1)) :
    relatorCircleSuccessor w j hn (relatorCircleEnumeration w j hn i.castSucc) =
      relatorCircleEnumeration w j hn i.succ := by
  apply (relatorCircleIndexEquiv w j).injective
  grind [relatorCircleSuccessor_index, relatorCircleEnumeration_index]

theorem relatorCircleEnumeration_last_next :
    relatorCircleSuccessor w j hn
      (relatorCircleEnumeration w j hn (Fin.last (relatorCircleSize w j + 1))) =
        relatorCircleEnumeration w j hn 0 := by
  apply (relatorCircleIndexEquiv w j).injective
  grind [relatorCircleSuccessor_index, relatorCircleEnumeration_index, relatorCircleSize]

theorem relatorCircle_next_edge (a : RelatorCircle w j) :
    (∃ i : Fin (relatorCircleSize w j + 1),
      a = relatorCircleEnumeration w j hn i.castSucc ∧
        relatorCircleSuccessor w j hn a = relatorCircleEnumeration w j hn i.succ) ∨
    (a = relatorCircleEnumeration w j hn (Fin.last (relatorCircleSize w j + 1)) ∧
      relatorCircleSuccessor w j hn a = relatorCircleEnumeration w j hn 0) := by
  obtain ⟨k, rfl⟩ := (relatorCircleEnumeration w j hn).surjective a
  refine Fin.lastCases ?_ ?_ k
  · simp_all [relatorCircleEnumeration_last_next]
  · simp_all [relatorCircleEnumeration_next]

def relatorCircleCycle : FinitePosetCycle (RelatorCircle w j) (relatorCircleSize w j) where
  positive := by dsimp [relatorCircleSize]; omega
  vertex := relatorCircleEnumeration w j hn
  consecutive i := by
    grind [relatorCircleSuccessor_comparable, relatorCircleEnumeration_next]
  closing := by
    grind [relatorCircleSuccessor_comparable, relatorCircleEnumeration_last_next]
  edges a b hne hab := by
    rcases relatorCircle_neighbors w j hn a b hne hab with h | h
    · grind [relatorCircle_next_edge]
    · grind [relatorCircle_next_edge]
  height x := circleDimension w x.val
  height_strict := fun _ _ h => circleDimension_strictMono w h
  height_le x := circleDimension_le_one w x.val

def relatorCircleTraversal := (relatorCircleCycle w j hn).traversal

/-- The actual valid relator-circle realization, with the explicit
once-around parametrization retained by the exported traversal lemmas. -/
def relatorCircleBoundaryHomeomorph  :=
  (relatorCircleCycle w j hn).boundaryHomeomorph

end FiniteChains.PresModel
