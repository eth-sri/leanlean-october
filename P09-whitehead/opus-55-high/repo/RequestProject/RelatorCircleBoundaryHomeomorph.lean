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
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.PresModel
open Comb RelativeAttachment

def cPosCyclicIndex : CPos ≃ Fin 4 where
  toFun
    | .cor => 0
    | .cedgL => 1
    | .cmid => 2
    | .cedgR => 3
  invFun i := ![CPos.cor, CPos.cedgL, CPos.cmid, CPos.cedgR] i
  left_inv t := by aesop
  right_inv i := by fin_cases i <;> rfl

variable {A J : Type} (w : J → List (A × Bool)) (j : J)

def relatorCircleProductEquiv : RelatorCircle w j ≃ Fin (w j).length × CPos where
  toFun x := (⟨x.val.2.1, x.property.2⟩, x.val.2.2)
  invFun x := relatorCirclePoint w j x.1 x.2
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext x.property.1.symm rfl
  right_inv _ := rfl

def relatorCircleIndexEquiv :=
  (relatorCircleProductEquiv w j).trans
    ((Equiv.prodCongr (Equiv.refl _) cPosCyclicIndex).trans finProdFinEquiv)

variable (hn : 0 < (w j).length)

theorem relatorCircleIndex_symm_pair k t :
    (relatorCircleIndexEquiv w j).symm (finProdFinEquiv (k, t)) =
      relatorCirclePoint w j k (cPosCyclicIndex.symm t) := by
  apply (relatorCircleIndexEquiv w j).injective
  rw [Equiv.apply_symm_apply]
  change finProdFinEquiv (k, t) = finProdFinEquiv (k, cPosCyclicIndex (cPosCyclicIndex.symm t))
  simp

def relatorCircleSuccessor (x : RelatorCircle w j) : RelatorCircle w j :=
  let k : Fin (w j).length := ⟨x.val.2.1, x.property.2⟩
  match x.val.2.2 with
  | .cor => relatorCirclePoint w j k .cedgL
  | .cedgL => relatorCirclePoint w j k .cmid
  | .cmid => relatorCirclePoint w j k .cedgR
  | .cedgR => relatorCirclePoint w j
      ⟨(k.val + 1) % (w j).length, Nat.mod_lt _ hn⟩ .cor

theorem relatorCircleSuccessor_comparable x :
    x ≤ relatorCircleSuccessor w j hn x ∨ relatorCircleSuccessor w j hn x ≤ x := by
  rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
  change j' = j at hj
  subst j'
  cases t
  · exact Or.inl (TCirc.cor_le_cedgL w hk)
  · exact Or.inl (TCirc.cmid_le_cedgR w hk)
  · exact Or.inr (TCirc.cmid_le_cedgL w hk)
  · exact Or.inr (TCirc.cor_csucc_le_cedgR w hk)

theorem relatorCircle_le_neighbors a b (hne : a ≠ b) (hab : a ≤ b) :
    relatorCircleSuccessor w j hn a = b ∨ relatorCircleSuccessor w j hn b = a := by
  rcases hab with he | he
  · exact (hne (Subtype.ext he)).elim
  rcases a with ⟨⟨ja, ka, ta⟩, hja, hka⟩
  rcases b with ⟨⟨jb, kb, tb⟩, hjb, hkb⟩
  change ja = j at hja
  change jb = j at hjb
  subst ja
  subst jb
  obtain ⟨_, _, ht⟩ := he
  aesop

theorem relatorCircle_neighbors a b (hne : a ≠ b)
    (hab : a ≤ b ∨ b ≤ a) :
    relatorCircleSuccessor w j hn a = b ∨ relatorCircleSuccessor w j hn b = a := by
  rcases hab with hab | hba
  · exact relatorCircle_le_neighbors w j hn a b hne hab
  · exact (relatorCircle_le_neighbors w j hn b a hne.symm hba).symm

theorem relatorCircleSuccessor_index x :
    (relatorCircleIndexEquiv w j (relatorCircleSuccessor w j hn x)).val =
      if (relatorCircleIndexEquiv w j x).val + 1 < (w j).length * 4 then
        (relatorCircleIndexEquiv w j x).val + 1 else 0 := by
  rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
  change j' = j at hj
  subst j'
  change k < (w j).length at hk
  cases t
  · change 1 + 4 * k = if 0 + 4 * k + 1 < (w j).length * 4 then 0 + 4 * k + 1 else 0
    grind
  · change 3 + 4 * k = if 2 + 4 * k + 1 < (w j).length * 4 then 2 + 4 * k + 1 else 0
    grind
  · change 2 + 4 * k = if 1 + 4 * k + 1 < (w j).length * 4 then 1 + 4 * k + 1 else 0
    grind
  · change 0 + 4 * ((k + 1) % (w j).length) =
      if 3 + 4 * k + 1 < (w j).length * 4 then 3 + 4 * k + 1 else 0
    by_cases hnext : k + 1 < (w j).length
    · rw [Nat.mod_eq_of_lt hnext]
      grind
    · have he : k + 1 = (w j).length := by omega
      rw [he, Nat.mod_self]
      grind

def relatorCircleSize := (w j).length * 4 - 2

include hn in
theorem relatorCircleSize_add_two : relatorCircleSize w j + 2 = (w j).length * 4 := by
  dsimp [relatorCircleSize]
  omega

def relatorCircleEnumeration :=
  (finCongr (relatorCircleSize_add_two w j hn)).trans (relatorCircleIndexEquiv w j).symm

theorem relatorCircleEnumeration_index i :
    (relatorCircleIndexEquiv w j (relatorCircleEnumeration w j hn i)).val = i.val := by
  change (relatorCircleIndexEquiv w j
    ((relatorCircleIndexEquiv w j).symm (Fin.cast (relatorCircleSize_add_two w j hn) i))).val = i.val
  simp

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
  apply Fin.ext
  rw [relatorCircleSuccessor_index, relatorCircleEnumeration_index, relatorCircleEnumeration_index]
  have hN := relatorCircleSize_add_two w j hn
  simp_all

theorem relatorCircle_next_edge a :
    (∃ i : Fin (relatorCircleSize w j + 1),
      a = relatorCircleEnumeration w j hn i.castSucc ∧
        relatorCircleSuccessor w j hn a = relatorCircleEnumeration w j hn i.succ) ∨
    (a = relatorCircleEnumeration w j hn (Fin.last (relatorCircleSize w j + 1)) ∧
      relatorCircleSuccessor w j hn a = relatorCircleEnumeration w j hn 0) := by
  obtain ⟨k, rfl⟩ := (relatorCircleEnumeration w j hn).surjective a
  refine Fin.lastCases ?_ ?_ k
  · exact Or.inr ⟨rfl, relatorCircleEnumeration_last_next w j hn⟩
  · intro i
    exact Or.inl ⟨i, rfl, relatorCircleEnumeration_next w j hn i⟩

def relatorCircleCycle : FinitePosetCycle (RelatorCircle w j) (relatorCircleSize w j) where
  positive := by grind [relatorCircleSize]
  vertex := relatorCircleEnumeration w j hn
  consecutive i := by
    have h := relatorCircleSuccessor_comparable w j hn (relatorCircleEnumeration w j hn i.castSucc)
    grind [relatorCircleEnumeration_next]
  closing := by
    have h := relatorCircleSuccessor_comparable w j hn
      (relatorCircleEnumeration w j hn (Fin.last (relatorCircleSize w j + 1)))
    grind [relatorCircleEnumeration_last_next]
  edges a b hne hab := by
    rcases relatorCircle_neighbors w j hn a b hne hab with h | h
    · rcases relatorCircle_next_edge w j hn a with ⟨i, ha, hb⟩ | ⟨ha, hb⟩
      · simp_all
      simp_all
    · rcases relatorCircle_next_edge w j hn b with ⟨i, hb, ha⟩ | ⟨hb, ha⟩
      · simp_all
      simp_all
  height x := circleDimension w x.val
  height_strict := fun _ _ h => circleDimension_strictMono w h
  height_le x := circleDimension_le_one w x.val

def relatorCircleTraversal := (relatorCircleCycle w j hn).traversal

/-- The actual valid relator-circle realization, with the explicit
once-around parametrization retained by the exported traversal lemmas. -/
def relatorCircleBoundaryHomeomorph :=
  (relatorCircleCycle w j hn).boundaryHomeomorph
