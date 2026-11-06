module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.S2.MassDecomposition

public import Erdos821.P3Clean.Structure

/-! Splitting the fixed small labels from the variable big labels. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

abbrev SmallLabels (P : PrimeGroups) (M ) :=
  (g : P.SmallGroup) → Fin M → P.Prime g.val

def restrictSmall {M } (a : P.Labels M) : SmallLabels P M := fun g => a g.val

def joinLabels {M } (a : SmallLabels P M) (b : P.BigLabels M) : P.Labels M :=
  fun g => if hg : P.big g = true then b ⟨g, hg⟩ else a ⟨g, by
    cases h : P.big g <;> simp_all⟩

section
variable {M : ℕ} (a : SmallLabels P M) (b : P.BigLabels M)

theorem joinLabels_small      
    (g : P.SmallGroup) : joinLabels a b g.val = a g := by
  simp [joinLabels, g.property]

theorem joinLabels_big      
    (g : P.BigGroup) : joinLabels a b g.val = b g := by
  simp [joinLabels, g.property]

end

def splitLabels (P : PrimeGroups) (M : ℕ) : P.Labels M ≃ SmallLabels P M × P.BigLabels M where
  toFun a := (restrictSmall a, P.restrictBig a)
  invFun a := joinLabels a.1 a.2
  left_inv := by
    grind [joinLabels, restrictSmall, PrimeGroups.restrictBig]
  right_inv := by
    intro a
    apply Prod.ext
    · funext g
      exact joinLabels_small a.1 a.2 g
    · funext g
      exact joinLabels_big a.1 a.2 g

theorem prod_group_split {R : Type*} [CommMonoid R] (f : P.Group → R) :
    (∏ g : P.Group, f g) =
      (∏ g : P.SmallGroup, f g.val) * ∏ g : P.BigGroup, f g.val := by solve_by_elim [_root_.Erdos821.S2Core.primeGroups_prod_split]

def smallPrefixProduct {M } (J ) (hJM : J ≤ M) (a : SmallLabels P M)  :=
  ∏ g : P.SmallGroup, ∏ j : Fin J, (a g ⟨j.val, lt_of_lt_of_le j.isLt hJM⟩).val

section
variable {J ell m : ℕ} (ν : Pattern P J ell m)

theorem D_split    
     a   u  :
    ν.D a u = smallPrefixProduct J (Nat.le_add_right J ell) (restrictSmall a) *
      ν.DBig (P.restrictBig a) (fun g => u g.val) := by
  unfold Pattern.D Pattern.DBig smallPrefixProduct
  rw [prod_group_split]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  have hs := ν.small g.val g.property
  simp [hs, Pattern.slot, restrictSmall]

theorem compatible_split    
     a b  :
    ν.compatible a b ↔
      (∀ g : P.SmallGroup, ∀ j : Fin J, a g.val (ν.slot j) = b g.val (ν.slot j)) ∧
        ν.matchesBig (P.restrictBig a) (P.restrictBig b) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro g j
      apply h g.val (ν.slot j)
      exact ⟨j, rfl, by simp [ν.small g.val g.property]⟩
    · intro g i hi
      exact h g.val i hi
  · rintro ⟨hs, hb⟩ g i hi
    by_cases hg : P.big g = true
    · exact hb ⟨g, hg⟩ i hi
    · have hsmall : P.big g = false := by cases h : P.big g <;> simp_all
      obtain ⟨j, rfl, _⟩ := hi
      exact hs ⟨g, hsmall⟩ j

theorem ban_split    
     a b   u  :
    ν.ban a b u ↔ ∀ g : P.BigGroup, ∀ i ∈ ν.changed g.val,
      ∀ j, u g.val i ≠ a g.val j ∧ u g.val i ≠ b g.val j := by
  constructor
  · intro h g i hi j
    exact h g.val i hi j
  · intro h g i hi j
    by_cases hg : P.big g = true
    · exact h ⟨g, hg⟩ i hi j
    · have hsmall : P.big g = false := by cases hh : P.big g <;> simp_all
      rw [ν.small g hsmall] at hi
      exact False.elim (Finset.notMem_empty i hi)

end

end Erdos821.P3Clean
