import Mathlib.Tactic

import RequestProject.GenusApply
import RequestProject.PresPosetConnected
import RequestProject.PresPosetPartialOrder

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
  (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- Nonempty representatives retaining the prescribed genus surface word. -/
noncomputable def genusNonemptyW : Jr ⊕ PUnit → List (α × Bool) :=
  Sum.elim (fun j => presNonemptyWords ρ (a 0) (Sum.inl j)) (fun _ => surfWord a b q)

theorem genusNonemptyW_ne_nil (j : Jr ⊕ PUnit) : genusNonemptyW ρ a b q j ≠ [] := by
  cases j with
  | inl j => solve_by_elim [FiniteChains.PresModel.presNonemptyWords_ne_nil]
  | inr s =>
    intro h
    have hl := congrArg List.length h
    change (surfWord a b q).length = 0 at hl
    rw  [surfWord_length] at hl
    have := Nat.pos_of_neZero q
    omega

omit [NeZero q] in
theorem mk_genusNonemptyW
    (hr : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q)) :
    ∀ j, FreeGroup.mk (genusNonemptyW ρ a b q j) = ρ j := by
  rintro (j | s)
  · solve_by_elim [FiniteChains.PresModel.mk_presNonemptyWords]
  · cases s
    exact hr.symm

abbrev genusNonemptyW_isConnected  :=
  presPos_isConnected _ (genusNonemptyW_ne_nil ρ a b q)

noncomputable abbrev genusNonemptyAtt  :=
  surfAtt (w := genusNonemptyW ρ a b q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM a b q) (genus_hvlab a b q) (genus_helb a b q) (gc q)

theorem genusNonemptyAtt_base :
    genusNonemptyAtt ρ a b q (gBase q) = ptBase (genusNonemptyW ρ a b q) := by
  rw  [gBase, att_V, vertLab_of_even (by rfl)]
  rfl

end FiniteChains.Davis.Genus
