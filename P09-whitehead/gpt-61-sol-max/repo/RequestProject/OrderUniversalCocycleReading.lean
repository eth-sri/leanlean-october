import Mathlib.Tactic

import RequestProject.OrderCxMonodromy
import RequestProject.CombUniversalCover

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (c : OrdCocycle P G) (a : P)

/-- Read an actual universal-cover vertex from its actual path class. -/
def readVertex  :=
  Quotient.lift (fun p : PathFrom (orderCx P) a => c.readPath p.val)
    (fun _ _ h => c.readPath_htpy h)



@[simp] theorem readVertex_base : c.readVertex a (UV.base (orderCx P) a) = 1 := rfl

/-- The actual vertex reading is equivariant for the actual path-class deck action. -/
theorem readVertex_deck (g : Pi1 (orderCx P) a) (p : UV (orderCx P) a) :
    c.readVertex a (deckV g p) = c.monodromy a g * c.readVertex a p := by
  induction g using Quotient.inductionOn with
  | h g =>
    induction p using Quotient.inductionOn with
    | h p => exact c.readPath_append g.val p.val

/-- Appending an actual oriented edge multiplies the actual vertex reading by its cocycle value. -/
theorem readVertex_extend (e : (orderCx P).E × Bool) (p : UV (orderCx P) a)
    (h : endV p = germSrc (orderCx P).src (orderCx P).tgt e) :
    c.readVertex a (extend e p) = c.readVertex a p * c.readGerm e := by
  induction p using Quotient.inductionOn with
  | h p =>
    change c.readPath (extendP e p).val = c.readPath p.val * c.readGerm e
    rw [extendP_pos h, c.readPath_append]
    simp 

/-- Faithful monodromy makes actual vertex reading injective on each actual endpoint fibre. -/
theorem readVertex_fibre_injective (hc : Function.Injective (c.monodromy a))
    (p q : UV (orderCx P) a) (he : endV p = endV q)
    (hr : c.readVertex a p = c.readVertex a q) : p = q := by
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := orderCx P) (x₀ := a)).simply_transitive p q he
  change deckV g p = q at hg
  have hm := c.readVertex_deck a g p
  rw [hg, ← hr] at hm
  have hone  := mul_right_cancel
    (hm.symm.trans (one_mul (c.readVertex a p)).symm)
  have hg1  := hc (hone.trans (map_one (c.monodromy a)).symm)
  rw [hg1, deckV_one] at hg
  exact hg

/-- Surjective monodromy makes vertex reading surjective on every inhabited actual endpoint fibre. -/
theorem readVertex_fibre_surjective (hc : Function.Surjective (c.monodromy a))
    (p : UV (orderCx P) a) (z : G) :
    ∃ q : UV (orderCx P) a, endV q = endV p ∧ c.readVertex a q = z := by
  obtain ⟨g, hg⟩ := hc (z * (c.readVertex a p)⁻¹)
  refine ⟨deckV g p, endV_deckV g p, ?_⟩
  rw [c.readVertex_deck, hg]
  simp 

end FiniteChains.Comb.OrdCocycle
