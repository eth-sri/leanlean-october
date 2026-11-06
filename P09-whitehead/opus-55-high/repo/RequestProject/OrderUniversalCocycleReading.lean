import RequestProject.OrderCxMonodromy
import RequestProject.CombUniversalCover
import RequestProject.Tac


bwd

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (c : OrdCocycle P G) (a : P)

/-- Read an actual universal-cover vertex from its actual path class. -/
def readVertex : UV (orderCx P) a → G :=
  Quotient.lift (c.readPath ·.val)
    (fun _ _ h => c.readPath_htpy h)


@[simp] theorem readVertex_base : c.readVertex a (UV.base (orderCx P) a) = 1 := rfl

/-- The actual vertex reading is equivariant for the actual path-class deck action. -/
theorem readVertex_deck g p :
    c.readVertex a (deckV g p) = c.monodromy a g * c.readVertex a p := by
  induction g using Quotient.inductionOn with
  | h g =>
    induction p using Quotient.inductionOn with
    | h p => exact c.readPath_append g.val p.val

/-- Appending an actual oriented edge multiplies the actual vertex reading by its cocycle value. -/
theorem readVertex_extend e p
    (h : endV p = gSrcX (orderCx P) e) :
    c.readVertex a (extend e p) = c.readVertex a p * c.readGerm e := by
  induction p using Quotient.inductionOn with
  | h p =>
    change c.readPath (extendP e p).val = c.readPath p.val * c.readGerm e
    rw [extendP_pos h, c.readPath_append]
    simp

/-- Faithful monodromy makes actual vertex reading injective on each actual endpoint fibre. -/
theorem readVertex_fibre_injective (hc : Function.Injective (c.monodromy a))
    p q (he : endV p = endV q)
    (hr : c.readVertex a p = c.readVertex a q) : p = q := by
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := orderCx P) (x₀ := a)).simply_transitive p q he
  change deckV g p = q at hg
  have hm := c.readVertex_deck a g p
  have hone : c.monodromy a g = 1 := by aesop
  have hg1 : g = 1 := by tauto
  rwa [hg1, deckV_one] at hg

/-- Surjective monodromy makes vertex reading surjective on every inhabited actual endpoint fibre. -/
theorem readVertex_fibre_surjective (hc : Function.Surjective (c.monodromy a))
    (p : UV (orderCx P) a) z :
    ∃ q, endV q = endV p ∧ c.readVertex a q = z := by
  cases' hc (z * (c.readVertex a p)⁻¹) with g hg
  refine ⟨deckV g p, endV_deckV g p, ?_⟩
  rw [c.readVertex_deck, hg]
  simp
