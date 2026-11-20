module

public import NearlyMinimax.HistoryDensityTransport

@[expose] public section

/-!
# Actual canonical-coordinate transport for marked independent exchanges
-/

noncomputable section
namespace NearlyMinimax

variable {A : Type*} {n : ℕ}

section
variable (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val)
include hij

theorem historyTuple_swap_take :
    (List.ofFn (f ∘ Equiv.swap i j)).take i.val = (List.ofFn f).take i.val := by
  apply List.ext_getElem (by simp)
  grind

theorem historyTuple_swap_drop :
    (List.ofFn (f ∘ Equiv.swap i j)).drop (j.val + 1) = (List.ofFn f).drop (j.val + 1) := by
  apply List.ext_getElem (by simp)
  grind

/-- The explicit word decomposition at two adjacent positions. -/
theorem historyTuple_adjacent_decomposition :
    List.ofFn f = (List.ofFn f).take i.val ++ f i :: f j :: (List.ofFn f).drop (j.val + 1) := by
  have hi : i.val < (List.ofFn f).length := by simp
  have hj : j.val < (List.ofFn f).length := by simp
  calc
    _ = (List.ofFn f).take i.val ++ (List.ofFn f).drop i.val := (List.take_append_drop _ _).symm
    _ = _ := by
      simp [List.drop_eq_getElem_cons hi, hij, List.drop_eq_getElem_cons hj]

end

end NearlyMinimax
