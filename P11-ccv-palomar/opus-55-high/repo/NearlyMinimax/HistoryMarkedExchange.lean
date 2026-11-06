module

public import NearlyMinimax.HistoryDensityTransport

@[expose] public section

/-!
# Actual canonical-coordinate transport for marked independent exchanges
-/

noncomputable section
namespace NearlyMinimax

variable {A : Type*} {n : ℕ}

theorem historyTuple_swap_take (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    (List.ofFn (f ∘ Equiv.swap i j)).take i.val = (List.ofFn f).take i.val := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_take, List.getElem_ofFn, Function.comp_def]
  have hkbound : k < i.val := by
    simp only [List.length_take, List.length_ofFn] at hk
    exact hk.trans_le (Nat.min_le_left _ _)
  have hki : (⟨k, by omega⟩ : Fin n) ≠ i := by intro he; have hv : k = i.val := congrArg Fin.val he; omega
  have hkj : (⟨k, by omega⟩ : Fin n) ≠ j := by intro he; have hv : k = j.val := congrArg Fin.val he; omega
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem historyTuple_swap_drop (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    (List.ofFn (f ∘ Equiv.swap i j)).drop (j.val + 1) = (List.ofFn f).drop (j.val + 1) := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_drop, List.getElem_ofFn, Function.comp_def]
  have hkbound : j.val + 1 + k < n := by simp only [List.length_drop, List.length_ofFn] at hk; omega
  have hki : (⟨j.val + 1 + k, hkbound⟩ : Fin n) ≠ i := by intro he; have hv : j.val + 1 + k = i.val := congrArg Fin.val he; omega
  have hkj : (⟨j.val + 1 + k, hkbound⟩ : Fin n) ≠ j := by intro he; have hv : j.val + 1 + k = j.val := congrArg Fin.val he; omega
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- The explicit word decomposition at two adjacent positions. -/
theorem historyTuple_adjacent_decomposition (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    List.ofFn f = (List.ofFn f).take i.val ++ f i :: f j :: (List.ofFn f).drop (j.val + 1) := by
  have hi : i.val < (List.ofFn f).length := by simp
  have hj : j.val < (List.ofFn f).length := by simp
  calc
    _ = (List.ofFn f).take i.val ++ (List.ofFn f).drop i.val := (List.take_append_drop _ _).symm
    _ = _ := by
      rw [List.drop_eq_getElem_cons hi, hij, List.drop_eq_getElem_cons hj]
      simp only [List.getElem_ofFn, Fin.eta]

end NearlyMinimax
