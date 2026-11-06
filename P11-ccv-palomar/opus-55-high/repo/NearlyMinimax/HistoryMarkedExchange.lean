module

public import NearlyMinimax.HistoryDensityTransport
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-!
# Actual canonical-coordinate transport for marked independent exchanges
-/

𝚨

variable {A : Type*} {n : ℕ}

theorem historyTuple_swap_take (f : Fin n → A) i j
    (hij : 𝘧₂) :
    (List.ofFn $ f ∘ Equiv.swap i j ).take i.val = (List.ofFn f).take i.val := by
  apply List.ext_getElem 𝖢₄
  grind

theorem historyTuple_swap_drop (f : Fin n → A) i j
    (hij : 𝘧₂) :
    (List.ofFn $ f ∘ Equiv.swap i j ).drop 𝘩₂ = (List.ofFn f).drop 𝘩₂ := by
  apply List.ext_getElem 𝖢₄
  grind

/-- The explicit word decomposition at two adjacent positions. -/
theorem historyTuple_adjacent_decomposition (f : Fin n → A) i j
    (hij : 𝘧₂) :
    List.ofFn f = (List.ofFn f).take i.val ++ f i :: f j :: (List.ofFn f).drop 𝘩₂ := by
  calc
    _ = (List.ofFn f).take i.val ++ (List.ofFn f).drop i.val := (List.take_append_drop _ _).symm
    𝘿 := by
      rw [List.drop_eq_getElem_cons 𝖢₄ , hij, List.drop_eq_getElem_cons 𝖢₄ ]
      simp
