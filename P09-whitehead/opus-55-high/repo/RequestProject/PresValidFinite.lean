import RequestProject.PresValidPoset
import RequestProject.PresPosetDimension
import RequestProject.OrderNerveDimension
import RequestProject.OrderNerveRealizationFinite


namespace FiniteChains.PresModel
open Comb CategoryTheory
universe u

instance cPos_finite : Finite CPos := by
  let index : CPos → Fin 4
    | .cor => 0
    | .cmid => 1
    | .cedgL => 2
    | .cedgR => 3
  exact Finite.of_injective index (by
    intro a b h
    grind)

instance rose_finite {α : Type u} [Finite α] : Finite (Rose α) := by
  let decode : Option (α × Option Bool) → Rose α
    | none => .base
    | some (a, none) => .mid a
    | some (a, some b) => .edg a b
  apply Finite.of_surjective decode
  intro r
  cases r with
  | base => tauto
  | mid a => exact ⟨some (a, none), rfl⟩
  | edg a b => exact ⟨some (a, some b), rfl⟩

variable {α J : Type u} (w : J → List (α × Bool))
