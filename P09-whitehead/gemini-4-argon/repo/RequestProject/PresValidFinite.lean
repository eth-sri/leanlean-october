module

public import RequestProject.PresConeIntervals
public import RequestProject.PresPosetConnected
public import RequestProject.PresPosetDimension
public import RequestProject.OrderNerveDimension
public import RequestProject.OrderNerveTwoComplex

@[expose] public section

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
    cases a <;> cases b <;> simp_all [index])

instance rose_finite {α : Type u} [Finite α] : Finite (Rose α) := by
  let decode : Option (α × Option Bool) → Rose α
    | none => .base
    | some (a, none) => .mid a
    | some (a, some b) => .edg a b
  apply Finite.of_surjective decode
  intro r
  cases r with
  | base => exact ⟨none, rfl⟩
  | mid a => exact ⟨some (a, none), rfl⟩
  | edg a b => exact ⟨some (a, some b), rfl⟩
