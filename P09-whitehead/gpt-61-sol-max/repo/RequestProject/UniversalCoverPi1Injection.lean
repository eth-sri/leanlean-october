import Mathlib.Tactic

import RequestProject.CombPi2

/-! An injective fundamental-group inclusion embeds its genuine universal-cover vertices. -/
namespace FiniteChains.Comb
variable {X Y : Complex2.{u}}

theorem univLiftV_deckV (f : Hom X Y) (a : X.V) (g : Pi1 X a) (v : UV X a) :
    univLiftV a f (deckV g v) = deckV (pi1Map f a g) (univLiftV a f v) := by
  induction g using Quotient.ind with
  | _ p =>
    induction v using UV.ind with
    | h q =>
      dsimp
      congr 1
      apply Subtype.ext
      exact mapPath_append f p.1 q.1

theorem deckV_free (a : X.V) (g : Pi1 X a) (v : UV X a)
    (h : deckV g v = v) : g = 1 := by
  obtain ⟨d, _, hu⟩ := (isRegular_univProj (X := X) (x₀ := a)).simply_transitive v v rfl
  exact (hu g h).trans (hu 1 (deckV_one v)).symm

end FiniteChains.Comb
