import Mathlib.Tactic

import RequestProject.QCubeThreeComponentRecovery

/-! Existence of decreasing actual coordinate frames for three-dimensional cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_ordered_frame (c : QCube A) (hc : c.spx.card = 3) :
    ∃ u v w : V, v < u ∧ w < v ∧ c.spx = {u, v, w} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Finset.card_eq_three.mp hc
  have perm (a b d : V) (hp : ∀ t : V, t = x ∨ t = y ∨ t = z ↔
      t = a ∨ t = b ∨ t = d) : c.spx = {a, b, d} := by
    aesop
  rcases lt_or_gt_of_ne hxy with hxy | hxy <;>
    rcases lt_or_gt_of_ne hxz with hxz | hxz <;>
    rcases lt_or_gt_of_ne hyz with hyz | hyz
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · exact ⟨x, y, z, hxy, hyz, hs⟩

end FiniteChains.Davis
