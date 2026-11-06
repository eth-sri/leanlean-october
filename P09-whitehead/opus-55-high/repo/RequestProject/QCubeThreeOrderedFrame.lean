import RequestProject.QCubeThreeComponentRecovery


/-! Existence of decreasing actual coordinate frames for three-dimensional cubes. -/
namespace FiniteChains.Davis
open RACG
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_ordered_frame (c : QCube A) (hc : c.spx.card = 3) :
    ∃ u v w, v < u ∧ w < v ∧ c.spx = {u, v, w} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Finset.card_eq_three.mp hc
  rcases lt_or_gt_of_ne hxy with hxy | hxy <;>
    rcases lt_or_gt_of_ne hxz with hxz | hxz <;>
    rcases lt_or_gt_of_ne hyz with hyz | hyz
  · grind
  · grind
  · grind
  · grind
  · grind
  · tauto
  · grind
  tauto
