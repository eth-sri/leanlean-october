import Mathlib.Tactic

import RequestProject.TopologicalSingular.SquareSubdivisionGeometry

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

variable (p q : GenLoop (Fin 2) X x)
theorem transAt_leftRectangle  :
    (GenLoop.transAt 0 p q).val.comp (leftRectangle squareHalf) = p.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p (Function.update (leftRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (leftRectangle squareHalf z) 0)))
    else q (Function.update (leftRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (leftRectangle squareHalf z) 0 - 1)))) = p z
  have hh : ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2 := by
    change (1 / 2 : ℝ) * (z 0 : ℝ) ≤ 1 / 2
    nlinarith [(z 0).property.2]
  rw [if_pos hh]
  apply congrArg p
  funext i
  fin_cases i
  · simp_all [leftRectangle, squareHalf]
  · simp [leftRectangle]

theorem rightRectangle_half_coordinate (z : Fin 2 → I) :
    ((rightRectangle squareHalf z) 0 : ℝ) = (1 + (z 0 : ℝ)) / 2 := by
  dsimp [FiniteChains.TopologicalSingular.rightRectangle, FiniteChains.TopologicalSingular.squareHalf]
  ring

theorem transAt_rightRectangle  :
    (GenLoop.transAt 0 p q).val.comp (rightRectangle squareHalf) = q.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((rightRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p (Function.update (rightRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (rightRectangle squareHalf z) 0)))
    else q (Function.update (rightRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (rightRectangle squareHalf z) 0 - 1)))) = q z
  split_ifs with h
  · have hz : z 0 = 0 := by
      apply Subtype.ext
      have hr := rightRectangle_half_coordinate z
      change (z 0 : ℝ) = 0
      nlinarith [(z 0).property.1]
    have he : 2 * ((rightRectangle squareHalf z) 0 : ℝ) = 1 := by
      simp_all [rightRectangle_half_coordinate]
    calc
      _ = x := GenLoop.boundary p _ ⟨0, Or.inr (by
        simp_all )⟩
      _ = q z := (GenLoop.boundary q z ⟨0, Or.inl hz⟩).symm
  · apply congrArg q
    funext i
    fin_cases i
    · simp only [Function.update_apply]
      rw [if_pos (by rfl)]
      have he : 2 * ((rightRectangle squareHalf z) 0 : ℝ) - 1 = (z 0 : ℝ) := by
        rw [rightRectangle_half_coordinate]
        ring
      rw [he, Set.projIcc_of_mem zero_le_one (z 0).property]
      exact Subtype.ext rfl
    · simp [rightRectangle]

end FiniteChains.TopologicalSingular
