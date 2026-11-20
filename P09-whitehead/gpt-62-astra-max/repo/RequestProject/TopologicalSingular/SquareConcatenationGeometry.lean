module

public import RequestProject.TopologicalSingular.SquareSubdivisionGeometry

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem transAt_leftRectangle (p q : GenLoop _ X x) :
    (GenLoop.transAt 0 p q).val.comp (leftRectangle squareHalf) = p.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p _
    else q _) = p z
  have hh : ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2 := by
    change (1 / 2) * (z 0 : ℝ) ≤ 1 / 2
    grind
  rw [if_pos hh]
  apply congrArg p
  funext i
  fin_cases i
  · simp only [Function.update_apply]
    have he : 2 * ((leftRectangle squareHalf z) 0) = (z 0 : ℝ) := by
      change 2 * ((1 / 2) * (z 0 : ℝ)) = _
      ring
    simp_all
  · rfl

theorem rightRectangle_half_coordinate (z : Fin 2 → I) :
    ((rightRectangle squareHalf z) 0) = (1 + (z 0 : ℝ)) / 2 := by
  change 1 - ((1 - (1 / 2)) * (1 - (z 0 : ℝ))) = _
  ring

theorem transAt_rightRectangle (p q : GenLoop _ X x) :
    (GenLoop.transAt 0 p q).val.comp (rightRectangle squareHalf) = q.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((rightRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p _
    else q _) = q z
  split_ifs with h
  · have hz : z 0 = 0 := by
      apply Subtype.ext
      have hr := rightRectangle_half_coordinate z
      change (z 0 : ℝ) = 0
      grind
    have he : 2 * ((rightRectangle squareHalf z) 0 : ℝ) = 1 := by
      rw [rightRectangle_half_coordinate, hz]
      norm_num
    calc
      _ = x := GenLoop.boundary p _ ⟨0, Or.inr (by
        simp_all )⟩
      _ = q z := (GenLoop.boundary q z ⟨0, Or.inl hz⟩).symm
  · apply congrArg q
    funext i
    fin_cases i
    · simp only [Function.update_apply]
      have he : 2 * ((rightRectangle squareHalf z) 0) - 1 = (z 0 : ℝ) := by
        rw [rightRectangle_half_coordinate]
        ring
      simp_all
    · rfl

end FiniteChains.TopologicalSingular
