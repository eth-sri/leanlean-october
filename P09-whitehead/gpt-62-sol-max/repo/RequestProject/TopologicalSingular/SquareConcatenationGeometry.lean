module

public import RequestProject.TopologicalSingular.SquareSubdivisionGeometry

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

private theorem update_rectangle {z w : Fin 2 → I} (h : w 1 = z 1) {r : ℝ}
    (hr : r = z 0) : Function.update w 0 (Set.projIcc 0 1 zero_le_one r) = z := by
  rw [hr]
  funext i
  fin_cases i <;> simp [h]

private theorem transAt_comp_apply (p q : GenLoop (Fin 2) X x)
    (F : C((Fin 2 → I), Fin 2 → I)) (z : Fin 2 → I) :
    ((GenLoop.transAt 0 p q).val.comp F) z =
      if (F z 0 : ℝ) ≤ 1 / 2 then
        p (Function.update (F z) 0 (Set.projIcc 0 1 zero_le_one (2 * F z 0)))
      else q (Function.update (F z) 0 (Set.projIcc 0 1 zero_le_one (2 * F z 0 - 1))) := rfl

theorem transAt_leftRectangle (p q : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 p q).val.comp (leftRectangle squareHalf) = p.val := by
  apply ContinuousMap.ext
  intro z
  rw [transAt_comp_apply]
  have hh : ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2 := by
    change (1 / 2 : ℝ) * (z 0) ≤ 1 / 2
    nlinarith [(z 0).property.2]
  rw [if_pos hh]
  apply congrArg p (update_rectangle (z := z) (w := leftRectangle squareHalf z) rfl ?_)
  change 2 * ((1 / 2) * (z 0 : ℝ)) = _
  ring

theorem rightRectangle_half_coordinate (z : Fin 2 → I) :
    ((rightRectangle squareHalf z) 0 : ℝ) = (1 + (z 0 : ℝ)) / 2 := by
  change 1 - ((1 - (1 / 2 : ℝ)) * (1 - (z 0))) = _
  ring

theorem transAt_rightRectangle (p q : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 p q).val.comp (rightRectangle squareHalf) = q.val := by
  apply ContinuousMap.ext
  intro z
  rw [transAt_comp_apply]
  split_ifs with h
  · have hz : z 0 = 0 := by
      apply Subtype.ext
      have hr := rightRectangle_half_coordinate z
      change (z 0 : ℝ) = 0
      nlinarith [(z 0).property.1]
    have he : 2 * ((rightRectangle squareHalf z) 0 : ℝ) = 1 := by
      simp [rightRectangle_half_coordinate, hz]
    calc
      _ = x := GenLoop.boundary p _ ⟨0, Or.inr (by
        simp [he] )⟩
      _ = q z := (GenLoop.boundary q z ⟨0, Or.inl hz⟩).symm
  · apply congrArg q (update_rectangle (z := z) (w := rightRectangle squareHalf z) rfl ?_)
    rw [rightRectangle_half_coordinate]
    ring

end FiniteChains.TopologicalSingular
