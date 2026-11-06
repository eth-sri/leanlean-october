/- Actual three-frame coarse data from the unrestricted Jacobi kernel.
Both cyclic steps use pullbacks of the arbitrary cubic, never its invariance. -/
module

public import AlbertRecognition.FixedFrame.CyclicPullback
public import AlbertRecognition.FixedFrame.ScalarBlockConsequences
public import AlbertRecognition.FixedFrame.ThreeFrameRelations

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

private def cycleData (B : SymmetricCubic) (i : Fin 3)
    (d : FrameScalarData (KB (pullbackCubic cyclicV B) (h i)) i) :
    FrameScalarData (KB B (h (i+1))) (i+1) where
  a := d.a
  b := d.b
  c := d.c
  on_h_self := by
    simpa only [show automorphismV cyclicAutomorphism = cyclicV from rfl, cyclicV_h] using
      scalar_action_of_pullback cyclicAutomorphism B _ _ _ d.on_h_self
  on_complementary_diagonal := by
    intro j hj
    have hk : i ≠ j - 1 := mt eq_sub_iff_add_eq.mp hj
    have hh := scalar_action_of_pullback cyclicAutomorphism B _ _ _
      (d.on_complementary_diagonal (j-1) hk)
    simpa only [show automorphismV cyclicAutomorphism = cyclicV from rfl, map_add, map_smul, cyclicV_h, sub_add_cancel] using hh
  on_X := by
    intro k u
    have hh := scalar_action_of_pullback cyclicAutomorphism B _ _ _
      (d.on_X (k-1) (if k = 0 then u else octConj u))
    fin_cases i <;> fin_cases k <;> simpa [show automorphismV cyclicAutomorphism = cyclicV from rfl, Fin.neg_def, X] using hh

theorem threeFrameScalarData_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : Nonempty (ThreeFrameScalarData B) := by
  let PB := pullbackCubic cyclicV B
  have hPB := A_q_pullback_zero cyclicAutomorphism B hB
  obtain ⟨d0⟩ := h0_coarse_actions_of_A_q_zero B hB
  obtain ⟨d1⟩ := h0_coarse_actions_of_A_q_zero PB hPB
  obtain ⟨d2⟩ := h0_coarse_actions_of_A_q_zero (pullbackCubic cyclicV PB)
    (A_q_pullback_zero cyclicAutomorphism PB hPB)
  exact ⟨Fin.cases d0 (Fin.cases (cycleData B 0 d1)
    (Fin.cases (cycleData B 1 (cycleData PB 0 d2)) (fun i => Fin.elim0 i)))⟩

end
end AlbertRecognition.FixedFrame
