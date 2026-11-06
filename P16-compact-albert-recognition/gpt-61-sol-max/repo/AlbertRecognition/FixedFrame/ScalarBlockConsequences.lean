/- Concrete h0 coarse actions derived from the native scalar blocks.
-/
module

public import AlbertRecognition.FixedFrame.ScalarBlocks
public import AlbertRecognition.FixedFrame.ThreeFrameRelations

@[expose] public section
namespace AlbertRecognition.FixedFrame
section
open Glennie

/-- Actual complementary diagonal coordinates for the zero-based h0 frame. -/
theorem h_half_h0_eq_frameD (j : Fin 3) (hj : 0 ≠ j) :
    h j + (1/2 : ℝ) • h 0 = (if j = 1 then -(3/2 : ℝ) else 3/2) • frameD := by
  fin_cases j
  · exact (hj rfl).elim
  all_goals apply Subtype.ext; apply Albert.ext <;> norm_num [h, e, unit, frameD]

/-- The scalar-block output supplies every native coarse h0 action needed by
three-frame transport. No covariance or invariance is a premise. -/
theorem frame_commutant_h0_coarse_actions (G : Module.End ℝ V)
    (hG : ∀ t : Fin 8, G.comp (frameAction (octBasis t)) =
      (frameAction (octBasis t)).comp G) :
    Nonempty (FrameScalarData G 0) := by
  obtain ⟨a,b,c,ha,hb,h12,hs⟩ := frame_commutant_scalar_blocks G hG
  refine ⟨⟨a,b,c,ha,?_,?_⟩⟩
  · intro j hj
    rw [h_half_h0_eq_frameD j hj, map_smul, hb]
    module
  · intro k u
    fin_cases k
    · exact h12 u
    · simpa [X, frameSpin_apply] using hs (0,u)
    · simpa [X, frameSpin_apply] using hs (u,0)

/-- Concrete h0 coarse data for the arbitrary-cubic Jacobi kernel. The sole
hypothesis is the literal initial-gate equation; all actions are derived. -/
theorem h0_coarse_actions_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    Nonempty (FrameScalarData (KB B (h 0)) 0) := by
  apply frame_commutant_h0_coarse_actions (KB B (h 0))
  intro t
  apply LinearMap.ext
  intro x
  exact h0_frame_action_intertwines_of_A_q_zero B hB (octBasis t) x

end
end AlbertRecognition.FixedFrame
