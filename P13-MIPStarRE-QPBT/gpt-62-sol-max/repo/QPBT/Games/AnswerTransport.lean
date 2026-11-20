module

public import QPBT.Games.DistanceTheorems.TensorSupport

/-! Pushforward of a bipartite outcome law by local answer maps. -/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus

/-- Summing over fibers of the two answer maps pushes events back to the original labels. -/
private theorem sum_event_fibers {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]
    (f : α → γ) (g : β → δ) (w : α → β → ℝ) (E : γ → δ → Prop) [DecidableRel E] :
    (∑ c, ∑ d, if E c d then
      ∑ a ∈ Finset.univ.filter (fun a => f a = c),
        ∑ b ∈ Finset.univ.filter (fun b => g b = d), w a b else 0) =
      ∑ a, ∑ b, if E (f a) (g b) then w a b else 0 := by
  simp_rw [Finset.ite_sum_zero]
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
  simp only [Finset.sum_fiberwise_apply]

/-- A strategy obtained by local postprocessing measures the pullback of each answer event. -/
theorem outcomeEventWeight_postprocess {G H : Game} (S : Strategy G) (T : Strategy H)
    (x : G.QuestionA) (y : G.QuestionB) (u : H.QuestionA) (v : H.QuestionB)
    (f : G.AnswerA → H.AnswerA) (g : G.AnswerB → H.AnswerB)
    (h : ∀ a b, outcomeWeight T u v a b = stateQForm S.ψ
      (heteroKron (((S.A x).postprocess f).effect a) (((S.B y).postprocess g).effect b)))
    (E : H.AnswerA → H.AnswerB → Prop) [DecidableRel E] :
    outcomeEventWeight T u v E = outcomeEventWeight S x y (fun a b => E (f a) (g b)) := by
  unfold outcomeEventWeight
  simp_rw [h, Measurement.postprocess_effect,
    heteroKron_finset_sum_left, stateQForm_finset_sum,
    heteroKron_finset_sum_right, stateQForm_finset_sum]
  exact sum_event_fibers f g (outcomeWeight S x y) E

end MIPStarRE.QPBT
