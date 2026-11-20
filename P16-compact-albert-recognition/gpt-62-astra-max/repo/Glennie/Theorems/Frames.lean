module

public import Glennie.Native.AlgebraLaws

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Basic.Complex.Basic

public import Mathlib.Tactic.Module

/- Native frame encoder and marginal identities, without spectral assumptions. -/

public section

namespace Glennie
noncomputable section

theorem frame_encoder_trace (p : Fin 3 → Albert) (hp : Frame p) :
    trace (encoder p) = 0 := by
  simp [encoder, hp.trace_one]

theorem frame_encoder_square (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (encoder p) = p 2 + p 0 := by
  simp [encoder, jordan_sub_left, jordan_sub_right, hp.idempotent,
    hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide)]

theorem frame_encoder_cube (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (jordan (encoder p) (encoder p)) = encoder p := by
  grind [frame_encoder_square p hp, encoder, jordan_sub_left, jordan_add_right, hp.idempotent, hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide), sub_zero, zero_sub]

theorem frame_encoder_norm (p : Fin 3 → Albert) (hp : Frame p) :
    inner (encoder p) (encoder p) = 2 := by
  grind [inner, frame_encoder_square p hp, trace_add, hp.trace_one]

theorem frame_projector_first (p : Fin 3 → Albert) (hp : Frame p) :
    (1 / 2 : ℝ) • (jordan (encoder p) (encoder p) - encoder p) = p 0 := by
  rw [frame_encoder_square p hp]
  unfold encoder
  module

theorem frame_projector_middle (p : Fin 3 → Albert) (hp : Frame p) :
    1 - jordan (encoder p) (encoder p) = p 1 := by
  rw [frame_encoder_square p hp, ← hp.sum_unit]
  abel

theorem frame_projector_last (p : Fin 3 → Albert) (hp : Frame p) :
    (1 / 2 : ℝ) • (jordan (encoder p) (encoder p) + encoder p) = p 2 := by
  rw [frame_encoder_square p hp]
  unfold encoder
  module

theorem ledger_cyclic (p q r : Fin 3 → Albert) (i j k : Fin 3) :
    ledger p q r i j k = ledger q r p j k i := by
  change inner (jordan (p i) (q j)) (r k) = inner (jordan (q j) (r k)) (p i)
  rw [inner_jordan_associative, inner_comm]

end
end Glennie
