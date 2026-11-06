module

public import Glennie.Native.AlgebraLaws
public import Glennie.Theorems.ScalarEstimates
public import Mathlib.Tactic.Module

/- Native frame encoder and marginal identities, without spectral assumptions. -/

public section

namespace Glennie

theorem frame_encoder_trace (p : Fin 3 → Albert) (hp : Frame p) :
    trace (encoder p) = 0 := by
  simp [encoder, hp.trace_one]

theorem frame_encoder_square (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (encoder p) = p 2 + p 0 := by
  simp [encoder, jordan_sub_left, jordan_sub_right, hp.idempotent,
    hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide)]

theorem frame_encoder_cube (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (jordan (encoder p) (encoder p)) = encoder p := by
  rw [frame_encoder_square p hp]
  simp [encoder, jordan_sub_left, jordan_add_right, hp.idempotent,
    hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide),
    sub_zero, zero_sub]
  abel

theorem frame_encoder_norm (p : Fin 3 → Albert) (hp : Frame p) :
    inner (encoder p) (encoder p) = 2 := by
  rw [inner, frame_encoder_square p hp, trace_add, hp.trace_one, hp.trace_one]
  norm_num

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

theorem ledger_last_marginal (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    (∑ k, ledger p q r i j k) = inner (p i) (q j) := by
  simp [Fin.sum_univ_three, ledger]
  rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right,
    hr.sum_unit, jordan_unit_right]
  rfl

theorem uniformLedger_pair_overlap (p q r : Fin 3 → Albert)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 := by
  rw [← ledger_last_marginal p q r hr i j]
  simp [UniformLedger] at hu
  simp [hu]
  norm_num

theorem uniformLedger_cyclic (p q r : Fin 3 → Albert)
    (hu : UniformLedger p q r) : UniformLedger q r p := by
  intro j k i
  rw [← ledger_cyclic]
  exact hu i j k

end Glennie
