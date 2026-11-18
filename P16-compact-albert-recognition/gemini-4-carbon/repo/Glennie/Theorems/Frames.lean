module

public import Glennie.Native.CubicIdentity

@[expose] public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000

def quatI : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def quatJ : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def quatK : Quaternion ℝ := ⟨0, 0, 0, 1⟩
def octI : Octonion := (quatI, 0)
def octJ : Octonion := (quatJ, 0)
def octK : Octonion := (quatK, 0)
def octL : Octonion := (0, 1)
def octJL : Octonion := (0, quatJ)
def witnessX : Albert := ⟨-1, 0, 1, 0, 0, 0⟩
def witnessY : Albert := ⟨0, 0, 0, octScalar 1, octI, octScalar 1⟩
def witnessZ : Albert := ⟨0, 0, 0, octJL, -octL, -octK⟩

theorem frame_encoder_trace (p : Fin 3 → Albert) (hp : Frame p) : trace (encoder p) = 0 := by
  simp [encoder, hp.trace_one]

theorem frame_encoder_square (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (encoder p) = p 2 + p 0 := by
  simp [encoder, jordan_sub_left, jordan_sub_right, hp.idempotent, hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide)]

theorem frame_encoder_cube (p : Fin 3 → Albert) (hp : Frame p) :
    jordan (encoder p) (jordan (encoder p) (encoder p)) = encoder p := by
  rw [frame_encoder_square p hp]
  simp only [encoder, jordan_sub_left, jordan_add_right, hp.idempotent,
    hp.orthogonal 2 0 (by decide), hp.orthogonal 0 2 (by decide), sub_zero, zero_sub]; abel

theorem frame_encoder_norm (p : Fin 3 → Albert) (hp : Frame p) : inner (encoder p) (encoder p) = 2 := by
  rw [inner, frame_encoder_square p hp, trace_add, hp.trace_one, hp.trace_one]; norm_num

theorem frame_projector_first (p : Fin 3 → Albert) (hp : Frame p) :
    (1 / 2 : ℝ) • (jordan (encoder p) (encoder p) - encoder p) = p 0 := by
  rw [frame_encoder_square p hp]; unfold encoder; module

theorem frame_projector_middle (p : Fin 3 → Albert) (hp : Frame p) :
    1 - jordan (encoder p) (encoder p) = p 1 := by
  rw [frame_encoder_square p hp, ← hp.sum_unit]; abel

theorem frame_projector_last (p : Fin 3 → Albert) (hp : Frame p) :
    (1 / 2 : ℝ) • (jordan (encoder p) (encoder p) + encoder p) = p 2 := by
  rw [frame_encoder_square p hp]; unfold encoder; module

theorem ledger_cyclic (p q r : Fin 3 → Albert) (i j k : Fin 3) :
    ledger p q r i j k = ledger q r p j k i := by
  change inner (jordan (p i) (q j)) (r k) = inner (jordan (q j) (r k)) (p i)
  rw [inner_jordan_associative, inner_comm]

theorem ledger_last_marginal (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    (∑ k, ledger p q r i j k) = inner (p i) (q j) := by
  simp only [Fin.sum_univ_three, ledger]
  rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right, hr.sum_unit, jordan_unit_right]; rfl

theorem uniformLedger_pair_overlap (p q r : Fin 3 → Albert)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) : inner (p i) (q j) = 1 / 3 := by
  rw [← ledger_last_marginal p q r hr i j]; simp [UniformLedger] at hu; simp [hu]; norm_num

theorem uniformLedger_cyclic (p q r : Fin 3 → Albert) (hu : UniformLedger p q r) : UniformLedger q r p :=
  fun j k i => (ledger_cyclic p q r i j k).symm.trans (hu i j k)

def newtonCubicNorm (x : Albert) : ℝ :=
  ((trace x) ^ 3 - 3 * trace x * trace (jordan x x) + 2 * trace (jordan x (jordan x x))) / 6

theorem newtonCubicNorm_coordinates (x : Albert) :
    newtonCubicNorm x = x.d0 * x.d1 * x.d2 - x.d0 * octNormSq x.o12 -
      x.d1 * octNormSq x.o02 - x.d2 * octNormSq x.o01 +
      2 * octRe (octMul (octMul x.o01 x.o12) (octConj x.o02)) := by
  simp [newtonCubicNorm, trace, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, octRe, octNormSq, Quaternion.normSq_def', smul_eq_mul]; ring

theorem frame_encoder_cubicNorm (p : Fin 3 → Albert) (hp : Frame p) : newtonCubicNorm (encoder p) = 0 := by
  simp [newtonCubicNorm, frame_encoder_trace p hp, frame_encoder_cube p hp]

theorem newtonCubicNorm_smul (a : ℝ) (x : Albert) : newtonCubicNorm (a • x) = a ^ 3 * newtonCubicNorm x := by
  simp only [newtonCubicNorm, jordan_smul_left, jordan_smul_right, trace_smul, smul_smul]; ring

def projectorFrame (x : Albert) : Fin 3 → Albert :=
  ![(1 / 2 : ℝ) • (jordan x x - x), 1 - jordan x x, (1 / 2 : ℝ) • (jordan x x + x)]

theorem projectorFrame_encoder (x : Albert) : encoder (projectorFrame x) = x := by
  simp only [encoder, projectorFrame, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; module

theorem projectorFrame_is_frame (x : Albert) (ht : trace x = 0) (hn : inner x x = 2) (hc0 : newtonCubicNorm x = 0) :
    Frame (projectorFrame x) := by
  have hs : trace (jordan x x) = 2 := hn
  have hc : jordan x (jordan x x) = x := by
    have hcb : trace (jordan x (jordan x x)) = 0 := by rw [newtonCubicNorm, ht] at hc0; linarith
    have hr := cubicResidual_eq_zero x
    simp only [cubicResidual, ht, hs, hcb] at hr
    have h6 : (6 : ℝ) • (jordan x (jordan x x) - x) = 0 := by convert hr using 1; module
    exact sub_eq_zero.mp (by simpa [smul_smul] using congrArg ((1 / 6 : ℝ) • ·) h6)
  have h4 : jordan (jordan x x) (jordan x x) = jordan x x := by rw [jordan_identity x x, hc]
  have hsx : jordan (jordan x x) x = x := by rw [jordan_comm, hc]
  refine ⟨fun i => by fin_cases i <;> norm_num [projectorFrame, trace_smul, trace_add, trace_sub, trace_unit, ht, hs],
    fun i => by fin_cases i <;> simp only [Fin.reduceFinMk, projectorFrame, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right, jordan_smul_left, jordan_smul_right, jordan_unit_left, jordan_unit_right, hc, h4, hsx] <;> module,
    fun i j hij => by fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
                      all_goals simp only [Fin.reduceFinMk, projectorFrame, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right, jordan_smul_left, jordan_smul_right, jordan_unit_left, jordan_unit_right, hc, h4, hsx] <;> module,
    by simp only [projectorFrame, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; module⟩

end
end Glennie
