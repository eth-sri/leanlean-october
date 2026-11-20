module

public import Glennie.Theorems.Frames
public import Glennie.Compact.Affine20.Chart
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/- The explicitly ordered traceless Q family of the three native frame encoders.
   This is a native formula binding, not an invariant-ring generation theorem. -/

@[expose] public section

namespace Glennie.Compact.NativeQFamilyLedger

open Glennie Glennie.Compact.Affine20
open scoped BigOperators

noncomputable section

export _root_.Glennie.SubmissionR03 (framePower qSingle qPair qTriple q26)

theorem qSingle_frame (T : Triple) (hT : ∀ v, Frame (T v))
    (v : Fin 3) (s : Fin 2) : qSingle T v s = if s = 0 then 2 else 0 := by
  simp only [qSingle, framePower,SubmissionR03.b0_eq]; grind [ frame_encoder_norm, inner, encoder, jordan, trace, frame_encoder_cube, frame_encoder_trace]

private abbrev cells (T : Triple) := ledger (T 0) (T 1) (T 2)
private def mix (T : Triple) (w : Fin 3 → Fin 3 → ℝ) : Triple :=
  fun a i => ∑ j, w i j • T a j

private theorem mix_cells {T S : Triple} (h : cells T = cells S) (w : Fin 3 → Fin 3 → ℝ) :
    cells (mix T w) = cells (mix S w) := by
  have formula (A : Triple) (i j k : Fin 3) : cells (mix A w) i j k =
      ∑ a, ∑ b, ∑ c, w i a * w j b * w k c * cells A a b c := by
    simp [mix, cells, ledger, Fin.sum_univ_three, jordan_add_left, jordan_add_right,
      jordan_smul_left, jordan_smul_right, trace_add, trace_smul]; ring
  funext i j k; rw [formula, h, formula]

private def powers (T : Triple) : Triple := fun a => ![1, framePower (T a) 0, framePower (T a) 1]

private theorem power_change (T : Triple) (h : ∀ a, Frame (T a)) :
    powers T = mix T ![![1,1,1],![-1,0,1],![1,0,1]] := by
  funext a i; fin_cases i <;> simp [mix, Fin.sum_univ_three, powers, framePower,
    (h a).sum_unit, frame_encoder_square _ (h a)]
  all_goals try simp [encoder]
  all_goals abel

private theorem atom_change (T : Triple) (h : ∀ a, Frame (T a)) :
    T = mix (powers T) ![![0,-1/2,1/2],![1,0,-1],![0,1/2,1/2]] := by
  funext a i; fin_cases i <;> simp [mix, Fin.sum_univ_three, powers, framePower,
    ← frame_projector_first _ (h a), ← frame_projector_middle _ (h a), ← frame_projector_last _ (h a)] <;> module

private theorem cells_iff_full {T S : Triple} (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    cells T = cells S ↔ fullLedger T = fullLedger S := by
  refine ⟨fun h => ?_,congrArg Prod.fst⟩
  change (fullLedger T).1 = (fullLedger S).1 at h
  have p := ledger54_inDomain T hT; have q := ledger54_inDomain S hS
  refine Prod.ext h (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> funext i j
  · rw [← p.C_k, ← q.C_k, h]
  · rw [← p.C_i, ← q.C_i, h]
  · rw [← p.C_j, ← q.C_j, h]

private theorem trace_power (p : Fin 3 → Albert) (h : Frame p) (i : Fin 2) :
    trace (framePower p i) = if i = 0 then 0 else 2 := by
  fin_cases i
  · exact frame_encoder_trace _ h
  · exact frame_encoder_norm _ h

/- Reading the moment tensor in the (unit, encoder, square) basis omits
only constants and repeats, and lists the zx block in the transposed order. -/
set_option maxHeartbeats 2000000 in
private theorem q26_iff_powers (T S : Triple) (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ cells (powers T) = cells (powers S) := by
  simp only [q26,SubmissionR03.f0_eq,SubmissionR03.f1_eq,SubmissionR03.f2_eq,SubmissionR03.b0_eq,SubmissionR03.b1_eq, Matrix.vecCons_inj, qSingle_frame T hT, qSingle_frame S hS, true_and, eq_self, and_true]
  simp only [funext_iff, Fin.forall_fin_succ, cells, powers, ledger, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, jordan_unit_right, jordan_unit_left, trace_power _ (hT _), trace_power _ (hS _), eq_self, true_and, and_true]
  simp only [qPair, qTriple,SubmissionR03.f0_eq,SubmissionR03.f1_eq,SubmissionR03.f2_eq, inner, jordan_comm (framePower (T 2) _), jordan_comm (framePower (S 2) _)]
  simp only [IsEmpty.forall_iff, and_true, true_and]
  tauto

theorem q26_eq_iff_ledger54_eq (T S : Triple) (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ fullLedger T = fullLedger S := by
  rw [q26_iff_powers T S hT hS, ← cells_iff_full hT hS]
  constructor <;> intro h
  · rw [atom_change T hT, atom_change S hS]; exact mix_cells h _
  · rw [power_change T hT, power_change S hS]; exact mix_cells h _

end
end Glennie.Compact.NativeQFamilyLedger
