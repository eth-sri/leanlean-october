module

public import Glennie.Hilbert
public import Glennie.LinearSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import Glennie.Theorems.Frames
public import Glennie.Compact.ObservationScript
public import Glennie.Compact.Affine20.Chart
public import Mathlib.Data.Fin.VecNotation

/- The explicitly ordered traceless Q family of the three native frame encoders.
   This is a native formula binding, not an invariant-ring generation theorem. -/

@[expose] public section

namespace Glennie.Compact.NativeQFamilyLedger

open Glennie Glennie.Compact.Affine20
open Glennie.SubmissionR04Intrinsic
noncomputable section
set_option maxHeartbeats 2000000

abbrev framePower (p : Fin 3 → Albert) (s : Fin 2) : Albert := Local.power jordan p s

abbrev qSingle (T : Triple) (v : Fin 3) (s : Fin 2) : ℝ := Local.qSingle trace jordan T v s

abbrev qPair (T : Triple) (v w : Fin 3) (s t : Fin 2) : ℝ := Local.qPair trace jordan T v w s t

abbrev qTriple (T : Triple) (s t u : Fin 2) : ℝ := Local.qTriple trace jordan T s t u

/-- The 26 traceless script values in exact order: six single powers, four values
for each of (x,y), (y,z), (z,x), and eight left-bracketed triple values. -/
def q26 (T : Triple) : Fin 26 → ℝ := Local.q26 trace jordan T

theorem qSingle_frame (T : Triple) (hT : ∀ v, Frame (T v))
    (v : Fin 3) (s : Fin 2) : qSingle T v s = if s = 0 then 2 else 0 := by
  fin_cases s
  · exact frame_encoder_norm (T v) (hT v)
  · change inner (encoder (T v))
        (jordan (encoder (T v)) (encoder (T v))) = 0
    change trace (jordan (encoder (T v))
      (jordan (encoder (T v)) (encoder (T v)))) = 0
    rw [frame_encoder_cube (T v) (hT v)]
    exact frame_encoder_trace (T v) (hT v)

private theorem framePower_eq (p : Fin 3 → Albert) (hp : Frame p) (s : Fin 2) :
    framePower p s = if s = 0 then p 2 - p 0 else p 2 + p 0 := by
  fin_cases s
  · rfl
  · exact frame_encoder_square p hp

/-- Equal complete ordered-frame ledgers yield equal native script-ordered Q26
values. This is the one-way binding; no invariant-ring generation is used. -/
private theorem frame_reconstruct (p : Fin 3 → Albert) (hp : Frame p) :
    p = ![(1 / 2 : ℝ) • (framePower p 1 - framePower p 0),
      1 - framePower p 1, (1 / 2 : ℝ) • (framePower p 1 + framePower p 0)] := by
  exact frame_as_projector p hp

private theorem framePower_trace (p : Fin 3 → Albert) (hp : Frame p) (s : Fin 2) :
    trace (framePower p s) = if s = 0 then 0 else 2 := by
  fin_cases s
  · exact frame_encoder_trace p hp
  · exact frame_encoder_norm p hp

theorem q26_eq_iff_ledger54_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ ledger54 T = ledger54 S := by
  constructor <;> intro h
  ·
    have hxy (s t : Fin 2) : qPair T 0 1 s t = qPair S 0 1 s t := by
      fin_cases s <;> fin_cases t <;> simp_all [q26, Local.q26]
    have hyz (s t : Fin 2) : qPair T 1 2 s t = qPair S 1 2 s t := by
      fin_cases s <;> fin_cases t <;> simp_all [q26, Local.q26]
    have hzx (s t : Fin 2) : qPair T 0 2 s t = qPair S 0 2 s t := by
      fin_cases s <;> fin_cases t <;> simp_all [q26, Local.q26, qPair, Local.qPair, Local.pairing, jordan_comm]
    have htr (s t u : Fin 2) : qTriple T s t u = qTriple S s t u := by
      fin_cases s <;> fin_cases t <;> fin_cases u <;> simp_all [q26, Local.q26]
    simp only [qPair, qTriple, Local.qPair, Local.qTriple, Local.pairing] at hxy hyz hzx htr
    simp only [ledger54, inner]
    rw [frame_reconstruct (T 0) (hT 0), frame_reconstruct (T 1) (hT 1),
      frame_reconstruct (T 2) (hT 2), frame_reconstruct (S 0) (hS 0),
      frame_reconstruct (S 1) (hS 1), frame_reconstruct (S 2) (hS 2)]
    ext i j k <;> fin_cases i <;> fin_cases j <;> (try fin_cases k) <;>
      simp [Glennie.ledger, albert_linear, jordan_unit_left, jordan_unit_right, trace_unit,
        framePower_trace _ (hT _), framePower_trace _ (hS _), hxy, hyz, hzx, htr]

    all_goals simp [jordan_comm, hzx]
  ·
    have hxy (i j : Fin 3) : trace (jordan (T 0 i) (T 1 j)) = trace (jordan (S 0 i) (S 1 j)) :=
      congrArg (fun L : Ledger54 => L.2.1 i j) h
    have hyz (i j : Fin 3) : trace (jordan (T 1 i) (T 2 j)) = trace (jordan (S 1 i) (S 2 j)) :=
      congrArg (fun L : Ledger54 => L.2.2.1 i j) h
    have hzx (i j : Fin 3) : trace (jordan (T 2 i) (T 0 j)) = trace (jordan (S 2 i) (S 0 j)) :=
      congrArg (fun L : Ledger54 => L.2.2.2 i j) h
    have htr (i j k : Fin 3) :
        trace (jordan (jordan (T 0 i) (T 1 j)) (T 2 k)) =
        trace (jordan (jordan (S 0 i) (S 1 j)) (S 2 k)) :=
      congrArg (fun L : Ledger54 => L.1 i j k) h
    funext n
    fin_cases n <;> simp [q26, Local.q26, qSingle_frame T hT, qSingle_frame S hS, Local.qPair, Local.qTriple, Local.pairing, framePower_eq _ (hT _), framePower_eq _ (hS _),
      albert_linear, hxy, hyz, hzx, htr]
end
end Glennie.Compact.NativeQFamilyLedger
