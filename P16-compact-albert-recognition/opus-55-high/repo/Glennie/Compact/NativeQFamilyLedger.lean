module

public import Glennie.Theorems.Frames
public import Glennie.Compact.Affine20.Relabel
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/- The explicitly ordered traceless Q family of the three native frame encoders.
   This is a native formula binding, not an invariant-ring generation theorem. -/

@[expose] public section

namespace Glennie.Compact.NativeQFamilyLedger

open Glennie.Compact.Affine20
open scoped BigOperators

noncomputable section

def framePower (p : Fin 3 → Albert) (s : Fin 2) : Albert :=
  if s = 0 then encoder p else jordan (encoder p) (encoder p)

def qSingle (T : Triple) (v : Fin 3) (s : Fin 2) : ℝ :=
  inner (framePower (T v) 0) (framePower (T v) s)

def qPair (T : Triple) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  inner (framePower (T v) s) (framePower (T w) t)

def qTriple (T : Triple) (s t u : Fin 2) : ℝ :=
  trace (jordan (jordan (framePower (T 0) s) (framePower (T 1) t))
    (framePower (T 2) u))

/-- The 26 traceless script values in exact order: six single powers, four values
for each of (x,y), (y,z), (z,x), and eight left-bracketed triple values. -/
def q26 (T : Triple) : Fin 26 → ℝ := ![
  qSingle T 0 0, qSingle T 0 1, qSingle T 1 0, qSingle T 1 1,
  qSingle T 2 0, qSingle T 2 1,
  qPair T 0 1 0 0, qPair T 0 1 0 1, qPair T 0 1 1 0, qPair T 0 1 1 1,
  qPair T 1 2 0 0, qPair T 1 2 0 1, qPair T 1 2 1 0, qPair T 1 2 1 1,
  qPair T 2 0 0 0, qPair T 2 0 0 1, qPair T 2 0 1 0, qPair T 2 0 1 1,
  qTriple T 0 0 0, qTriple T 0 0 1, qTriple T 0 1 0, qTriple T 0 1 1,
  qTriple T 1 0 0, qTriple T 1 0 1, qTriple T 1 1 0, qTriple T 1 1 1]

theorem qSingle_frame (T : Triple) (hT : ∀ v, Frame (T v))
    (v : Fin 3) (s : Fin 2) : qSingle T v s = if s = 0 then 2 else 0 := by
  fin_cases s
  · simpa [qSingle, framePower] using frame_encoder_norm (T v) (hT v)
  · change inner (encoder (T v))
        (jordan (encoder (T v)) (encoder (T v))) = 0
    change trace (jordan (encoder (T v))
      (jordan (encoder (T v)) (encoder (T v)))) = 0
    rw [frame_encoder_cube (T v) (hT v)]
    exact frame_encoder_trace (T v) (hT v)

theorem q26_eq_of_ledger54_eq (T S : Triple)
    (hT : ∀ v, Frame (T v)) (hS : ∀ v, Frame (S v))
    (h : ledger54 T = ledger54 S) : q26 T = q26 S := by
  simp [ledger54, ledger, inner, Prod.ext_iff, funext_iff] at h
  funext n
  fin_cases n <;> simp [q26, qSingle_frame, hT, hS, qPair, qTriple, framePower, frame_encoder_square] <;>
  simp [inner, encoder, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right, h]

set_option maxHeartbeats 1000000 in
theorem ledger54_eq_of_q26_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (h : q26 T = q26 S) : ledger54 T = ledger54 S := by
  simp [q26, qSingle, qPair, qTriple, inner, framePower, Matrix.vecCons_inj, one_ne_zero, ↓reduceIte] at h
  have e (U : Triple) (hU : ∀ a, Frame (U a)) : U = fun a => ![(1 / 2 : ℝ) • (jordan (encoder (U a))
      (encoder (U a)) - encoder (U a)), 1 - jordan (encoder (U a)) (encoder (U a)),
      (1 / 2 : ℝ) • (jordan (encoder (U a)) (encoder (U a)) + encoder (U a))] := by
    funext a i
    fin_cases i
    exacts [(frame_projector_first _ (hU a)).symm, (frame_projector_middle _ (hU a)).symm,
      (frame_projector_last _ (hU a)).symm]
  have n (U : Triple) (hU : ∀ a, Frame (U a)) a : trace (jordan (encoder (U a)) (encoder (U a))) = 2 :=
    frame_encoder_norm _ (hU a)
  simp [n, hT, hS, jordan_comm] at h
  rw [e T hT, e S hS]
  simp [ledger54, Prod.ext_iff, funext_iff]
  refine ⟨fun i j k => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩ <;>
  fin_cases i <;> fin_cases j <;> (try fin_cases k) <;>
  simp [ledger, inner, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right,
    jordan_smul_left, jordan_smul_right, frame_encoder_trace, n, hT, hS, h, jordan_comm]

/-- The finite Q26 and full54 ledgers carry exactly the same equality data
for ordered native frames, with no invariant-ring or orbit premise. -/
theorem q26_eq_iff_ledger54_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q26 T = q26 S ↔ ledger54 T = ledger54 S :=
  ⟨ledger54_eq_of_q26_eq T S hT hS, q26_eq_of_ledger54_eq T S hT hS⟩

end
end Glennie.Compact.NativeQFamilyLedger
