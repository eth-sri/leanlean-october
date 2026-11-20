module

public import Glennie.Theorems.Frames
public import Glennie.Compact.Affine20.Chart
public import Glennie.Native.CubicIdentity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
/- The explicitly ordered traceless Q family of the three native frame encoders.
   This is a native formula binding, not an invariant-ring generation theorem. -/

public meta section

/-- Order the singles, cyclic pairs and triples identically in both models. -/
macro "qFamilyTable% " S:term:max P:term:max Q:term:max " using "
    a:term:max b:term:max c:term:max i:term:max j:term:max : term =>
  `(![
  $S $a $i, $S $a $j, $S $b $i, $S $b $j,
  $S $c $i, $S $c $j,
  $P $a $b $i $i, $P $a $b $i $j,
  $P $a $b $j $i, $P $a $b $j $j,
  $P $b $c $i $i, $P $b $c $i $j,
  $P $b $c $j $i, $P $b $c $j $j,
  $P $c $a $i $i, $P $c $a $i $j,
  $P $c $a $j $i, $P $c $a $j $j,
  $Q $i $i $i, $Q $i $i $j,
  $Q $i $j $i, $Q $i $j $j,
  $Q $j $i $i, $Q $j $i $j,
  $Q $j $j $i, $Q $j $j $j])

end

@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

@[simp] theorem b0_eq : b0 = (0 : Fin 2) := rfl
@[simp] theorem b1_eq : b1 = (1 : Fin 2) := rfl

/-- The fixed frame encoder or its Jordan square. -/
def framePower (p : Fin 3 → Albert) (s : Fin 2) : Albert :=
  if s = b0 then encoder p else jordan (encoder p) (encoder p)
def qSingle (T : Triple) (v : Fin 3) (s : Fin 2) : ℝ :=
  inner (framePower (T v) b0) (framePower (T v) s)
def qPair (T : Triple) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  inner (framePower (T v) s) (framePower (T w) t)
def qTriple (T : Triple) (s t u : Fin 2) : ℝ :=
  trace (jordan (jordan (framePower (T f0) s) (framePower (T f1) t))
    (framePower (T f2) u))
/-- Six single-frame readings, twelve pair readings and eight triple readings. -/
def q26 (T : Triple) : Fin 26 → ℝ := qFamilyTable% (qSingle T) (qPair T) (qTriple T) using f0 f1 f2 b0 b1

end
end Glennie.SubmissionR03

namespace Glennie.Compact.NativeQFamilyLedger

open Glennie Glennie.Compact.Affine20
open scoped BigOperators

noncomputable section

export Glennie.SubmissionR03 (framePower qSingle qPair qTriple q26)

theorem qSingle_frame (T : Triple) (hT : IsFrameTriple T)
    (v : Fin 3) (s : Fin 2) : qSingle T v s = if s = 0 then 2 else 0 := by
  fin_cases s
  · simpa [qSingle, framePower] using frame_encoder_norm (T v) (hT v)
  · change inner (encoder (T v))
        (jordan (encoder (T v)) (encoder (T v))) = 0
    change trace (jordan (encoder (T v))
      (jordan (encoder (T v)) (encoder (T v)))) = 0
    rw [frame_encoder_cube (T v) (hT v)]
    exact frame_encoder_trace (T v) (hT v)

private def moment (p : Fin 3 → Albert) : Fin 3 → Albert := ![1, framePower p 0, framePower p 1]

private def mix (m : Fin 3 → Fin 3 → ℝ) (p : Fin 3 → Albert) (i : Fin 3) : Albert :=
  ∑ j, m i j • p j

private def tripleLedger (T : Triple) := ledger (T 0) (T 1) (T 2)

private theorem ledger_mix (m : Fin 3 → Fin 3 → ℝ) {T S : Triple}
    (h : tripleLedger T = tripleLedger S) :
    tripleLedger (mix m ∘ T) = tripleLedger (mix m ∘ S) := by
  funext i j k
  have he a b c := congrFun (congrFun (congrFun h a) b) c
  simp only [tripleLedger, ledger, ← traceLinear_apply, ← jordanLinear_apply] at he ⊢
  simp only [Function.comp_apply, mix, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, he]

private def moments (T : Triple) := tripleLedger (moment ∘ T)

private def vandermonde : Fin 3 → Fin 3 → ℝ := ![![1,1,1], ![-1,0,1], ![1,0,1]]
private def inverseWeights : Fin 3 → Fin 3 → ℝ := ![![0,-1/2,1/2], ![1,0,-1], ![0,1/2,1/2]]

private theorem moment_sum (p : Fin 3 → Albert) (hp : Frame p) : moment p = mix vandermonde p := by
  funext s
  fin_cases s <;> simp [mix, vandermonde, moment, Fin.sum_univ_three, hp.sum_unit, framePower,
    frame_encoder_square p hp] <;> (try unfold encoder) <;> abel

private theorem frame_sum (p : Fin 3 → Albert) (hp : Frame p) : p = mix inverseWeights (moment p) := by
  funext s
  fin_cases s <;> norm_num [mix, inverseWeights, moment, Fin.sum_univ_three, framePower,
    frame_encoder_square p hp] <;> simp [encoder, ← hp.sum_unit] <;> module

private theorem trace_power (p : Fin 3 → Albert) (hp : Frame p) (s : Fin 2) :
    trace (framePower p s) = if s = 0 then 0 else 2 := by
  fin_cases s <;> simp [framePower, frame_encoder_trace p hp, frame_encoder_square p hp,
    trace_add, hp.trace_one] <;> norm_num

private theorem trace_jordan (x y : Albert) : trace (jordan x y) = inner x y := rfl

set_option maxHeartbeats 1500000 in
private theorem q26_eq_iff_moments_eq (T S : Triple) (hT : IsFrameTriple T)
    (hS : IsFrameTriple S) : q26 T = q26 S ↔ moments T = moments S := by
  have htr (a s) := trace_power (T a) (hT a) s
  have hsr (a s) := trace_power (S a) (hS a) s
  simp [q26, qPair, qTriple, qSingle_frame T hT, qSingle_frame S hS,
    funext_iff, Fin.forall_fin_succ, moments, tripleLedger, Function.comp_apply, ledger, moment, trace_jordan,
    jordan_unit_left, jordan_unit_right, htr, hsr, inner_comm]
  tauto

open Glennie.SubmissionR03 (fullLedger) in
theorem _root_.Glennie.SubmissionR03.q26_eq_iff_fullLedger_eq (T S : Triple)
    (hT : IsFrameTriple T) (hS : IsFrameTriple S) :
    q26 T = q26 S ↔ fullLedger T = fullLedger S := by
  rw [q26_eq_iff_moments_eq T S hT hS]
  have fw (X : Triple) (hX : IsFrameTriple X) : moments X = tripleLedger (mix vandermonde ∘ X) :=
    congrArg tripleLedger (funext fun i => moment_sum _ (hX i))
  have bw (X : Triple) (hX : IsFrameTriple X) :
      tripleLedger ((mix inverseWeights ∘ moment) ∘ X) = tripleLedger X :=
    congrArg tripleLedger (funext fun i => (frame_sum _ (hX i)).symm)
  constructor
  · intro h
    have hC : (ledger54 T).1 = (ledger54 S).1 := (bw T hT).symm.trans ((ledger_mix inverseWeights h).trans (bw S hS))
    have hD := ledger54_inDomain T hT
    have hD' := ledger54_inDomain S hS
    refine Prod.ext hC (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i j; rw [← hD.C_k, ← hD'.C_k, hC]
    · funext j k; rw [← hD.C_i, ← hD'.C_i, hC]
    · funext k i; rw [← hD.C_j, ← hD'.C_j, hC]
  · intro h
    rw [fw T hT, fw S hS]
    exact ledger_mix vandermonde (congrArg Prod.fst h)

end
end Glennie.Compact.NativeQFamilyLedger
