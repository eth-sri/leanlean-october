module

public import Glennie.Compact.ChartTransfer
public import Glennie.Compact.ObservationData
public import Glennie.Compactness
public import Glennie.BasicLaws
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
@[expose] public section

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.ChartTransfer

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

local notation "σ" => Equiv.swap (0 : Fin 3) 2

private theorem perm_sum {A : Type*} [AddCommMonoid A] (f : Fin 3 → A) :
    f (σ 0) + f (σ 1) + f (σ 2) = f 0 + f 1 + f 2 := by
  simpa only [Fin.sum_univ_three] using Equiv.sum_comp σ f

/-- The first frame read through the transposition (0 2); frames 1 and 2 unchanged. -/
def revTriple (T : Triple) : Triple :=
  ![fun i => T 0 (σ i), T 1, T 2]

/-! ## The matching involution of the 54 raw ledger entries -/

/-- The transposition (0 2) applied to the first C index, the first P index and the second
R index. -/
def revLedger (L : Ledger54) : Ledger54 :=
  (fun i j k => L.1 (σ i) j k,
    fun i j => L.2.1 (σ i) j,
    L.2.2.1,
    fun k i => L.2.2.2 k (σ i))

theorem ledger54_revTriple (T : Triple) : ledger54 (revTriple T) = revLedger (ledger54 T) := rfl

theorem revLedger_revLedger (L : Ledger54) : revLedger (revLedger L) = L := by
  simp [revLedger]

theorem revLedger_inDomain {L : Ledger54} (hL : InDomain L) : InDomain (revLedger L) where
  P_row i := hL.P_row _
  P_col j := (perm_sum (L.2.1 · j)).trans (hL.P_col j)
  Q_row := hL.Q_row
  Q_col := hL.Q_col
  R_row k := (perm_sum (L.2.2.2 k)).trans (hL.R_row k)
  R_col i := hL.R_col _
  C_k i j := hL.C_k _ j
  C_i j k := (perm_sum (L.1 · j k)).trans (hL.C_i j k)
  C_j k i := hL.C_j k _

/-! ## The chart involution -/

/-- The reversal read on the twenty chart coordinates. -/
def tau (b : Fin 20 → ℝ) : Fin 20 → ℝ := encode20 (revLedger (decode20 b))

theorem tau_encode20 (L : Ledger54) (hL : InDomain L) :
    tau (encode20 L) = encode20 (revLedger L) := by
  simp only [tau, decode_encode L hL]

theorem tau_tau (b : Fin 20 → ℝ) : tau (tau b) = b := by
  change tau (encode20 (revLedger (decode20 b))) = b
  rw [tau_encode20 _ (revLedger_inDomain (decode20_inDomain b)),
    revLedger_revLedger, encode20_decode20]

theorem continuous_tau : Continuous tau :=
  FrameTopology.continuous_encode20.comp
    ((by unfold revLedger; fun_prop : Continuous revLedger).comp continuous_decode20)

/-! ## Frames and Phi under the reversal -/

theorem frame_swap {p : Fin 3 → Albert} (hp : Frame p) :
    Frame (fun i => p (σ i)) where
  trace_one i := hp.trace_one (σ i)
  idempotent i := hp.idempotent (σ i)
  orthogonal i j hij :=
    hp.orthogonal (σ i) (σ j)
      ((σ).injective.ne hij)
  sum_unit := (perm_sum p).trans hp.sum_unit

theorem frame_revTriple (T : Triple) (hT : IsFrameTriple T) (a : Fin 3) :
    Frame (revTriple T a) := by
  rcases fin3_cases a with rfl | rfl | rfl
  · exact frame_swap (hT 0)
  · exact hT 1
  · exact hT 2

export Glennie.SubmissionR03 (phiOf)

theorem phiOf_apply (T : Triple) :
    phiOf T = phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) := rfl

theorem phiOf_revTriple (T : Triple) : phiOf (revTriple T) = -phiOf T := by
  have h : encoder (revTriple T 0) = (-1 : ℝ) • encoder (T 0) := by
    simp [revTriple, encoder, neg_sub]
  change phi (encoder (revTriple T 0)) (encoder (T 1)) (encoder (T 2)) = -phiOf T
  rw [h, phi_smul_first, phiOf_apply]
  ring

theorem continuous_phiOf : Continuous phiOf := by
  unfold phiOf phi U encoder
  fun_prop

theorem continuous_revTriple : Continuous fun T : Triple => revTriple T := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  rcases fin3_cases a with rfl | rfl | rfl
  · exact (continuous_apply (σ i)).comp (continuous_apply (0 : Fin 3))
  · exact (continuous_apply i).comp (continuous_apply (1 : Fin 3))
  · exact (continuous_apply i).comp (continuous_apply (2 : Fin 3))

end
end Glennie.Compact.Sections
