module

public import Glennie.ObservationLaws
public import Glennie.Theorems.Frames
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

export SubmissionR03 (ext3 lift4 lift8 centred encode20 decP decQ decR decC decode20)

/-! ## The genuine affine domain -/

/-- The margin identities satisfied by the ledger of any triple of frames. -/
structure InDomain (L : Ledger54) : Prop where
  P_row : ∀ i, L.2.1 i 0 + L.2.1 i 1 + L.2.1 i 2 = 1
  P_col : ∀ j, L.2.1 0 j + L.2.1 1 j + L.2.1 2 j = 1
  Q_row : ∀ j, L.2.2.1 j 0 + L.2.2.1 j 1 + L.2.2.1 j 2 = 1
  Q_col : ∀ k, L.2.2.1 0 k + L.2.2.1 1 k + L.2.2.1 2 k = 1
  R_row : ∀ k, L.2.2.2 k 0 + L.2.2.2 k 1 + L.2.2.2 k 2 = 1
  R_col : ∀ i, L.2.2.2 0 i + L.2.2.2 1 i + L.2.2.2 2 i = 1
  C_k : ∀ i j, L.1 i j 0 + L.1 i j 1 + L.1 i j 2 = L.2.1 i j
  C_i : ∀ j k, L.1 0 j k + L.1 1 j k + L.1 2 j k = L.2.2.1 j k
  C_j : ∀ k i, L.1 i 0 k + L.1 i 1 k + L.1 i 2 k = L.2.2.2 k i

theorem pair_row (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (i : Fin 3) :
    inner (p i) (q 0) + inner (p i) (q 1) + inner (p i) (q 2) = 1 := by
  simp [← inner_add_right, hq.sum_unit, inner_unit_right, hp.trace_one]

theorem pair_col (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (j : Fin 3) :
    inner (p 0) (q j) + inner (p 1) (q j) + inner (p 2) (q j) = 1 := by
  rw [inner_comm (p 0), inner_comm (p 1), inner_comm (p 2)]
  apply pair_row <;> assumption

/-- The last-index margin of the triple ledger, written out over the three outcomes with
this file's numerals (the same algebra as the `ledger_last_marginal`). -/
theorem ledger_margin3 (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    ledger p q r i j 0 + ledger p q r i j 1 + ledger p q r i j 2 = inner (p i) (q j) := by
  simp only [ledger]
  rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right, hr.sum_unit,
    jordan_unit_right]
  rfl

/-- Every triple of actual frames has its ledger in the affine domain. Each field first
rewrites the ledger projections with the variable-level lemmas `ledger54_C/P/Q/R`, so no
unification has to unfold Albert products. -/
theorem ledger54_inDomain (T : Triple) (h : ∀ a, Frame (T a)) : InDomain (fullLedger T) where
  P_row := pair_row _ _ (h 0) (h 1)
  Q_row := pair_row _ _ (h 1) (h 2)
  R_row := pair_row _ _ (h 2) (h 0)
  P_col := pair_col _ _ (h 0) (h 1)
  Q_col := pair_col _ _ (h 1) (h 2)
  R_col := pair_col _ _ (h 2) (h 0)
  C_k := ledger_margin3 _ _ _ (h 2)
  C_i j k := by
    simp only [ledger54_C, ledger54_Q]
    rw [ledger_cyclic (T 0) (T 1) (T 2) 0 j k, ledger_cyclic (T 0) (T 1) (T 2) 1 j k,
      ledger_cyclic (T 0) (T 1) (T 2) 2 j k]
    exact ledger_margin3 (T 1) (T 2) (T 0) (h 0) j k
  C_j k i := by
    simp only [ledger54_C, ledger54_R]
    rw [ledger_cyclic (T 0) (T 1) (T 2) i 0 k, ledger_cyclic (T 0) (T 1) (T 2) i 1 k,
      ledger_cyclic (T 0) (T 1) (T 2) i 2 k, ledger_cyclic (T 1) (T 2) (T 0) 0 k i,
      ledger_cyclic (T 1) (T 2) (T 0) 1 k i, ledger_cyclic (T 1) (T 2) (T 0) 2 k i]
    exact ledger_margin3 (T 2) (T 0) (T 1) (h 1) k i

/-- Each non-head cell is determined by the affine margin equations. -/
theorem decode_encode (L : Ledger54) (h : InDomain L) : decode20 (encode20 L) = L := by
  obtain ⟨p,q,r,s,t,u,x,y,z⟩ := h
  simp [Fin.forall_fin_succ] at p q r s t u x y z
  ext i j k <;> fin_cases i <;> fin_cases j <;> (try fin_cases k) <;>
    norm_num [decode20,encode20,decC,decP,decQ,decR,centred,lift8,lift4,ext3] <;> linarith

theorem decode_encode_frames (T : Triple) (hT : ∀ a, Frame (T a)) :
    decode20 (encode20 (fullLedger T)) = fullLedger T := decode_encode _ (ledger54_inDomain T hT)

@[fun_prop] theorem continuous_encode20 : Continuous encode20 := by
  apply continuous_pi; intro i; fin_cases i <;> dsimp [encode20, centred] <;> fun_prop

@[fun_prop] private theorem continuous_ext3 {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (i : Fin 3) : Continuous (fun x => ext3 (f x) (g x) i) := by
  fin_cases i <;> dsimp [ext3] <;> fun_prop

@[fun_prop] theorem continuous_decode20 : Continuous decode20 := by
  unfold decode20 decC decP decQ decR lift8 lift4
  fun_prop

end
end Glennie.Compact.Affine20
