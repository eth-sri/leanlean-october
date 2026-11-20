module

public import Glennie.Compact.Affine20.Relabel
public import Glennie.Theorems.Frames
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

/-- The fixed twenty-coordinate affine chart of complete overlap ledgers. -/
def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / (Nat.cast 3 : ℝ) + (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.1 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.1 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    L.2.2.2 f0 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f0 f1 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f0 - 1 / (Nat.cast 3 : ℝ), L.2.2.2 f1 f1 - 1 / (Nat.cast 3 : ℝ),
    centred L f0 f0 f0, centred L f0 f0 f1, centred L f0 f1 f0, centred L f0 f1 f1,
    centred L f1 f0 f0, centred L f1 f0 f1, centred L f1 f1 f0, centred L f1 f1 f1]
/-- The chart decoder uses zero-margin 2-by-2 and 2-by-2-by-2 lifts. -/
def ext3 (x y : ℝ) : Fin 3 → ℝ := ![x, y, -(x + y)]
def lift4 (a b c d : ℝ) (i j : Fin 3) : ℝ := ext3 (ext3 a b j) (ext3 c d j) i
def lift8 (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j k : Fin 3) : ℝ :=
  ext3 (ext3 (ext3 h000 h001 k) (ext3 h010 h011 k) j)
    (ext3 (ext3 h100 h101 k) (ext3 h110 h111 k) j) i
def decP (v : Fin 20 → ℝ) (i j : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 0) (v 1) (v 2) (v 3) i j
def decQ (v : Fin 20 → ℝ) (j k : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 4) (v 5) (v 6) (v 7) j k
def decR (v : Fin 20 → ℝ) (k i : Fin 3) : ℝ := 1 / (Nat.cast 3 : ℝ) + lift4 (v 8) (v 9) (v 10) (v 11) k i
def decC (v : Fin 20 → ℝ) (i j k : Fin 3) : ℝ :=
  lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k +
    (decP v i j + decQ v j k + decR v k i) / (Nat.cast 3 : ℝ) - (Nat.cast 2 : ℝ) / (Nat.cast 9 : ℝ)
def decode20 (v : Fin 20 → ℝ) : Ledger54 := (decC v, decP v, decQ v, decR v)


end
end Glennie.SubmissionR03

namespace Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

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
  rw [← inner_add_right, ← inner_add_right, hq.sum_unit, inner_unit_right, hp.trace_one]

theorem pair_col (p q : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (j : Fin 3) :
    inner (p 0) (q j) + inner (p 1) (q j) + inner (p 2) (q j) = 1 := by
  simpa only [inner_comm (q j)] using pair_row q p hq hp j

private theorem ledger_margin3 (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    ledger p q r i j 0 + ledger p q r i j 1 + ledger p q r i j 2 = inner (p i) (q j) := by
  simpa only [Fin.sum_univ_three] using ledger_last_marginal p q r hr i j

theorem ledger54_inDomain (T : Triple) (hT : IsFrameTriple T) : InDomain (ledger54 T) where
  P_row := pair_row _ _ (hT 0) (hT 1)
  P_col := pair_col _ _ (hT 0) (hT 1)
  Q_row := pair_row _ _ (hT 1) (hT 2)
  Q_col := pair_col _ _ (hT 1) (hT 2)
  R_row := pair_row _ _ (hT 2) (hT 0)
  R_col := pair_col _ _ (hT 2) (hT 0)
  C_k := ledger_margin3 _ _ _ (hT 2)
  C_i j k := by
    simp only [ledger54_C, ledger54_Q, ledger_cyclic (T 0) (T 1) (T 2)]
    exact ledger_margin3 _ _ _ (hT 0) _ _
  C_j k i := by
    simp only [ledger54_C, ledger54_R, ledger_cyclic (T 0) (T 1) (T 2), ledger_cyclic (T 1) (T 2) (T 0)]
    exact ledger_margin3 _ _ _ (hT 1) _ _

/-! ## Zero-margin reconstruction -/

export Glennie.SubmissionR03 (ext3 lift4 lift8 centred encode20 decP decQ decR decC decode20)

/-- The chart and the margin equations determine every ledger entry. -/
theorem decode_encode (L : Ledger54) (h : InDomain L) : decode20 (encode20 L) = L := by
  rcases h with ⟨p₁,p₂,q₁,q₂,r₁,r₂,c₁,c₂,c₃⟩
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true] at p₁ p₂ q₁ q₂ r₁ r₂ c₁ c₂ c₃
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  all_goals funext i j
  case' refine_1 => funext k; fin_cases k
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [decode20, encode20, decP, decQ, decR, decC, centred, lift4, lift8, ext3] <;> grind

/-- The chart inverts on the ledger of every triple of actual frames. -/
theorem decode_encode_frames (T : Triple) (hT : IsFrameTriple T) :
    decode20 (encode20 (ledger54 T)) = ledger54 T :=
  decode_encode _ (ledger54_inDomain T hT)


end
end Glennie.Compact.Affine20
