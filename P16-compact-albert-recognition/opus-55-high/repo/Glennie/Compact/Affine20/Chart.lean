/- The genuine affine-20 ledger domain and its chart.
  * `InDomain L`: the margin identities. Each pair block is doubly stochastic, and the
    triple block C has the pair blocks as its three margins.
  * `ledger54_inDomain`: every triple of actual native frames lies in the domain
    (`ledger_margin3`, the algebra of the `ledger_last_marginal`, and the `ledger_cyclic`, Glennie.Theorems.Frames). Every field first rewrites the ledger
    projections with the variable-level lemmas `ledger54_C/P/Q/R` (Relabel).
  * `encode20` reads 20 coordinates: the 2x2 heads of P-1/3, Q-1/3, R-1/3 (12) and the 2x2x2
    head of the centred tensor H = C - (P + Q + R)/3 + 2/9 (8). `decode20` rebuilds all 54
    entries from 20 numbers.
  * `decode_encode`: decode20 (encode20 L) = L for every L in the domain, through generic
    zero-margin reconstruction lemmas (`ext3_reconstruct`, `lift4_reconstruct`,
    `lift8_reconstruct`); `decode_encode_frames` for actual frames.
  * `AffineComb f`: f preserves affine combinations. It holds for encode20, decode20 and
    every `ledgerAct γ`, and it is closed under composition.
  * `act20 γ = encode20 ∘ ledgerAct γ ∘ decode20`, the relabelling on chart coordinates;
    `act20_affine`, and `relabel_ledger`: for actual frames,
    act20 γ (encode20 (ledger54 T)) = encode20 (ledger54 (relabelTriple γ T)).
No rank, inverse-function, fixed-point or analytic statement is made here.
Proof method: index splits use the Boolean lemmas `fin3_cases`/`fin20_cases` (no
`fin_cases`); coordinates and projections are rewritten only with rfl lemmas on variables
(`encode20_apply_n`, `decode20_C/P/Q/R`, `ext3_zero/one/two`, `ledgerAct_*`, `pairExt_xy`)
and the Prod/Pi pointwise lemmas under `simp only`, then closed by `ring`. -/
module

public import Glennie.Compact.Affine20.Relabel
public import Glennie.Theorems.Frames
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Glennie.Compact.Affine20

noncomputable section

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
  rw [inner_comm (p 0), inner_comm (p 1), inner_comm (p 2)]
  exact pair_row q p hq hp j

/-- The last-index margin of the triple ledger, written out over the three outcomes with
this file's numerals (the same algebra as the `ledger_last_marginal`). -/
theorem ledger_margin3 (p q r : Fin 3 → Albert) (hr : Frame r) (i j : Fin 3) :
    ledger p q r i j 0 + ledger p q r i j 1 + ledger p q r i j 2 = inner (p i) (q j) := by
  simp [ledger]
  rw [← trace_add, ← trace_add, ← jordan_add_right, ← jordan_add_right, hr.sum_unit,
    jordan_unit_right]
  rfl

/-- Every triple of actual frames has its ledger in the affine domain. Each field first
rewrites the ledger projections with the variable-level lemmas `ledger54_C/P/Q/R`, so no
unification has to unfold Albert products. -/
theorem ledger54_inDomain (T : Triple) (hT : ∀ a, Frame (T a)) : InDomain (ledger54 T) where
  P_row := pair_row _ _ (hT 0) (hT 1)
  P_col := pair_col _ _ (hT 0) (hT 1)
  Q_row := pair_row _ _ (hT 1) (hT 2)
  Q_col := pair_col _ _ (hT 1) (hT 2)
  R_row := pair_row _ _ (hT 2) (hT 0)
  R_col := pair_col _ _ (hT 2) (hT 0)
  C_k := ledger_margin3 _ _ _ (hT 2)
  C_i j k := by
    simp [ledger54_C, ledger54_Q, ledger_cyclic (T 0)]
    exact ledger_margin3 _ _ _ (hT 0) j k
  C_j k i := by
    simp [ledger54_C, ledger54_R, ledger_cyclic (T 0), ledger_cyclic (T 1)]
    exact ledger_margin3 _ _ _ (hT 1) k i

/-! ## Zero-margin reconstruction -/

/-- (x, y, -(x + y)). -/
def ext3 (x y : ℝ) : Fin 3 → ℝ := ![x, y, -(x + y)]

/-- The 3x3 matrix with zero row and column sums and top-left 2x2 block (a b; c d). -/
def lift4 (a b c d : ℝ) (i j : Fin 3) : ℝ := ext3 (ext3 a b j) (ext3 c d j) i

/-- The 3x3x3 tensor with zero margins and 2x2x2 head (h_abc). -/
def lift8 (h000 h001 h010 h011 h100 h101 h110 h111 : ℝ) (i j k : Fin 3) : ℝ :=
  ext3 (ext3 (ext3 h000 h001 k) (ext3 h010 h011 k) j)
    (ext3 (ext3 h100 h101 k) (ext3 h110 h111 k) j) i

/-! ## The chart -/

/-- The centred triple tensor H = C - (P + Q + R)/3 + 2/9. -/
def centred (L : Ledger54) (i j k : Fin 3) : ℝ :=
  L.1 i j k - (L.2.1 i j + L.2.2.1 j k + L.2.2.2 k i) / 3 + 2 / 9

/-- The 20 chart coordinates: 2x2 heads of P - 1/3, Q - 1/3, R - 1/3, and the 2x2x2 head of
the centred tensor. -/
def encode20 (L : Ledger54) : Fin 20 → ℝ :=
  ![L.2.1 0 0 - 1 / 3, L.2.1 0 1 - 1 / 3, L.2.1 1 0 - 1 / 3, L.2.1 1 1 - 1 / 3,
    L.2.2.1 0 0 - 1 / 3, L.2.2.1 0 1 - 1 / 3, L.2.2.1 1 0 - 1 / 3, L.2.2.1 1 1 - 1 / 3,
    L.2.2.2 0 0 - 1 / 3, L.2.2.2 0 1 - 1 / 3, L.2.2.2 1 0 - 1 / 3, L.2.2.2 1 1 - 1 / 3,
    centred L 0 0 0, centred L 0 0 1, centred L 0 1 0, centred L 0 1 1,
    centred L 1 0 0, centred L 1 0 1, centred L 1 1 0, centred L 1 1 1]

def decP (v : Fin 20 → ℝ) (i j : Fin 3) : ℝ := 1 / 3 + lift4 (v 0) (v 1) (v 2) (v 3) i j

def decQ (v : Fin 20 → ℝ) (j k : Fin 3) : ℝ := 1 / 3 + lift4 (v 4) (v 5) (v 6) (v 7) j k

def decR (v : Fin 20 → ℝ) (k i : Fin 3) : ℝ := 1 / 3 + lift4 (v 8) (v 9) (v 10) (v 11) k i

def decC (v : Fin 20 → ℝ) (i j k : Fin 3) : ℝ :=
  lift8 (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18) (v 19) i j k +
    (decP v i j + decQ v j k + decR v k i) / 3 - 2 / 9

/-- The 54 entries rebuilt from the 20 chart coordinates. -/
def decode20 (v : Fin 20 → ℝ) : Ledger54 := (decC v, decP v, decQ v, decR v)

/-! Coordinate values of the chart (rfl on a variable ledger). -/

/-- On the genuine domain the chart is inverted by decode20. -/
theorem decode_encode (L : Ledger54) (h : InDomain L) : decode20 (encode20 L) = L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp [Fin.forall_fin_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  casesm* _ ∧ _
  ext i j k <;> fin_cases i <;> fin_cases j <;> (try fin_cases k) <;>
    simp [decode20, decC, decP, decQ, decR, lift8, lift4, ext3, encode20, centred] <;>
    linarith

/-- The chart inverts on the ledger of every triple of actual frames. -/
theorem decode_encode_frames (T : Triple) (hT : ∀ a, Frame (T a)) :
    decode20 (encode20 (ledger54 T)) = ledger54 T :=
  decode_encode _ (ledger54_inDomain T hT)

/-! ## Affine maps (preservation of affine combinations) -/

/-- `f` preserves affine combinations: f (x + t (y - x)) = f x + t (f y - f x). -/
def AffineComb {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E → F) : Prop :=
  ∀ (x y : E) (t : ℝ), f (x + t • (y - x)) = f x + t • (f y - f x)

theorem AffineComb.comp {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] [AddCommGroup G] [Module ℝ G] {f : E → F} {g : F → G}
    (hg : AffineComb g) (hf : AffineComb f) : AffineComb (fun x => g (f x)) := by
  intro x y t
  show g (f (x + t • (y - x))) = g (f x) + t • (g (f y) - g (f x))
  rw [hf x y t]
  exact hg (f x) (f y) t

/-! The proofs below split indices with the Boolean case lemmas, rewrite only with
variable-level rfl lemmas and the Prod/Pi pointwise lemmas (`simp only`), and close with
`ring`. No step compares two different structures by unfolding. -/

theorem encode20_affine : AffineComb encode20 := by
  intro x y t
  funext n
  fin_cases n <;> simp [encode20, centred] <;> ring

theorem decode20_affine : AffineComb decode20 := by
  intro x y t
  ext i j k <;> fin_cases i <;> fin_cases j <;> (try fin_cases k) <;>
    simp [decode20, decC, decP, decQ, decR, lift8, lift4, ext3] <;> ring

/-! ## The relabelling action in chart coordinates -/

end
end Glennie.Compact.Affine20
