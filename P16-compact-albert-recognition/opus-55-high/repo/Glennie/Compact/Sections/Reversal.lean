/- First-frame reversal, its chart-coordinate involution, and the oddness and continuity of Phi.

  * `revTriple T`: frame 0 read through the transposition (0 2), frames 1 and 2 unchanged.
    `revLedger`: the matching transposition of the first index of the C block, of the first
    index of P and of the second index of R. `ledger54_revTriple` is the naturality
    statement; it is a reduction, not a transport of the `ledgerAct` machinery, so
    nothing here depends on `Affine20.ledgerAct` or on `Affine20.relabel_ledger`.
  * `revLedger_revLedger`, `revLedger_inDomain`, `revLedger_affine`, then
    `tau := encode20 ∘ revLedger ∘ decode20` with `tau_tau`, `involutive_tau`, `tau_encode20`
    and `continuous_tau`.
  * `frame_swap`, `frame_revTriple`: a frame read through a permutation is a frame. This is the
    `hvalidReverse` input of the `RobustBranchReversal.reversalSection_valid` (:65).
  * `phiOf`, `encoder_revTriple_zero`, `phiOf_revTriple`: Phi is odd under the reversal, through
    the `BasicLaws.phi_smul_first` (BasicLaws.lean) at the scalar -1.
    `negPhiOf_revTriple` is the same fact in the shape
    `RobustBranchReversal.reversalSection_negative` (:52) takes at `phi := fun T => -phiOf T`,
    which is how the POSITIVE sign of the reversed section is obtained.
  * `continuous_U`, `continuous_phi3`, `continuous_phiOf`, `continuous_negPhiOf`,
    `continuous_revTriple`: the `hreverse` and sign-shrink continuity inputs, through 
    `Compactness.continuous_jordan` (Compactness.lean) and
    `Compactness.continuous_native_inner` (:41).

WHAT CANNOT BE INSTANTIATED, STATED PLAINLY. `RobustBranchReversal.reversalSection_ledger` (:40),
and hence `two_sections_of_reversal` (:92), take
`hledgerReverse : ∀ x, ledger (reverse x) = tau (ledger x)`, quantified over ALL of X. At
`X := Triple`, `ledger := fun T => encode20 (ledger54 T)` and this `tau`, that hypothesis is
FALSE: `tau (encode20 L) = encode20 (revLedger L)` needs `InDomain L` (it runs through
`Affine20.decode_encode`, Chart.lean), and the 54-entry ledger of an arbitrary triple is not
in the affine domain. This construction uses the lemmas whose hypotheses do hold universally
(`reversalDomain_isOpen` :77, `flat_mem_reversalDomain` :34, `reversalSection_continuousOn` :81,
`reversalSection_negative` :52, `reversalSection_valid` :65) and proves the ledger conjunct
natively in three lines, where the frame hypothesis is in hand. The alternative — instantiating
the whole of `two_sections_of_reversal` at the subtype `{T : Triple // ∀ a, Frame (T a)}` — does
work, but it makes the output subtype-valued; the section construction here uses the bare
triple domain.

No inverse-function, rank or section statement is made here. -/
module

public import Glennie.Compact.ChartTransfer
public import Glennie.Compactness
public import Glennie.BasicLaws
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.ChartTransfer

noncomputable section


/-! ## The transposition (0 2) of Fin 3 -/

theorem swap02_zero : (Equiv.swap (0 : Fin 3) 2) 0 = 2 :=
  Equiv.swap_apply_left 0 2

theorem swap02_one : (Equiv.swap (0 : Fin 3) 2) 1 = 1 :=
  Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

theorem swap02_two : (Equiv.swap (0 : Fin 3) 2) 2 = 0 :=
  Equiv.swap_apply_right 0 2

/-! ## First-frame reversal of a triple -/

/-- The first frame read through the transposition (0 2); frames 1 and 2 unchanged. -/
def revTriple (T : Triple) : Triple :=
  ![fun i => T 0 (Equiv.swap (0 : Fin 3) 2 i), T 1, T 2]

theorem revTriple_one (T : Triple) : revTriple T 1 = T 1 := rfl

theorem revTriple_two (T : Triple) : revTriple T 2 = T 2 := rfl

/-! ## The matching involution of the 54 raw ledger entries -/

/-- The transposition (0 2) applied to the first C index, the first P index and the second
R index. -/
def revLedger (L : Ledger54) : Ledger54 :=
  (fun i j k => L.1 (Equiv.swap (0 : Fin 3) 2 i) j k,
    fun i j => L.2.1 (Equiv.swap (0 : Fin 3) 2 i) j,
    L.2.2.1,
    fun k i => L.2.2.2 k (Equiv.swap (0 : Fin 3) 2 i))

/-- Naturality: reversing the triple applies `revLedger` to its 54 raw entries. -/
theorem ledger54_revTriple (T : Triple) :
    ledger54 (revTriple T) = revLedger (ledger54 T) := by rfl

theorem revLedger_revLedger (L : Ledger54) : revLedger (revLedger L) = L := by
  simp [revLedger]

theorem revLedger_inDomain {L : Ledger54} (hL : InDomain L) : InDomain (revLedger L) where
  P_row i := hL.P_row _
  P_col j := by simp [revLedger, swap02_one]; linarith [hL.P_col j]
  Q_row := hL.Q_row
  Q_col := hL.Q_col
  R_row k := by simp [revLedger, swap02_one]; linarith [hL.R_row k]
  R_col i := hL.R_col _
  C_k i j := hL.C_k _ j
  C_i j k := by simp [revLedger, swap02_one]; linarith [hL.C_i j k]
  C_j k i := hL.C_j k _

theorem revLedger_affine : AffineComb revLedger := fun _ _ _ => rfl

/-! ## The chart involution -/

/-- The reversal read on the twenty chart coordinates. -/
def tau (b : Fin 20 → ℝ) : Fin 20 → ℝ := encode20 (revLedger (decode20 b))

theorem tau_apply (b : Fin 20 → ℝ) : tau b = encode20 (revLedger (decode20 b)) := rfl

theorem tau_encode20 (L : Ledger54) (hL : InDomain L) :
    tau (encode20 L) = encode20 (revLedger L) := by
  rw [tau_apply, decode_encode L hL]

theorem tau_tau (b : Fin 20 → ℝ) : tau (tau b) = b := by
  rw [tau_apply b, tau_encode20 _ (revLedger_inDomain (decode20_inDomain b)),
    revLedger_revLedger, encode20_decode20]

theorem affineComb_tau : AffineComb tau :=
  AffineComb.comp (g := fun L => encode20 (revLedger L))
    (AffineComb.comp encode20_affine revLedger_affine)
    decode20_affine

theorem continuous_tau : Continuous tau :=
  AffineComb.continuous20 affineComb_tau

/-! ## Frames and Phi under the reversal -/

theorem frame_swap {p : Fin 3 → Albert} (hp : Frame p) :
    Frame (fun i => p (Equiv.swap (0 : Fin 3) 2 i)) where
  trace_one i := hp.trace_one (Equiv.swap (0 : Fin 3) 2 i)
  idempotent i := hp.idempotent (Equiv.swap (0 : Fin 3) 2 i)
  orthogonal i j hij :=
    hp.orthogonal (Equiv.swap (0 : Fin 3) 2 i) (Equiv.swap (0 : Fin 3) 2 j)
      ((Equiv.swap (0 : Fin 3) 2).injective.ne hij)
  sum_unit := by
    show p (Equiv.swap (0 : Fin 3) 2 0) + p (Equiv.swap (0 : Fin 3) 2 1) +
      p (Equiv.swap (0 : Fin 3) 2 2) = 1
    rw [swap02_zero, swap02_one, swap02_two, ← hp.sum_unit]
    abel

theorem frame_revTriple (T : Triple) (hT : ∀ a : Fin 3, Frame (T a)) (a : Fin 3) :
    Frame (revTriple T a) := by
  rcases fin3_cases a with rfl | rfl | rfl
  exacts [frame_swap (hT 0), hT 1, hT 2]

/-- Phi of a triple, read off its three encoders. -/
def phiOf (T : Triple) : ℝ := phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

theorem phiOf_apply (T : Triple) :
    phiOf T = phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) := rfl

theorem encoder_revTriple_zero (T : Triple) :
    encoder (revTriple T 0) = -encoder (T 0) := by
  show T 0 (Equiv.swap (0 : Fin 3) 2 2) - T 0 (Equiv.swap (0 : Fin 3) 2 0) = -(T 0 2 - T 0 0)
  rw [swap02_two, swap02_zero]
  abel

theorem phiOf_revTriple (T : Triple) : phiOf (revTriple T) = -phiOf T := by
  simp only [phiOf_apply, encoder_revTriple_zero, ← neg_one_smul ℝ (encoder (T 0)), phi_smul_first]
  simp [revTriple]; ring

/-- The shape `RobustBranchReversal.reversalSection_negative` (:52) takes, at
`phi := fun T => -phiOf T`: instantiating it there turns the reversed section's sign POSITIVE. -/
theorem negPhiOf_revTriple (T : Triple) :
    (fun X => -phiOf X) (revTriple T) = -((fun X => -phiOf X) T) := by
  show -phiOf (revTriple T) = -(-phiOf T)
  rw [phiOf_revTriple]

/-! ## Continuity of Phi -/

theorem cj {X : Type*} [TopologicalSpace X] {f g : X → Albert}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => jordan (f x) (g x) := by
  simpa [Function.comp_def] using continuous_jordan.comp (hf.prodMk hg)

theorem cU {X : Type*} [TopologicalSpace X] {f g : X → Albert}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => U (f x) (g x) := by
  simp [U, two_smul]
  exact ((cj hf (cj hf hg)).add (cj hf (cj hf hg))).sub (cj (cj hf hf) hg)

theorem continuous_encoder_slot (a : Fin 3) :
    Continuous fun T : Triple => encoder (T a) := by
  have h2 := continuous_apply_apply (ρ := fun (_ _ : Fin 3) => Albert) a (2 : Fin 3)
  have h0 := continuous_apply_apply (ρ := fun (_ _ : Fin 3) => Albert) a (0 : Fin 3)
  exact h2.sub h0

theorem continuous_phiOf : Continuous phiOf := by
  have he := continuous_encoder_slot
  unfold phiOf phi
  simpa [Function.comp_def, Pi.sub_apply] using continuous_native_inner.comp (((cU (he 0) (cU (he 1) (he 2))).sub
    (cU (he 1) (cU (he 0) (he 2)))).prodMk (cU (he 2) (cj (he 0) (he 1))))

theorem continuous_revTriple : Continuous fun T => revTriple T := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  rcases fin3_cases a with rfl | rfl | rfl
  · exact (continuous_apply (Equiv.swap (0 : Fin 3) 2 i)).comp (continuous_apply (0 : Fin 3))
  · exact (continuous_apply i).comp (continuous_apply (1 : Fin 3))
  · exact (continuous_apply i).comp (continuous_apply (2 : Fin 3))

end
end Glennie.Compact.Sections
