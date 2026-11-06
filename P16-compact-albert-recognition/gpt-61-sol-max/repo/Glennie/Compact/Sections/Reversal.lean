/- First-frame reversal, its chart involution, and oddness of Phi. The chart
naturality identity requires a frame triple: its affine-domain hypothesis does
not hold for arbitrary nine native elements. -/
module
public import Mathlib.Tactic

public import AlbertGeometry.LinearSimp

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.NormNum
public import Aesop
public import Mathlib.Tactic

public import Glennie.Compact.ChartTransfer
public import Glennie.Compactness
public import Glennie.BasicLaws
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Tactic.Abel

@[expose] public section

namespace Glennie.Compact.Sections
attribute [local fun_prop] Glennie.continuous_jordan Glennie.continuous_native_inner

open Glennie.Compact.Affine20 Glennie.Compact.ChartTransfer

noncomputable section

set_option maxHeartbeats 2000000
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

theorem revTriple_zero (T : Triple) :
    revTriple T 0 = fun i => T 0 (Equiv.swap (0 : Fin 3) 2 i) := rfl

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
    ledger54 (revTriple T) = revLedger (ledger54 T) := by
  aesop

/-- Reversal in chart coordinates. -/
def tau (b : Fin 20 → ℝ) : Fin 20 → ℝ := encode20 (revLedger (decode20 b))

theorem tau_encode20 (T : Triple) (hT : ∀ a, Frame (T a)) :
    tau (encode20 (ledger54 T)) = encode20 (revLedger (ledger54 T)) := by
  rw [tau, decode_encode_frames T hT]

theorem tau_tau (b : Fin 20 → ℝ) : tau (tau b) = b := by
  funext n
  fin_cases n <;> norm_num [tau, encode20, revLedger, decode20, decC, decP, decQ,
    decR, lift8, lift4, ext3, centred, Equiv.swap_apply_def] <;> ring

theorem continuous_tau : Continuous tau := by
  unfold tau encode20 revLedger decode20 centred decC decP decQ decR lift8 lift4 ext3
  fun_prop

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
  · rw [revTriple_zero]
    exact frame_swap (hT 0)
  · rw [revTriple_one]
    exact hT 1
  · rw [revTriple_two]
    exact hT 2

/-- Phi of a triple, read off its three encoders. -/
def phiOf (T : Triple) : ℝ := phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

theorem phiOf_mapAtoms (g : CompactAutomorphism) (T : Triple) :
    phiOf (mapAtoms g T) = phiOf T := by
  simp only [phiOf, mapAtoms_slot, g.encoder_map, g.phi_map]

theorem encoder_revTriple_zero (T : Triple) :
    encoder (revTriple T 0) = -encoder (T 0) := by
  simp [encoder, revTriple, neg_sub]

theorem phiOf_revTriple (T : Triple) : phiOf (revTriple T) = -phiOf T := by
  simp only [phiOf, revTriple_one, revTriple_two, encoder_revTriple_zero]
  rw [← neg_one_smul ℝ (encoder (T 0)), phi_smul_first]
  norm_num

/-! ## Continuity of Phi -/

theorem continuous_phiOf : Continuous phiOf := by
  unfold phiOf phi U encoder
  fun_prop

theorem continuous_revTriple : Continuous fun T : Triple => revTriple T := by
  unfold revTriple
  fun_prop

end
end Glennie.Compact.Sections
