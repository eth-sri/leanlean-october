module

public import Glennie.Compact.ChartTransfer
public import Glennie.Compact.FrameTopology
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

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

export SubmissionR03 (phiOf)

theorem phiOf_apply (T : Triple) : phiOf T = phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2)) := rfl
@[fun_prop] theorem continuous_phiOf : Continuous phiOf := by unfold phiOf phi U encoder; fun_prop

/-- Swap the first two entire frames. Phi is alternating in these slots, and
the centered chart transforms by a permutation, without feasibility hypotheses. -/
def flip (T : Triple) : Triple := fun a => T (![1,0,2] a)
def perm (i : Fin 20) : Fin 20 := #v[0,2,1,3,8,10,9,11,4,6,5,7,12,13,16,17,14,15,18,19][i]
def transposeChart (b : Fin 20 → ℝ) := fun i => b (perm i)

theorem flip_chart (T : Triple) : encode20 (fullLedger (flip T)) = transposeChart (encode20 (fullLedger T)) := by
  funext i; fin_cases i <;> simp [encode20,centred,transposeChart,perm,flip,fullLedger,ledger,
    inner_comm,jordan_comm] <;> ring

theorem transpose_twice (b : Fin 20 → ℝ) : transposeChart (transposeChart b) = b := by
  funext i; fin_cases i <;> rfl
@[fun_prop] theorem continuous_transposeChart : Continuous transposeChart := by unfold transposeChart; fun_prop
@[fun_prop] theorem continuous_flip : Continuous flip := by unfold flip; fun_prop

theorem phi_flip (T : Triple) : phiOf (flip T) = -phiOf T := by
  simp [phiOf,flip,phi,jordan_comm,inner_sub_left]
end
end Glennie.Compact.Sections
