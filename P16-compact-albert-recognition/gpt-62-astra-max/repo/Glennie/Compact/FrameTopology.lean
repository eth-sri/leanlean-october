module
public import Glennie.ObservationLaws
public import Glennie.Compactness
public import Mathlib.Tactic.FunProp
@[expose] public section
namespace Glennie.Compact.FrameTopology
open Affine20
attribute [fun_prop] continuous_jordan continuous_native_inner

theorem continuous_ledger54 : Continuous fullLedger := by
  unfold fullLedger ledger
  simp only [show ∀ a b, trace (jordan a b) = inner a b from fun _ _ => rfl]
  fun_prop
end Glennie.Compact.FrameTopology
