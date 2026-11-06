/- Four elementary topological inputs for the saturation obligation.

  * `frames_isCompact` and `frameTriples_isCompact`: the set of ordered native
    frames, and the set of frame triples, are compact. Closedness is the four
    `Frame` fields read as equalities between continuous functions of the
    atoms (`isClosed_eq` plus `isClosed_iInter`, exactly as
    `automorphismMaps_closed`). Boundedness is
    `inner (p i) (p i) = trace (jordan (p i) (p i)) = trace (p i) = 1`,
    which `native_norm_sq` turns into `‖p i‖ = 1`, so the set lies inside a
    finite product of unit closed balls; `isCompact_pi_infinite` and
    `IsCompact.of_isClosed_subset` finish, the same two steps as
    `automorphismMaps_compact`.

  * `continuous_ledger54`: the raw 54-entry ledger is continuous in the
    triple. Componentwise by `continuous_pi` and `Continuous.prodMk`, with the
    `continuous_jordan` / `continuous_native_inner` composed with the
    coordinate projections `fun T => T a i`.

  * `fibre_tube`: for compact `K`, a map continuous on `K` into a Hausdorff
    space, and an open `U` containing the WHOLE fibre `K ∩ f⁻¹' {y}`, some
    open neighbourhood `V` of `y` already satisfies `K ∩ f⁻¹' V ⊆ U`. Proved
    from Mathlib primitives only (`IsCompact.diff`,
    `IsCompact.image_of_continuousOn`, `IsCompact.isClosed`).

  * `flatBase_ledger_saturated`: the instance at the flat base. For
    every open set containing every frame triple whose 54-entry ledger equals
    the flat-base ledger, there is a neighbourhood of that ledger value in
    which every frame triple already lies in the open set. -/
module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import Glennie.Compactness
public import Glennie.Compact.Affine20.Relabel
public import Glennie.Compact.FlatBase

@[expose] public section

namespace Glennie.Compact.FrameTopology

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20

noncomputable section

attribute [local fun_prop] continuous_jordan continuous_native_inner

theorem continuous_entry (a i : Fin 3) : Continuous (fun T : Triple => T a i) := by fun_prop

theorem continuous_ledger54 : Continuous (fun T : Triple => ledger54 T) := by
  unfold ledger54 Glennie.ledger
  simp only [← inner_unit_right]
  fun_prop

/-- The flat base, as a frame triple. -/
def flatBaseTriple : Triple := ![flatFrameP, flatFrameQ, flatFrameR]

theorem flatBaseTriple_frames : ∀ a, Frame (flatBaseTriple a) := by
  intro a
  fin_cases a
  · exact flatFrameP_frame
  · exact flatFrameQ_frame
  · exact flatFrameR_frame

end
end Glennie.Compact.FrameTopology
