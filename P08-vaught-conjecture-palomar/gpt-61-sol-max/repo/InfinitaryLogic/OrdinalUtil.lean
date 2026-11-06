import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Family

/-!
# Small ordinal facts

Neutral helpers about countable ordinals, used by the Scott refinement count, the Borel
`BFEquiv` analysis, and the ranked-thinness package, together with the comparison of
`WellFounded.rank` along a relation homomorphism (`rank_le_rank_of_relHom`, not necessarily
injective) used for tree heights. Nothing here is specific to infinitary logic, descriptive set
theory, or any one of those consumers.  It also records the greatest attainable stage
(`exists_forall_iff_le_of_bounded_of_isSuccLimit_closed`): a downward-closed property of ordinals
holding at `0`, closed at successor limits and bounded, holds exactly up to a last, attained
stage, with a convenience form below `ω₁`.

Both shapes of the countability statement are provided: `Set.Countable (Set.Iio β)` and the
`Countable` *instance* on the coercion, since consumers need one or the other and converting
at each site is noise.

The greatest-attainable-stage lemma was offered for upstreaming by a consumer of this library.
-/

universe u

namespace InfinitaryLogic

/-- For `β < ω₁`, the ordinals below `β` form a countable **type**. -/
theorem countable_Iio_of_lt_omega1 (β : Ordinal₀) (hβ : β < Ordinal.omega 1) :
    Countable (Set.Iio β) := by
  have hle  := by
    have hlt  := Cardinal.lt_omega_iff_card_lt.mp hβ
    rw [← Cardinal.succ_aleph0] at hlt
    exact Order.lt_succ_iff.mp hlt
  rw [← Cardinal.mk_le_aleph0_iff]
  calc Cardinal.mk (Set.Iio β)
      = Cardinal.lift β.card := Cardinal.mk_Iio_ordinal β
    _ ≤ Cardinal.lift Cardinal.aleph0 := Cardinal.lift_le.mpr hle
    _ = Cardinal.aleph0 := by simp

/-- The same fact as a `Set.Countable`. -/
def setCountable_Iio_of_lt_omega1 (β : Ordinal₀) (hβ : β < Ordinal.omega 1) :=
  Set.countable_coe_iff.mp (countable_Iio_of_lt_omega1 β hβ)

/-! ## The greatest attainable stage -/

/-! ## Rank is monotone along relation homomorphisms -/

/-- **Rank under a relation homomorphism.**  If `f : r →r s` sends every `r`-step to an `s`-step,
then the `r`-rank of `a` is at most the `s`-rank of `f a`.  No injectivity is assumed: distinct
points may share an image, since only the steps below `a` are transported. -/
theorem rank_le_rank_of_relHom {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [WellFounded r] [WellFounded s] (f : r →r s) (a : α) :
    WellFounded.rank r a ≤ WellFounded.rank s (f a) := by
  induction a using WellFounded.induction' r with
  | ind a ih =>
    rw [WellFounded.rank_eq r]
    refine Ordinal.iSup_le fun b ↦ Order.succ_le_of_lt ?_
    exact (ih b b.2).trans_lt (WellFounded.rank_lt_of_rel (f.map_rel b.2))

