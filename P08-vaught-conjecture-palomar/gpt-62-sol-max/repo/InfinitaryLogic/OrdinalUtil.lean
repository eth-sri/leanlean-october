/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.SetTheory.Ordinal.Family

@[expose] public section

universe u

namespace InfinitaryLogic

/-- For `β < ω₁`, the ordinals below `β` form a countable **type**. -/
theorem countable_Iio_of_lt_omega1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega 1) :
    Countable (Set.Iio β) := by
  have hle : β.card ≤ Cardinal.aleph0 := by
    have hlt : β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp hβ
    simp_all
  rw [← Cardinal.mk_le_aleph0_iff]
  calc Cardinal.mk (Set.Iio β)
      = Cardinal.lift.{1, 0} β.card := Cardinal.mk_Iio_ordinal β
    _ ≤ Cardinal.lift.{1, 0} Cardinal.aleph0 := Cardinal.lift_le.mpr hle
    _ = Cardinal.aleph0 := by simp

/-- The same fact as a `Set.Countable`. -/
theorem setCountable_Iio_of_lt_omega1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega 1) :
    Set.Countable (Set.Iio β) :=
  Set.countable_coe_iff.mp (countable_Iio_of_lt_omega1 β hβ)

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

end InfinitaryLogic
