/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthTemplate
public import VaughtConjecture.Knight.GrowthScalarLedger

/-! # Constructed hollow-growth input, admission and stage-bounded decoding

The relative template is acquired from the model. Its root attachment is
literal, its bottom class is actual, and its original actual pair is admitted
at every cutoff. The supported decoder is defined at all ordinal arguments;
this is not yet a lawful physical display or a receiving theorem.
-/

@[expose] public section

namespace VaughtConjecture.Knight.HollowGrowthTemplate
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open CellScheme.restrictFace Transform
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} (q : S α.1 (n + 1)) {Nmin : ℕ}
  (D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) Nmin)

/-- A model supplies every scalar input; no reference or template existence
assumption is left. Positive root arity remains explicit. -/
theorem acquire (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    (hn : 0 < n) (hp : W.eval t = some p) (hq : IsCoface p q) (floor : ℕ) :
    ∃ D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) floor,
      Nonempty (Input q D) := by
  obtain ⟨D⟩ := HollowGrowthReference.exists_data hM hg hh t p hp
    (donorRequests q) (donorRequests_ok q) (n + 1) floor
  exact ⟨D, exists_input q D hn hq⟩

namespace Input
variable {q D} (I : Input q D)

private theorem inClass_iff_of_heq {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {DA : CellScheme A} {B C : Finset ι × ℕ} (hBC : B = C)
    {ZA : Set (DA.below B)} {ZC : Set (DA.below C)} (hZ : HEq ZA ZC)
    (u : DA.Labelling) : InClass ZA u ↔ InClass ZC u := by
  subst C
  rw [eq_of_heq hZ]

/-- The relation is tested on the entire actual private bottom class below
the cap, not a selected or synchronized subclass. -/
theorem inClass_iff (u : D.context.type.scheme.scheme.Labelling) :
    InClass I.relative.ZA u ↔ ∀ d : D.context.type.scheme.scheme.RowDomain D.cap,
      u d.1 = ⊥ ↔ D.context.type.label d.1 = ⊥ :=
  inClass_iff_of_heq (congrArg (fun r => D.context.type.scheme.scheme.cell r.C) I.req_eq)
    I.class_eq u

end Input
end
end VaughtConjecture.Knight.HollowGrowthTemplate
