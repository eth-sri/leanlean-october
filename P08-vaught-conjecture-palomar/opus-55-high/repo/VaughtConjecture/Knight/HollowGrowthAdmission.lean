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

/-- Receipts of the constructed scalar input, not a physical-probe interface. -/
structure Input where
  donor_type : typeMap Fin.castSuccEmb q = some p
  hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan
  hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme
  hvC : Finset.univ.image D.face ∈ D.context.type.scheme.scheme.plan
  hC : D.context.type.scheme.restrictFace D.face hvC = p.scheme
  relative : RelativeData D.context.type.scheme.scheme D.context.type.scheme.rows
    q.scheme.scheme q.scheme.rows
  req_eq : relative.req = requests q D
  top_eq : relative.top = (Finset.univ, n + 1)
  attachment : Growth.RootAttachment p.scheme Fin.castSuccEmb hvP hP D.face hvC hC relative
  class_eq : HEq relative.ZA {d : D.context.type.scheme.scheme.below
    (D.context.type.scheme.scheme.cell D.cap) | D.context.type.label d.1 = ⊥}

theorem exists_input (hn : 0 < n) (hq : IsCoface p q) : Nonempty (Input q D) := by
  obtain ⟨hvP, hP, hvC, hC, X, hreq, htop, ⟨R⟩, hclass⟩ := exists_template q D hn hq
  exact ⟨⟨hq, hvP, hP, hvC, hC, X, hreq, htop, R, hclass⟩⟩

/-- A model supplies every scalar input; no reference or template existence
assumption is left. Positive root arity remains explicit. -/
theorem acquire (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    (hn : 0 < n) (hp : W.eval t = some p) (hq : IsCoface p q) floor :
    ∃ D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) floor,
      Nonempty (Input q D) := by
  obtain ⟨D⟩ := HollowGrowthReference.exists_data hM hg hh t p hp
    (donorRequests q) (donorRequests_ok q) (n + 1) floor
  exact ⟨D, exists_input q D hn hq⟩

namespace Input
variable {q D} (I : Input q D)

private theorem inClass_iff_of_heq {ι} [DecidableEq ι] {A}
    {DA : CellScheme A} {B C : Finset ι × ℕ} (hBC : B = C)
    {ZA : Set (DA.below B)} {ZC : Set (DA.below C)} (hZ : HEq ZA ZC)
    u : InClass ZA u ↔ InClass ZC u := by
  subst C
  rw [eq_of_heq hZ]

/-- The relation is tested on the entire actual private bottom class below
the cap, not a selected or synchronized subclass. -/
theorem inClass_iff (u : Cell D.context.type.scheme.scheme → ExtOrd) :
    InClass I.relative.ZA u ↔ ∀ d : D.context.type.scheme.scheme.below
      (D.context.type.scheme.scheme.cell D.cap),
      u d.1 = ⊥ ↔ D.context.type.label d.1 = ⊥ :=
  inClass_iff_of_heq (congrArg (fun r => D.context.type.scheme.scheme.cell r.C) I.req_eq)
    I.class_eq u

theorem actual_inClass : InClass I.relative.ZA D.context.type.label :=
  (I.inClass_iff _).mpr (fun _ => Iff.rfl)

theorem donor_arity_lt : n + 1 < I.relative.req.N := by
  rw [I.req_eq]
  exact (requests q D).R_lt_N

/-- Correctness, if extracted from the eventual physical rows over this actual
private face, reads the entire donor literally. It is not assumed extracted. -/
theorem exact_of_correct {v}
    (h : I.relative.req.Correct (I.relative.req.sec D.context.type.label) v) : v = q.label := by
  rw [I.req_eq] at h
  exact (correct_iff_eq_actual q D v).mp h

end Input
end
end VaughtConjecture.Knight.HollowGrowthTemplate
