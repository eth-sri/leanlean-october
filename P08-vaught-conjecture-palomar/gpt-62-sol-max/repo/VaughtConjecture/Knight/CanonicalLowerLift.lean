/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeOneLift
public import VaughtConjecture.Knight.GradeCutLifting
public import VaughtConjecture.Knight.CanonicalLowerDomain

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalLowerLift

open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (k : ℕ) (hkA : k ≤ A.card) (h1k : 1 < k)
  (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ k)

local notation "M" => Frame.mk sem 1 k (Nat.zero_lt_succ 0) h1k hkA hproper hg
local notation "hA" => Nat.le_trans (Nat.le_of_lt h1k) hkA
local notation "S" => scheme M

def oldLow (d : Cell D) (hd : D.grade d ≤ 1) :
    (S).below (A, 1) :=
  ⟨oldCell M (lowerOld M d), by
    simpa only [oldCell, lowerOld, CanonicalGradeCutSections.old,
      SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using
      (show GradedLe (D.cell d) (A, 1) from
        ⟨D.scope_subset d, hd⟩)⟩

theorem equiv_old (d : Cell (GradeCutBoundary.scheme D 1)) :
    CanonicalLowerDomain.equiv M (A, 1) le_rfl
      (CanonicalFieldOwnerLift.oldTarget (GradeCutBoundary.rows D 1 sem) 1 (Cell D)
        (GradeCutBoundary.toCell D 1) (by decide) hA
        (GradeCutBoundary.grade_bound D 1) d) =
      oldLow sem k hkA h1k hproper hg (GradeCutBoundary.toCell D 1 d)
        (GradeCutBoundary.grade_bound D 1 d) := by
  apply Subtype.ext
  change oldCell M
    (GradeCutLayerCarrier.embed D (CanonicalGradeCutSections.Profiles sem 1) 1 (by decide) hA
      (SourceLayerCarrier.toCell (GradeCutBoundary.scheme D 1)
        (CanonicalGradeCutSections.Profiles sem 1) 1 (by decide) hA (.inl d))) = _
  rw [GradeCutLayerCarrier.embed, SourceLayerCarrier.appendMap_toCell]
  rfl

/-- The actual lower-layer lift, from arbitrary lawful local inputs. It
restores distinct values and top, with no bound by an upper-grade owner.
The only section-supply inputs are the two OLD face lifting clauses. -/
theorem exists_positive_lift {C : Finset ι}
    (hfull : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : D.below (C, 1) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, 1) p)
    {q : (S).below (A, 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows M) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (C, 1),
      min (p e) γ = min (q (oldLow sem k hkA h1k hproper hg e.1 e.2.2)) γ)
    (W : CutCover sem (C, 1) 1) :
    ∃ r : (S).below (A, 1) → ExtOrd,
      RespectsSemanticsBelow (rows M) (A, 1) r ∧
      (∀ e : D.below (C, 1), r (oldLow sem k hkA h1k hproper hg e.1 e.2.2) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  let eC := GradeCutBoundary.belowEquiv D 1 (C, 1) le_rfl
  let eA := CanonicalLowerDomain.equiv M (A, 1) le_rfl
  have hp' := GradeCutBoundary.pullback_respects D 1 sem le_rfl hp
  have hq' := CanonicalLowerDomain.pullback_respects M
    le_rfl hq
  have hf : ∃ c : (GradeCutBoundary.scheme D 1).below (C, 1),
      (GradeCutBoundary.scheme D 1).cell c.1 = (C, 1) := by
    obtain ⟨c, hc⟩ := hfull
    refine ⟨eC.symm c, ?_⟩
    have he := congrArg (fun z : D.below (C, 1) => D.cell z.1) (eC.apply_symm_apply c)
    exact he.trans hc
  have hmap (e : (GradeCutBoundary.scheme D 1).below (C, 1)) :
      eA (CanonicalFieldOwnerLift.oldTarget (GradeCutBoundary.rows D 1 sem) 1 (Cell D)
        (GradeCutBoundary.toCell D 1) (by decide) hA
        (GradeCutBoundary.grade_bound D 1) e.1) =
      oldLow sem k hkA h1k hproper hg (eC e).1 (eC e).2.2 :=
    equiv_old sem k hkA h1k hproper hg e.1
  obtain ⟨r, hr, hread, hcap⟩ := CanonicalGradeOneLift.exists_positive_lift
    (GradeCutBoundary.rows D 1 sem) (Cell D) (GradeCutBoundary.toCell D 1) hA
    (GradeCutBoundary.proper D 1 hproper) (GradeCutBoundary.grade_bound D 1)
    (GradeCutBoundary.toCell D 1).injective hf hp' hq' hγ hγb
    (fun e => by
      change min (p (eC e)) γ = min (q (eA _)) γ
      rw [hmap]
      exact hag (eC e))
    (GradeCutLifting.cutCover sem 1 W)
  refine ⟨r ∘ eA.symm,
    (CanonicalLowerDomain.respects_iff M
      (A, 1) le_rfl r).mp hr, ?_, ?_⟩
  · intro e
    have he := hread (eC.symm e)
    grind
  grind

end

end VaughtConjecture.Knight.CanonicalLowerLift
