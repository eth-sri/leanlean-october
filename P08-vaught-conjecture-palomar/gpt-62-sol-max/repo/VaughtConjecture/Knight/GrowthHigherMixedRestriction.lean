/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedProjection

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Rows" => rows G

theorem original_or_full (c : Cell (P).carrier) :
    (∃ d : Cell G.I.boundary, c = original G d) ∨ (P).carrier.scope c = A := by
  rcases (P).cases c with ⟨b, rfl⟩ | ⟨hs, _, _⟩
  · rcases RelativeLadderLayer.cell_cases G.I.boundary G.pos b with
      ⟨d, rfl⟩ | ⟨v, rfl⟩
    · tauto
    · exact Or.inr (congrArg Prod.fst (ladder_index G v))
  · exact Or.inr hs

section Maxima

variable {G} (W : Cut G) {p q : CellScheme.below (carrier G) W.index → ExtOrd}

theorem gradeMax_eq_of_auxiliary (hp : RespectsSemanticsBelow Rows W.index p)
    (hq : RespectsSemanticsBelow Rows W.index q)
    (haux : ∀ z : (D).below W.index, (P).carrier.scope (erase G z.1) = A →
      p z = q z) (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ W.grade) :
    gradeMax W p k = gradeMax W q k := by
  have hle {r s : (D).below W.index → ExtOrd} (hr : RespectsSemanticsBelow Rows W.index r)
      (heq : ∀ z : (D).below W.index,
        (P).carrier.scope (erase G z.1) = A → r z = s z) :
      gradeMax W r k ≤ gradeMax W s k := by
    obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner W
      hr k hk hkj
    rw [← hmax, heq _ (by rw [erase_place]; exact hc)]
    exact le_gradeMax W s k _
      ((congrArg Prod.snd (place_index W _ _ _)).trans hg)
  exact le_antisymm (hle hp haux) (hle hq (fun z hz => (haux z hz).symm))

end Maxima

variable {G} (W : Cut G) (V : Finset ι) (hV : V ∈ R)
  (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V) (hUV : W.scope ⊆ V)
  {p q : CellScheme.below (carrier G) (V, W.grade) → ExtOrd}

include hV hmV in
/-- Every occurrence is determined, including unused auxiliary copies and
originals whose scopes are incomparable with the prescribed scope. -/
theorem eq_of_restriction (hp : RespectsSemanticsBelow Rows (V, W.grade) p)
    (hq : RespectsSemanticsBelow Rows (V, W.grade) q)
    (hag : ∀ d : (D).below W.index,
      p (CellScheme.below.mono (show GradedLe W.index (V, W.grade) from ⟨hUV, le_rfl⟩) d) =
      q (CellScheme.below.mono (show GradedLe W.index (V, W.grade) from ⟨hUV, le_rfl⟩) d)) : p = q := by
  let T := W.raise V hV hmV hUV
  have haux (z : (D).below (V, W.grade))
      (hz : (P).carrier.scope (erase G z.1) = A) : p z = q z :=
    ScopeReplicationSemantics.auxiliary_eq (GrowthReplicatedRows.frame P) 
      W.plan W.mixed W.card T.plan T.mixed T.card hUV hp hq hag z hz
  have hshadow (f : Field G.I.right.scheme G.I.left.scheme) :
      shadowSup T p f =
        shadowSup T q f := by
    apply Finset.sup_congr rfl
    intro a _
    apply haux
    rw [erase_ladderAt]
    exact congrArg Prod.fst (ladder_index G _)
  have hheight (k : ℕ) : height T p k =
      height T q k := by
    unfold height
    split_ifs with hk hkj
    · rfl
    · exact gradeMax_eq_of_auxiliary T hp hq haux
        k (by omega) hkj
    · rfl
  funext z
  rcases original_or_full G (erase G z.1) with
      ⟨d, hd⟩ | hz
  · rw [projection_readback T hp z d hd,
      projection_readback T hq z d hd,
      hshadow, hheight]
  · exact haux z hz

end

end VaughtConjecture.Knight.GrowthHigherMixed
