/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthHigherMixedProjection

/-! # Restriction injectivity at every fixed-carrier mixed cutoff

Equality of actual auxiliary copies determines all shadow maxima. Each grade
maximum is attained at an auxiliary owner, so equality of those maxima does
not presuppose equality of the still-hidden originals. Exact grade-dependent
readback then determines every original. This is uniqueness, not extension.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower frame t ht
local notation "D" => carrier frame t ht
local notation "Rows" => rows frame t ht

theorem original_or_full (c : Cell (P).carrier) :
    (∃ d : Cell I.boundary, c = original frame t ht d) ∨ (P).carrier.scope c = A := by
  rcases (P).cases c with ⟨b, rfl⟩ | ⟨hs, _, _⟩
  · rcases RelativeLadderLayer.cell_cases I.boundary frame.positive b with
      ⟨d, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨d, rfl⟩
    · exact Or.inr (congrArg Prod.fst (ladder_index frame t ht v))
  · exact Or.inr hs

section Maxima
variable (V : Finset ι) (hV : V ∈ R)
  (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
  (j : ℕ) (hjV : j ≤ V.card)
  {p q : CellScheme.below (carrier frame t ht) (V, j) → ExtOrd}

include hV hmV hjV in
theorem gradeMax_eq_of_auxiliary (hp : RespectsSemanticsBelow Rows (V, j) p)
    (hq : RespectsSemanticsBelow Rows (V, j) q)
    (haux : ∀ z : (D).below (V, j), (P).carrier.scope (erase frame t ht z.1) = A →
      p z = q z) (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) (hkt : k ≤ t + 2) :
    gradeMax frame t ht V j p k = gradeMax frame t ht V j q k := by
  have hle {r s : (D).SectionAt (V, j)} (hr : RespectsSemanticsBelow Rows (V, j) r)
      (heq : ∀ z : (D).below (V, j),
        (P).carrier.scope (erase frame t ht z.1) = A → r z = s z) :
      gradeMax frame t ht V j r k ≤ gradeMax frame t ht V j s k := by
    obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner frame t ht V hV hmV j hjV
      hr k hk hkj hkt
    rw [← hmax, heq _ (by rw [erase_place]; exact hc)]
    exact le_gradeMax frame t ht V j s k _
      ((congrArg Prod.snd (place_index frame t ht V hV hmV j hjV _ _ _)).trans hg)
  exact le_antisymm (hle hp haux) (hle hq (fun z hz => (haux z hz).symm))

end Maxima

variable (U V : Finset ι) (hU : U ∈ R) (hV : V ∈ R)
  (hmU : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
  (j : ℕ) (hjU : j ≤ U.card) (hjV : j ≤ V.card) (hj0 : 1 ≤ j) (hjt : j ≤ t + 2)
  (hUV : U ⊆ V)
  {p q : CellScheme.below (carrier frame t ht) (V, j) → ExtOrd}

include hU hV hmU hmV hjU hjV hj0 hjt in
/-- Every occurrence is determined, including unused auxiliary copies and
originals whose scopes are incomparable with the prescribed scope. -/
theorem eq_of_restriction (hp : RespectsSemanticsBelow Rows (V, j) p)
    (hq : RespectsSemanticsBelow Rows (V, j) q)
    (hag : ∀ d : (D).below (U, j),
      p (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d) =
      q (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d)) : p = q := by
  have haux (z : (D).below (V, j))
      (hz : (P).carrier.scope (erase frame t ht z.1) = A) : p z = q z :=
    ScopeReplicationRestriction.auxiliary_eq (P).carrier B C
      (GrowthReplicatedRows.proper_covered P) (P).rows
      (by rw [GrowthPaddedIteration.build_plan]; exact hU) hmU hjU
      (by rw [GrowthPaddedIteration.build_plan]; exact hV) hmV hjV hUV hp hq hag z hz
  have hshadow (f : Field I.right.scheme I.left.scheme) :
      shadowSup frame t ht V hV hmV j hjV hj0 p f =
        shadowSup frame t ht V hV hmV j hjV hj0 q f := by
    apply Finset.sup_congr rfl
    intro a _
    apply haux
    rw [erase_ladderAt]
    exact congrArg Prod.fst (ladder_index frame t ht _)
  have hheight (k : ℕ) : height frame t ht V j p k =
      height frame t ht V j q k := by
    unfold height
    split_ifs with hk hkj
    · rfl
    · exact gradeMax_eq_of_auxiliary frame t ht V hV hmV j hjV hp hq haux
        k (by omega) hkj (hkj.trans hjt)
    · rfl
  funext z
  rcases original_or_full frame t ht (erase frame t ht z.1) with
      ⟨d, hd⟩ | hz
  · rw [projection_readback frame t ht V hV hmV j hjV hj0 hp hjt z d hd,
      projection_readback frame t ht V hV hmV j hjV hj0 hq hjt z d hd,
      hshadow, hheight]
  · exact haux z hz

end
end VaughtConjecture.Knight.GrowthHigherMixed
