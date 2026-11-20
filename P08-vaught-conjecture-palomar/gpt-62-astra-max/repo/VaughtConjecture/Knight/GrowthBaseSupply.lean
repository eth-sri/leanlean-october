/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthOrderedBase
public import VaughtConjecture.Knight.ReceivingCatalogueRanks

/-! # Independent physical supply on the growth padded base

As in `LowOnlyGradeOneSupply`, terminal insertion retains complete field ranks,
then the actual numerical table is rendered on the installed anchor. Long-row
lawfulness is proved directly, not by positive-cap transport at bottom.
-/

@[expose] public section

namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd CappedDonor.Ref CanonicalPairedInverse
open LadderScalarRendering ReceivingCatalogueRanks
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

theorem exists_rank_anchor {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hs : Admitted X j S) :
    ∃ a : Catalogue X j, ∀ d, fieldRank a.val d = fieldRank S.profile d :=
  ProfileCatalogue.rank_member (profileFamily X j) hj hs

end
end VaughtConjecture.Knight.Growth

namespace VaughtConjecture.Knight.GrowthOrderedBase
open Transform Value ExtOrd AmalgamationPlan Growth RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.Attachment X)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev scheme := carrier I.boundary hA
  (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)
abbrev semantics := rows I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)

def privateIncl (d : I.right.Native 1) : I.boundary.below (A, 1) :=
  ⟨I.rightFace.map d.1,
    I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2⟩

def donorIncl (d : I.left.Native 1) : I.boundary.below (A, 1) :=
  ⟨I.leftFace.map d.1,
    I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩

def oldAt (d : I.boundary.below (A, 1)) : (scheme I X hA).below (A, 1) :=
  ⟨old I.boundary hA d.1, by rw [old_index]; exact d.2⟩
abbrev privateAt (d : I.right.Native 1) := oldAt I X hA (privateIncl I d)
abbrev donorAt (d : I.left.Native 1) := oldAt I X hA (donorIncl I d)

include T in
theorem exists_physical_section {S : State I.right.scheme I.left.scheme}
    (hs : Admitted X 1 S) :
    ∃ w : (scheme I X hA).SectionAt (A, 1),
      (semantics I X hA hB hC).Lawful w ∧
      ∀ d : I.boundary.below (A, 1), w (oldAt I X hA d) = S.profile (field I d.1) := by
  obtain ⟨a, ha⟩ := exists_rank_anchor X (by decide : 1 ≤ 1) hs
  refine ⟨fun d => renderWith I.boundary hA (field I) (fields I X) a S.profile ⊤ d.1,
    renderWith_respects I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)
      a S.profile ha (fun _ => le_top) hs.visible (extVisibilityReplace_top 1 1)
      (boundary_lawful I X T hs), ?_⟩
  intro d
  exact renderWith_old I.boundary hA (field I) (fields I X) a S.profile ⊤ ha d.1

include T in
theorem private_bottom_supply {p : I.right.Native 1 → ExtOrd}
    (hp : I.right.rows.Lawful p) :
    ∃ w, (semantics I X hA hB hC).Lawful w ∧
      ∀ d, w (privateAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.private_all (zero_admitted X 1) hp
    (selfVis_bot 1) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (privateIncl I d)).trans
    ((field_private I X T hs d.1).trans (he d))⟩

include T in
theorem donor_bottom_supply (hN : 1 < X.req.N)
    {p : I.left.Native 1 → ExtOrd}
    (hp : I.left.rows.Lawful p) :
    ∃ w, (semantics I X hA hB hC).Lawful w ∧
      ∀ d, w (donorAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.donor_before hN (zero_admitted X 1) hp
    (selfVis_bot 1) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (donorIncl I d)).trans
    ((field_donor I S d.1).trans (he d))⟩

end
end VaughtConjecture.Knight.GrowthOrderedBase
