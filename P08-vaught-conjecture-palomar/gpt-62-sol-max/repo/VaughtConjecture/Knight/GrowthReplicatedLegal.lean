/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthReplicatedBountiful
public import VaughtConjecture.Knight.OrderedFaceRestriction

@[expose] public section

namespace VaughtConjecture.Knight.GrowthReplicatedLegal

open Transform Value ExtOrd AmalgamationPlan Growth

noncomputable section

variable {l m n J : ℕ} {B C : Finset (Fin l)}
  {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hsmall : n + 1 < X.req.N)

local notation "G" => GrowthPaddedIteration.BuildContext.full I X T hA hB hC

/-- The actual full-height replicated carrier, with no assumed output lift. -/
def semScheme : SemScheme l where
  scheme := GrowthHigherMixed.carrier G
  rows := GrowthHigherMixed.rows G
  rows_coded := GrowthReplicatedRows.build_coded G
  consistent := GrowthReplicatedRows.consistent (G).tower
  bountiful := GrowthReplicatedBountiful.bountiful I X T hA hB hC hsmall
  complete := GrowthReplicatedRows.complete G (Nat.sub_add_cancel hA).ge

local notation "E" => semScheme I X T hA hB hC hsmall

theorem plan : (E).scheme.plan = R :=
  GrowthPaddedIteration.build_plan I X T hA hB hC _ _

def donor : ExactSemanticFace I.leftRows (E).rows :=
  GrowthReplicatedRows.donorFace G

def privateFace : ExactSemanticFace I.rightRows (E).rows :=
  GrowthReplicatedRows.privateFace G

theorem donor_receipt :
    OrderedFaceRestriction.Receipt I.left E I.placeLeft (donor I X T hA hB hC hsmall).map :=
  I.left_receipt (plan I X T hA hB hC hsmall) _ (GrowthReplicatedRows.donor_order G)

theorem private_receipt :
    OrderedFaceRestriction.Receipt I.right E I.placeRight (privateFace I X T hA hB hC hsmall).map :=
  I.right_receipt (plan I X T hA hB hC hsmall) _ (GrowthReplicatedRows.private_order G)

end

end VaughtConjecture.Knight.GrowthReplicatedLegal
