/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedProjection

@[expose] public section

namespace VaughtConjecture.Knight.GrowthReplicatedReadback

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources GrowthHigherMixed

open GrowthPaddedContract GrowthPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "Rows" => GrowthHigherMixed.rows G

/-- The boundary index of a placed private cell. -/
theorem private_cell (d : Cell G.I.right.scheme) :
    G.I.boundary.cell (G.I.rightFace.map d) =
      ((G.I.right.scheme.scope d).image G.I.placeRight, G.I.right.scheme.grade d) :=
  G.I.rightFace.index d

/-- The boundary index of a placed donor cell. -/
theorem donor_cell (d : Cell G.I.left.scheme) :
    G.I.boundary.cell (G.I.leftFace.map d) =
      ((G.I.left.scheme.scope d).image G.I.placeLeft, G.I.left.scheme.grade d) :=
  G.I.leftFace.index d

theorem private_scope_le (d : Cell G.I.right.scheme) :
    (G.I.right.scheme.scope d).image G.I.placeRight ⊆ C := (Finset.image_subset_image (Finset.subset_univ _)).trans (Finset.subset_of_eq G.I.imageRight)

theorem donor_scope_le (d : Cell G.I.left.scheme) :
    (G.I.left.scheme.scope d).image G.I.placeLeft ⊆ B := (Finset.image_subset_image (Finset.subset_univ _)).trans (Finset.subset_of_eq G.I.imageLeft)

variable (U : Finset ι) (j : ℕ)

/-- An original boundary cell as an occurrence of the observed section: the inherited cell
of the replicated carrier, not a copy. -/
def originalAt (d : Cell G.I.boundary) (hd : GradedLe (G.I.boundary.cell d) (U, j)) :
    CellScheme.below (carrier G) (U, j) :=
  ScopeReplicationCarrier.oldBelow (GrowthReplicatedRows.frame P) (U, j)
    ⟨original G d, by rw [original_index]; exact hd⟩

theorem erase_originalAt (d : Cell G.I.boundary) (hd : GradedLe (G.I.boundary.cell d) (U, j)) :
    erase G (originalAt G U j d hd).1 =
      original G d :=
  ScopeReplicationCarrier.erase_old (GrowthReplicatedRows.frame P) _

variable (hBU : B ⊆ U) (hCU : C ⊆ U)

/-- The occurrence of a private original of grade at most `j`. -/
def privateAt (d : Cell G.I.right.scheme) (hd : G.I.right.scheme.grade d ≤ j) :
    CellScheme.below (carrier G) (U, j) :=
  originalAt G U j (G.I.rightFace.map d)
    (by rw [private_cell]; exact ⟨(private_scope_le G d).trans hCU, hd⟩)

/-- The occurrence of a donor original of grade at most `j`. -/
def donorAt (d : Cell G.I.left.scheme) (hd : G.I.left.scheme.grade d ≤ j) :
    CellScheme.below (carrier G) (U, j) :=
  originalAt G U j (G.I.leftFace.map d)
    (by rw [donor_cell]; exact ⟨(donor_scope_le G d).trans hBU, hd⟩)

section Readback

variable {G} (W : Cut G) (hBU : B ⊆ W.scope) (hCU : C ⊆ W.scope)
  {p : CellScheme.below (carrier G) W.index → ExtOrd}

/-- A private original reads its complete field capped at the height of its own grade. -/
theorem private_readback (hp : RespectsSemanticsBelow Rows W.index p)
    (d : Cell G.I.right.scheme) (hd : G.I.right.scheme.grade d ≤ W.grade) :
    p (privateAt G W.scope W.grade hCU d hd) =
      min (shadowSup W p
        (GrowthOrderedBase.field G.I (G.I.rightFace.map d)))
        (height W p (G.I.right.scheme.grade d)) := by
  have h := projection_readback W hp
    (privateAt G W.scope W.grade hCU d hd) (G.I.rightFace.map d)
    (erase_originalAt G W.scope W.grade _ _)
  rwa [show G.I.boundary.grade (G.I.rightFace.map d) = G.I.right.scheme.grade d from
    congrArg Prod.snd (private_cell G d)] at h

/-- A donor original reads its complete field capped at the height of its own grade. -/
theorem donor_readback_height (hp : RespectsSemanticsBelow Rows W.index p)
    (d : Cell G.I.left.scheme) (hd : G.I.left.scheme.grade d ≤ W.grade) :
    p (donorAt G W.scope W.grade hBU d hd) =
      min (shadowSup W p
        (GrowthOrderedBase.field G.I (G.I.leftFace.map d)))
        (height W p (G.I.left.scheme.grade d)) := by
  have h := projection_readback W hp
    (donorAt G W.scope W.grade hBU d hd) (G.I.leftFace.map d)
    (erase_originalAt G W.scope W.grade _ _)
  rwa [show G.I.boundary.grade (G.I.leftFace.map d) = G.I.left.scheme.grade d from
    congrArg Prod.snd (donor_cell G d)] at h

end Readback

variable (hN : G.X.req.N ≤ j)

include hN in
/-- The private cap's grade is the activation grade, so its occurrence is observed. -/
theorem cap_grade_le : G.I.right.scheme.grade G.X.req.C ≤ j := G.X.grade_C.trans_le hN

/-- Every donor cell has grade at most the activation grade. -/
theorem donor_grade_le (d : Cell G.I.left.scheme) : G.I.left.scheme.grade d ≤ G.X.req.N :=
  (G.X.below_top d).2.trans G.X.top_le_N

/-- The grade bound of a private cell below the cap. -/
theorem grade_le_of_below_cap (d : G.I.right.scheme.below (G.I.right.scheme.cell G.X.req.C)) :
    G.I.right.scheme.grade d.1 ≤ G.X.req.N :=
  d.2.2.trans_eq G.X.grade_C

/-- The activation grade is the actual cap's grade, bounded by the private arity. -/
theorem threshold_le_card : G.X.req.N ≤ A.card := by
  have hg := G.I.right.scheme.grade_le_card_scope G.X.req.C
  rw [G.X.grade_C] at hg
  have h1 := Finset.card_le_card (Finset.subset_univ (G.I.right.scheme.scope G.X.req.C))
  have h2 : (Finset.univ : Finset (Fin J)).card = C.card := by
    rw [← G.I.imageRight, Finset.card_image_of_injective _ G.I.placeRight.injective]
  have h3 := Finset.card_le_card (Finset.ssubset_iff_subset_ne.mp G.rightProper).1
  omega

/-- The installed private occurrence map is the inherited original occurrence. -/
theorem privateFace_map (d : Cell G.I.right.scheme) (hd : G.I.right.scheme.grade d ≤ A.card) :
    (GrowthReplicatedRows.privateFace G).map d =
      (privateAt G A A.card (Finset.ssubset_iff_subset_ne.mp G.rightProper).1 d hd).1 := rfl

/-- The installed donor occurrence map is the inherited original occurrence. -/
theorem donorFace_map (d : Cell G.I.left.scheme) (hd : G.I.left.scheme.grade d ≤ A.card) :
    (GrowthReplicatedRows.donorFace G).map d =
      (donorAt G A A.card (Finset.ssubset_iff_subset_ne.mp G.leftProper).1 d hd).1 := rfl

end

end VaughtConjecture.Knight.GrowthReplicatedReadback
