/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SchemeBoundaryFaceMap
public import VaughtConjecture.Knight.OrderedFaceBoundarySemantics
public import VaughtConjecture.Knight.CappedLifting
public import VaughtConjecture.Knight.FullScopeZeroExtension

@[expose] public section

namespace VaughtConjecture.Knight.WholeDonorBoundary

open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension

open AmalgamatedBoundary (Overlap pointImage pointImage_complete)

open SemSchemeBoundaryInput (faceMap faceMap_index faceMap_exhaustive faceMap_total)

noncomputable section

variable {ι : Type*} [DecidableEq ι] (A B C : Finset ι)

variable (R : Finset (Finset ι))

/-- Two legal inputs on arbitrary faces with one literal common face.
Only point placements, plan restrictions, and input equalities are fields;
output consistency, row compatibility, and lower-domain transport are derived. -/
structure Input (m nL nR : ℕ) where
  isPlan : Plan.IsPlan A R
  left : SemScheme nL
  right : SemScheme nR
  common : SemScheme m
  placeLeft : Fin nL ↪ ι
  placeRight : Fin nR ↪ ι
  imageLeft : Finset.univ.image placeLeft = B
  imageRight : Finset.univ.image placeRight = C
  commonLeft : Fin m ↪ Fin nL
  commonRight : Fin m ↪ Fin nR
  visibleLeft : Finset.univ.image commonLeft ∈ left.scheme.plan
  visibleRight : Finset.univ.image commonRight ∈ right.scheme.plan
  faceLeft : left.restrictFace commonLeft visibleLeft = common
  faceRight : right.restrictFace commonRight visibleRight = common
  commute : commonLeft.trans placeLeft = commonRight.trans placeRight
  intersection : (Finset.univ.image commonLeft).image placeLeft =
    B ∩ C
  planLeft : Plan.restrictPlan R B = left.scheme.plan.image (Finset.image placeLeft)
  planRight : Plan.restrictPlan R C = right.scheme.plan.image (Finset.image placeRight)

namespace Input

variable {A B C R} {m nL nR : ℕ} (I : Input A B C R m nL nR)

abbrev leftScheme := pointImage I.left.scheme I.placeLeft I.imageLeft

abbrev rightScheme := pointImage I.right.scheme I.placeRight I.imageRight

abbrev leftRows := PointImageSemantics.rows I.left.scheme I.placeLeft I.imageLeft I.left.rows

abbrev rightRows := PointImageSemantics.rows I.right.scheme I.placeRight I.imageRight I.right.rows

private theorem common_image_right :
    (Finset.univ.image I.commonRight).image I.placeRight =
      B ∩ C := by
  rw [Finset.image_image, ← I.intersection, Finset.image_image]
  exact congrArg (fun e : Fin m ↪ ι => Finset.univ.image e) I.commute.symm

/-- Exchange the two sides of the same literal attachment. -/
def swap : Input A C B R m nR nL where
  isPlan := I.isPlan
  left := I.right
  right := I.left
  common := I.common
  placeLeft := I.placeRight
  placeRight := I.placeLeft
  imageLeft := I.imageRight
  imageRight := I.imageLeft
  commonLeft := I.commonRight
  commonRight := I.commonLeft
  visibleLeft := I.visibleRight
  visibleRight := I.visibleLeft
  faceLeft := I.faceRight
  faceRight := I.faceLeft
  commute := I.commute.symm
  intersection := by exact (common_image_right I).trans (Finset.inter_comm _ _)
  planLeft := I.planRight
  planRight := I.planLeft

private theorem image_common (T : Finset (Fin m)) :
    (T.image I.commonLeft).image I.placeLeft =
      (T.image I.commonRight).image I.placeRight := by
  rw [Finset.image_image, Finset.image_image]
  exact congrArg (fun e : Fin m ↪ ι => T.image e) I.commute

/-- The overlap is derived from the actual restricted occurrence enumerations. -/
def shared : Overlap I.leftScheme I.rightScheme I.common.scheme.card where
  f := (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft).toEmbedding
  g := (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight).toEmbedding
  f_mono := (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft).strictMono
  g_mono := (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight).strictMono
  shared d := by
    change ((I.left.scheme.cell
        (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft d)).1.image I.placeLeft,
        (I.left.scheme.cell
          (faceMap I.left I.common I.commonLeft I.visibleLeft I.faceLeft d)).2) =
      ((I.right.scheme.cell
        (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight d)).1.image I.placeRight,
        (I.right.scheme.cell
          (faceMap I.right I.common I.commonRight I.visibleRight I.faceRight d)).2)
    rw [faceMap_index I.left I.common I.commonLeft I.visibleLeft I.faceLeft d,
      faceMap_index I.right I.common I.commonRight I.visibleRight I.faceRight d]
    exact Prod.ext (image_common I _) rfl
  left_exhaustive d hd := by
    apply faceMap_exhaustive
    apply (Finset.image_subset_image_iff I.placeLeft.injective).mp
    rw [I.intersection]
    exact Finset.subset_inter
      (by grind) hd
  right_exhaustive d hd := by
    apply faceMap_exhaustive
    apply (Finset.image_subset_image_iff I.placeRight.injective).mp
    rw [common_image_right I]
    exact Finset.subset_inter hd
      (by grind)

theorem compatible : OrderedFaceBoundaryRows.Compatible I.leftScheme I.rightScheme
    I.shared I.leftRows I.rightRows := by
  intro c d
  exact (PointImageSemantics.total_eq I.left.scheme I.placeLeft I.imageLeft I.left.rows
    (I.shared.f c) (I.shared.f d)).trans
    (((faceMap_total I.left I.common I.commonLeft I.visibleLeft I.faceLeft c d).trans
      (faceMap_total I.right I.common I.commonRight I.visibleRight I.faceRight c d).symm).trans
      (PointImageSemantics.total_eq I.right.scheme I.placeRight I.imageRight I.right.rows
        (I.shared.g c) (I.shared.g d)).symm)

theorem leftPlan_le : I.leftScheme.plan ⊆ R := by
  intro S hS
  change S ∈ I.left.scheme.plan.image (Finset.image I.placeLeft) at hS
  rw [← I.planLeft] at hS
  exact (Finset.mem_inter.mp hS).1

theorem rightPlan_le : I.rightScheme.plan ⊆ R := by
  intro S hS
  change S ∈ I.right.scheme.plan.image (Finset.image I.placeRight) at hS
  rw [← I.planRight] at hS
  exact (Finset.mem_inter.mp hS).1

abbrev boundary := OrderedFaceBoundary.scheme I.leftScheme I.rightScheme I.shared
  R I.isPlan I.leftPlan_le I.rightPlan_le

abbrev rows := OrderedFaceBoundaryRows.rows I.leftScheme I.rightScheme I.shared
  R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows

def leftFace : ExactSemanticFace I.leftRows I.rows :=
  OrderedFaceBoundarySemantics.leftFace I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows

def rightFace : ExactSemanticFace I.rightRows I.rows :=
  OrderedFaceBoundarySemantics.rightFace I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows I.compatible

theorem consistent : I.rows.IsConsistent :=
  OrderedFaceBoundarySemantics.consistent I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows I.compatible
    (PointImageSemantics.consistent _ _ _ _ I.left.consistent)
    (PointImageSemantics.consistent _ _ _ _ I.right.consistent)

theorem coded : I.rows.IsCoded :=
  OrderedFaceBoundarySemantics.coded I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le I.leftRows I.rightRows
    (PointImageSemantics.coded _ _ _ _ I.left.rows_coded)
    (PointImageSemantics.coded _ _ _ _ I.right.rows_coded)

theorem left_order : StrictMono I.leftFace.map :=
  OrderedFaceBoundary.left_order I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le

theorem right_order : StrictMono I.rightFace.map :=
  OrderedFaceBoundary.right_order I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le

/-- A complete target vector is lawful precisely when both literal inputs are. -/
theorem respects_iff (p : Cell I.boundary → ExtOrd) :
    RespectsSemantics I.rows p ↔
      RespectsSemantics I.left.rows (p ∘ I.leftFace.map) ∧
      RespectsSemantics I.right.rows (p ∘ I.rightFace.map) := by
  rw [OrderedFaceBoundarySemantics.respects_iff _ _ _ _ _ _ _ _ _ I.compatible]
  exact and_congr
    (PointImageSemantics.respects_iff _ _ _ _ _)
    (PointImageSemantics.respects_iff _ _ _ _ _)

def paste (p : Cell I.left.scheme → ExtOrd) (q : Cell I.right.scheme → ExtOrd) :
    Cell I.boundary → ExtOrd :=
  OrderedFaceBoundarySemantics.paste I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le p q

theorem paste_pred {r : ExtOrd → Prop} {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : ∀ d, r (p d)) (hq : ∀ d, r (q d)) (d : Cell I.boundary) : r (I.paste p q d) :=
  ProfileFaceUnion.paste_pred I.shared.g hp hq ((OrderedFaceBoundary.enumeration _ _ I.shared).symm d)

theorem paste_rel {r : ExtOrd → ExtOrd → Prop}
    {p p' : Cell I.left.scheme → ExtOrd} {q q' : Cell I.right.scheme → ExtOrd}
    (hp : ∀ d, r (p d) (p' d)) (hq : ∀ d, r (q d) (q' d)) (d : Cell I.boundary) :
    r (I.paste p q d) (I.paste p' q' d) := ProfileFaceUnion.paste_rel I.shared.g hp hq ((OrderedFaceBoundary.enumeration _ _ I.shared).symm d)

theorem paste_left (p : Cell I.left.scheme → ExtOrd) (q : Cell I.right.scheme → ExtOrd)
    (d : Cell I.left.scheme) : I.paste p q (I.leftFace.map d) = p d :=
  OrderedFaceBoundarySemantics.paste_left I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le p q d

theorem paste_right (p : Cell I.left.scheme → ExtOrd) (q : Cell I.right.scheme → ExtOrd)
    (h : ∀ i, p (I.shared.f i) = q (I.shared.g i)) (d : Cell I.right.scheme) :
    I.paste p q (I.rightFace.map d) = q d :=
  OrderedFaceBoundarySemantics.paste_right I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le p q h d

/-- The selected inherited display needs agreement only on the literal common face. -/
theorem paste_respects {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
    (h : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    RespectsSemantics I.rows (I.paste p q) := by
  apply (I.respects_iff _).mpr
  constructor
  · have he : I.paste p q ∘ I.leftFace.map = p := funext (I.paste_left p q)
    exact he.symm ▸ hp
  · have he : I.paste p q ∘ I.rightFace.map = q := funext (I.paste_right p q h)
    exact he.symm ▸ hq

/-- The boundary contains exactly the two placed input faces. -/
theorem covered (d : Cell I.boundary) :
    (∃ c, I.leftFace.map c = d) ∨ (∃ c, I.rightFace.map c = d) :=
  OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared
    R I.isPlan I.leftPlan_le I.rightPlan_le d

/-- Properly placed inputs have no full-scope boundary owner. -/
theorem proper (hB : B ⊂ A) (hC : C ⊂ A) (d : Cell I.boundary) : I.boundary.scope d ≠ A := by
  rcases I.covered d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · rw [CellScheme.scope, I.leftFace.index]
    exact fun h => hB.not_ge (h ▸ I.leftScheme.scope_subset d)
  · rw [CellScheme.scope, I.rightFace.index]
    exact fun h => hC.not_ge (h ▸ I.rightScheme.scope_subset d)

/-- Paste two lawful lower sections. Their cutoffs may be nominal or reduced
by arity, provided they select exactly the cells through the target grade. -/
theorem paste_respects_below {j i k : ℕ} {p : Cell I.left.scheme → ExtOrd}
    {q : Cell I.right.scheme → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, i) (fun d => p d.1))
    (hq : RespectsSemanticsBelow I.right.rows (Finset.univ, k) (fun d => q d.1))
    (hs : ∀ d, p (I.shared.f d) = q (I.shared.g d))
    (hi : ∀ d, I.left.scheme.grade d ≤ i ↔ I.left.scheme.grade d ≤ j)
    (hk : ∀ d, I.right.scheme.grade d ≤ k ↔ I.right.scheme.grade d ≤ j) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => I.paste p q d.1) := by
  let u (d : Cell I.left.scheme) := if I.left.scheme.grade d ≤ j then p d else ⊥
  let v (d : Cell I.right.scheme) := if I.right.scheme.grade d ≤ j then q d else ⊥
  have hu : RespectsSemantics I.left.rows u := by
    convert hp.zeroAbove using 1
    funext d
    simp only [u, CellScheme.zeroAbove_apply, hi d]
  have hv : RespectsSemantics I.right.rows v := by
    convert hq.zeroAbove using 1
    funext d
    simp only [v, CellScheme.zeroAbove_apply, hk d]
  have hs' (d) : u (I.shared.f d) = v (I.shared.g d) := by
    have h : I.left.scheme.grade (I.shared.f d) = I.right.scheme.grade (I.shared.g d) :=
      congrArg Prod.snd (I.shared.shared d)
    simp only [u, v, h, hs]
  convert (I.paste_respects hu hv hs').toBelow (A, j) using 1
  funext d
  have hd : I.boundary.grade d.1 ≤ j := d.2.2
  rcases I.covered d.1 with ⟨c, hc⟩ | ⟨c, hc⟩
  · change Cell I.left.scheme at c
    rw [← hc, I.paste_left, I.paste_left]
    exact (if_pos ((congrArg Prod.snd (I.leftFace.index c)).ge.trans (hc ▸ hd))).symm
  · change Cell I.right.scheme at c
    rw [← hc, I.paste_right _ _ hs, I.paste_right _ _ hs']
    exact (if_pos ((congrArg Prod.snd (I.rightFace.index c)).ge.trans (hc ▸ hd))).symm

theorem left_mem {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) (hB : J.1 ⊆ B) :
    J ∈ Plan.gradedPlan I.leftScheme.plan := by
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hJ
  refine Plan.mem_gradedPlan.mpr ⟨?_, hp, hc⟩
  change J.1 ∈ I.left.scheme.plan.image (Finset.image I.placeLeft)
  rw [← I.planLeft]
  exact Finset.mem_inter.mpr ⟨hm, Finset.mem_powerset.mpr hB⟩

theorem right_mem {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) (hC : J.1 ⊆ C) :
    J ∈ Plan.gradedPlan I.rightScheme.plan := by
  obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hJ
  refine Plan.mem_gradedPlan.mpr ⟨?_, hp, hc⟩
  change J.1 ∈ I.right.scheme.plan.image (Finset.image I.placeRight)
  rw [← I.planRight]
  exact Finset.mem_inter.mpr ⟨hm, Finset.mem_powerset.mpr hC⟩

/-- Exactly the old point scopes are occupied; no mixed owner is hidden in this boundary. -/
theorem occupied_iff {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan R) :
    (∃ d, I.boundary.cell d = J) ↔ J.1 ⊆ B ∨ J.1 ⊆ C := by
  constructor
  · rintro ⟨d, rfl⟩
    rcases I.covered d with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · exact Or.inl (by
        rw [I.leftFace.index]
        exact I.leftScheme.scope_subset d)
    · exact Or.inr (by
        rw [I.rightFace.index]
        exact I.rightScheme.scope_subset d)
  · intro h
    apply OrderedFaceBoundary.complete_on_input I.leftScheme I.rightScheme I.shared
      R I.isPlan I.leftPlan_le I.rightPlan_le
      (pointImage_complete _ _ _ I.left.complete)
      (pointImage_complete _ _ _ I.right.complete)
    exact h.imp (I.left_mem hJ) (I.right_mem hJ)

include I in
theorem left_card : B.card = nL := by rw [← I.imageLeft, Finset.card_image_of_injective _ I.placeLeft.injective]; simp

include I in
theorem right_card : C.card = nR := by rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective]; simp

section Installed

variable {D : CellScheme A} {sem : Semantics D}
  (L : ExactSemanticFace I.leftRows sem) (G : ExactSemanticFace I.rightRows sem)

include I L G in
theorem installed_lift {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) : CappedLift sem h := by
  rcases hv with hb | hc
  · exact L.lift hb (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact G.lift hc (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

end Installed

theorem grade_le (d : Cell I.boundary) : I.boundary.grade d ≤ max nL nR := by
  rcases I.covered d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have h : I.left.scheme.grade d ≤ nL := by
      simpa using (I.left.scheme.grade_le_card_scope d).trans (Finset.card_le_univ _)
    exact (congrArg Prod.snd (I.leftFace.index d)).le.trans (h.trans (le_max_left _ _))
  · have h : I.right.scheme.grade d ≤ nR := by
      simpa using (I.right.scheme.grade_le_card_scope d).trans (Finset.card_le_univ _)
    exact (congrArg Prod.snd (I.rightFace.index d)).le.trans (h.trans (le_max_right _ _))

end Input

end

end VaughtConjecture.Knight.WholeDonorBoundary
