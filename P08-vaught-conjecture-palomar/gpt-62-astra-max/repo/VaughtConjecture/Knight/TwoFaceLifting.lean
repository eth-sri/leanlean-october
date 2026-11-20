/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.CappedLiftComposition

/-! # Lifting through either of two literal original faces -/

@[expose] public section
namespace VaughtConjecture.Knight.WholeDonorBoundary.Input
open AmalgamationPlan CoatomBoundaryExtension
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
  {m l r : ℕ} (I : Input A B C R m l r)

include I in
theorem card_left : B.card = l := by
  rw [← I.imageLeft, Finset.card_image_of_injective _ I.placeLeft.injective]; simp

include I in
theorem card_right : C.card = r := by
  rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective]; simp

variable {D : CellScheme A} {sem : Semantics D}
  (L : ExactSemanticFace I.leftRows sem) (H : ExactSemanticFace I.rightRows sem)

include L H in
theorem liftWithin {U V : Finset ι × ℕ} (hu : U ∈ Plan.gradedPlan R)
    (hv : V ∈ Plan.gradedPlan R) (h : GradedLe U V) (hs : V.1 ⊆ B ∨ V.1 ⊆ C) : CappedLift sem h := by
  by_cases he : U = V
  · subst V; exact lift_refl
  rcases hs with hb | hc
  · exact L.lift hb (I.left_mem hu (h.1.trans hb)) (I.left_mem hv hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact H.lift hc (I.right_mem hu (h.1.trans hc)) (I.right_mem hv hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

include L H in
theorem liftSubface {U T : Finset ι} {i j : ℕ} (ht : T ∈ R) (hf : T ⊆ B ∨ T ⊆ C)
    (hu : (U,i) ∈ Plan.gradedPlan R) (sub : U ⊆ T) (hT : T ⊆ A) (hij : i ≤ j)
    (next : i ≤ T.card → CappedLift sem (GradedLe.atGrade hT i)) :
    CappedLift sem (show GradedLe (U,i) (A,j) from ⟨sub.trans hT,hij⟩) := by
  obtain ⟨_, pos, bound⟩ := Plan.mem_gradedPlan.mp hu
  have hi := bound.trans (Finset.card_le_card sub)
  exact ((I.liftWithin (V := (T,i)) L H hu (Plan.mem_gradedPlan.mpr ⟨ht,pos,hi⟩) (GradedLe.atGrade sub i) hf).comp
    (next hi)).raise_target (h := sub.trans hT) hij

include L H in
/-- Lift first inside an original face, then from that face to the whole domain. -/
theorem liftViaFaces {B' C' : Finset ι} {j : ℕ}
    (hB : B ⊆ A) (hC : C ⊆ A) (cover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)
    (left : j ≤ l → CappedLift sem (show GradedLe (B,j) (A,j) from ⟨hB, le_rfl⟩))
    (right : j ≤ r → CappedLift sem (show GradedLe (C,j) (A,j) from ⟨hC, le_rfl⟩))
    (hs : (B',j) ∈ Plan.gradedPlan R) (ht : (C',j) ∈ Plan.gradedPlan R) (h : B' ⊆ C') :
    CappedLift sem (show GradedLe (B',j) (C',j) from ⟨h, le_rfl⟩) := by
  by_cases he : C' = A
  · subst C'
    by_cases he : B' = A
    · subst B'; exact lift_refl
    have mem {T} (hm : T ∈ R) (hsub : B' ⊆ T) : (T,j) ∈ Plan.gradedPlan R :=
      Plan.mem_gradedPlan.mpr ⟨hm, (Plan.mem_gradedPlan.mp hs).2.1,
        (Plan.mem_gradedPlan.mp hs).2.2.trans (Finset.card_le_card hsub)⟩
    rcases cover _ (Plan.mem_gradedPlan.mp hs).1 he with hb | hc
    · have hm := mem (I.leftPlan_le I.leftScheme.isPlan.domain_mem) hb
      exact (I.liftWithin L H hs hm ⟨hb, le_rfl⟩ (.inl (le_refl B))).comp
        (left ((Plan.mem_gradedPlan.mp hm).2.2.trans_eq I.card_left))
    · have hm := mem (I.rightPlan_le I.rightScheme.isPlan.domain_mem) hc
      exact (I.liftWithin L H hs hm ⟨hc, le_rfl⟩ (.inr (le_refl C))).comp
        (right ((Plan.mem_gradedPlan.mp hm).2.2.trans_eq I.card_right))
  · exact I.liftWithin L H hs ht ⟨h, le_rfl⟩ (cover _ (Plan.mem_gradedPlan.mp ht).1 he)
end VaughtConjecture.Knight.WholeDonorBoundary.Input
