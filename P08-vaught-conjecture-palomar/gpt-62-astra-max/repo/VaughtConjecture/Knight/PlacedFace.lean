/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.CappedDonorReceiving

/-! # Placing a full native face at an arbitrary cutoff -/

@[expose] public section
namespace VaughtConjecture.Knight.PlacedFace
open CappedDonor CoatomBoundaryExtension
variable {ι : Type*} [DecidableEq ι] {A B : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {n : ℕ} {S : SemScheme n} {place : Fin n ↪ ι} {he : Finset.univ.image place = B}
  (G : ExactSemanticFace (PointImageSemantics.rows S.scheme place he S.rows) sem)
  {i j : ℕ} (lo : min j n ≤ i) (hi : i ≤ j)

/-- Whether one uses the nominal grade or clips it at the arity, the occurrences are identical. -/
noncomputable def equiv : S.Native i ≃ D.below (B,j) :=
  (show S.Native i ≃ (AmalgamatedBoundary.pointImage S.scheme place he).below (B,j) from {
    toFun := fun d => ⟨d.1, (Finset.image_subset_image d.2.1).trans he.subset, d.2.2.trans hi⟩
    invFun := fun d => ⟨d.1, Finset.subset_univ _, (le_min d.2.2 (gradeC_le d.1)).trans lo⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (G.belowEquiv _ (Finset.Subset.refl _))

theorem grade (d : S.Native i) : D.grade (equiv G lo hi d).1 = S.scheme.grade d.1 :=
  congrArg Prod.snd (G.index d.1)

theorem lawful (q : D.SectionAt (B,j)) : sem.Lawful q ↔ S.rows.Lawful (q ∘ equiv G lo hi) := by
  apply pullback_iff (equiv G lo hi)
  apply respects_iff_of_equiv _ (fun d => (grade G lo hi d).symm) _ _
  · intro d e
    change S.scheme.scope d.1 ⊆ S.scheme.scope e.1 ↔ (D.cell (G.map d.1)).1 ⊆ (D.cell (G.map e.1)).1
    rw [G.index d.1, G.index e.1]; exact (Finset.image_subset_image_iff place.injective).symm
  · exact fun c d _ => (G.row c.1 (PointImageSemantics.belowEquiv S.scheme place he c.1 d)).symm

noncomputable abbrev incl (sub : B ⊆ A) (d : S.Native i) :=
  CellScheme.below.mono (D := D) (GradedLe.atGrade sub j) (equiv G lo hi d)

theorem lift (sub : B ⊆ A)
    (supply : ∀ {p : S.Native i → ExtOrd} {q : D.SectionAt (A,j)} {γ},
      S.rows.Lawful p → sem.Lawful q → SelfVis j γ → CappedEq (q ∘ incl G lo hi sub) p γ →
      sem.FaceLift (incl G lo hi sub) p q γ) : CappedLift sem (GradedLe.atGrade sub j) := by
  intro p q γ hp hq hv ha
  obtain ⟨r, hr, hread, hcap⟩ := supply ((lawful G lo hi p).mp hp) hq hv (fun d => ha (equiv G lo hi d))
  refine ⟨r, hr, hcap, ?_⟩
  intro d; obtain ⟨x,rfl⟩ := (equiv G lo hi).surjective d; exact hread x
end VaughtConjecture.Knight.PlacedFace
