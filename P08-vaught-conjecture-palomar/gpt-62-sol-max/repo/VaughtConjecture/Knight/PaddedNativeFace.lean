/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedFaceTransport

@[expose] public section

namespace VaughtConjecture.Knight.Padded

open Transform Value ExtOrd CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι} {K : Spec A} {n : ℕ} {S : SemScheme n}
  {e : Fin n ↪ ι} {he : Finset.univ.image e = B}

/-- Lifting data for an original face. A cutoff may be nominal or clipped at the arity,
provided it gives exactly the same original lower set. -/
structure NativeFace (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) K.boundaryRows)
    (cut : ℕ → ℕ) : Prop where
  le_cutoff : ∀ j, cut j ≤ j
  monotone : Monotone cut
  grade_cut : ∀ (d : Cell S.scheme) {j}, S.scheme.grade d ≤ j → S.scheme.grade d ≤ cut j
  fibre : ∀ {j}, 1 ≤ j → (∃ d : S.scheme.below (Finset.univ, cut j), S.scheme.grade d.1 = j) →
    NativeFibre K S (faceBoundary S G (le_cutoff j))

namespace NativeFace

variable {G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) K.boundaryRows}
  {cut : ℕ → ℕ} (F : NativeFace G cut) (hc : K.boundaryRows.IsConsistent)

private theorem base_lift : PaddedFaceLift.Lift S.rows K.baseRows
    (RelativeLadderLayer.prescribedAt K.boundary K.one ∘ faceBoundary S G (F.le_cutoff 1)) := by
  intro p q hp hq γ hγ hag
  by_cases h : ∃ d : S.scheme.below (Finset.univ, cut 1), S.scheme.grade d.1 = 1
  · letI : Fintype (K.context.Anchor 1) := K.anchorFinite 1
    exact RelativeLadderLayer.lift_fibre K.boundary K.boundaryRows K.one K.field K.proper
      (F.le_cutoff 1) _ K.context (F.fibre le_rfl h) (K.profile_visible le_rfl)
      K.profile_lawful (K.seed 1 le_rfl) hp hq hγ hag
  · exact ⟨q, hq, fun d => (h ⟨d, le_antisymm (d.2.2.trans (F.le_cutoff 1))
      (S.scheme.grade_pos d.1)⟩).elim, fun _ => rfl⟩

private theorem initial_lift : PaddedFaceLift.Lift S.rows (Initial.layer K hc).rows
    ((Initial.layer K hc).faceAt S G (F.le_cutoff 2)) :=
  (Initial.layer K hc).lift_fibre (F.le_cutoff 2) (by decide) (F.fibre (by decide))
    (PaddedFaceLift.restore_of_lower (J := (Finset.univ, cut 2)) (J₀ := (Finset.univ, cut 1))
      ⟨le_rfl, F.monotone (by decide : 1 ≤ 2)⟩ (F.le_cutoff 2)
      (fun d hd => ⟨d.2.1, F.grade_cut d.1 hd⟩)
      (fun d => (Initial.layer K hc).faceAt_grade G d.1 (d.2.2.trans (F.le_cutoff 2)))
      (Initial.lowerEquiv K) (Initial.lower_respects_iff K) (fun _ => rfl) F.base_lift)

private theorem step_lift {k : ℕ} (P : Layer K k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)
    (hlo : PaddedFaceLift.Lift S.rows P.rows (P.faceAt S G (F.le_cutoff k))) :
    PaddedFaceLift.Lift S.rows (successor P hk hnext).rows
      ((successor P hk hnext).faceAt S G (F.le_cutoff (k + 1))) := by
  let M := successor P hk hnext
  let hn : ¬ GradedLe (A, k + 1) (A, k) := fun h => Nat.not_succ_le_self k h.2
  intro p q
  exact M.lift_fibre (F.le_cutoff (k + 1)) (Nat.succ_pos _) (F.fibre (Nat.succ_pos _))
    (PaddedFaceLift.restore_of_lower (J := (Finset.univ, cut (k + 1))) (J₀ := (Finset.univ, cut k))
      (lo := P.faceAt S G (F.le_cutoff k))
      ⟨le_rfl, F.monotone (Nat.le_succ k)⟩ (F.le_cutoff (k + 1))
      (fun d hd => ⟨d.2.1, F.grade_cut d.1 hd⟩) (fun d => M.faceAt_grade G d.1 (d.2.2.trans (F.le_cutoff _)))
      (SourceLayerCarrier.inheritedEquiv _ _ _ _ _ _ hn)
      (SeparatedSourceLayerCarrier.respects_iff _ _ _ _ _ (P.separated (by omega))
        (StepRows.inherited_row P hk hnext) _ hn) (fun _ => rfl) hlo)

private theorem build_lift (t : ℕ) (ht : t + 2 ≤ A.card) :
    PaddedFaceLift.Lift S.rows (build (Initial.layer K hc) t ht).rows
      ((build (Initial.layer K hc) t ht).faceAt S G (F.le_cutoff (t + 2))) := by
  induction t with
  | zero => exact F.initial_lift hc
  | succ t ih =>
    exact F.step_lift (build (Initial.layer K hc) t (by omega)) (by omega) (by omega) (ih (by omega))

include F in
/-- All positive cutoffs are covered on the final carrier, not just the height of the build. -/
theorem capped_clause (hB : B ⊂ A) (t : ℕ) (ht : t + 2 ≤ A.card) {j : ℕ} (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    CappedLift (build (Initial.layer K hc) t ht).rows
      (show GradedLe (B, j) (A, j) from ⟨hB.subset, le_rfl⟩) := by
  have hcut (k : ℕ) (d : Cell S.scheme) : S.scheme.grade d ≤ cut k ↔ S.scheme.grade d ≤ k :=
    ⟨fun h => h.trans (F.le_cutoff k), F.grade_cut d⟩
  by_cases h₁ : j = 1
  · subst j
    exact (build (Initial.layer K hc) t ht).capped_base G hB (hcut 1) F.base_lift
  induction t with
  | zero =>
    obtain rfl : j = 2 := by omega
    exact (Initial.layer K hc).capped_face G hB (F.le_cutoff 2) (hcut 2) (F.initial_lift hc)
  | succ t ih =>
    by_cases h : j = t + 1 + 2
    · subst j
      exact (build (Initial.layer K hc) _ ht).capped_face G hB (F.le_cutoff _) (hcut _) (F.build_lift hc _ ht)
    · exact StepRows.lower_lift (build (Initial.layer K hc) t (by omega))
        (by omega) (by omega) _ (by omega) (ih (by omega) (by omega))

end NativeFace

end

end VaughtConjecture.Knight.Padded
