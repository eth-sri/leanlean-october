/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPrivateFibre

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

open CappedDonor.Ref.LowRef

noncomputable section

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

/-- Release specialized to the actual common-root occurrences. -/
theorem release_root {j : ℕ} (hj : K ≤ j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) (hbot : γ ≠ ⊥) (he : γ < F.gap.eC hj v)
    (hshield : ∀ a : P.scheme.below (faceIndex F.root.A j), F.p a.1 ≠ ⊤ →
      v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) < γ) :
    ∃ v', RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧
      (∀ a : P.scheme.below (faceIndex F.root.A j),
        v' (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) =
          v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a))) ∧
      F.gap.eC hj v' = γ := by
  let T (d : Cell C.scheme) : Prop :=
    ∃ a : P.scheme.below (F.root.A, F.root.A.card), (F.root.face a).1 = d ∧ F.p a.1 = ⊤
  have ht : ∀ a : C.scheme.below (faceIndex F.root.B j), T a.1 → C.scheme.grade a.1 ≤ K := by
    rintro a ⟨b, hb, ht⟩
    rw [← hb, ← F.root.grade]
    exact F.top_grade b.1 ht
  have hgap : ∀ (a : C.scheme.below (faceIndex F.root.B K))
      (ha : GradedLe (C.scheme.cell a.1) (C.scheme.cell F.gap.c)),
      T a.1 → F.gap.h < C.rows.E F.gap.c ⟨a.1, ha⟩ := by
    rintro a ha ⟨b, hb, ht⟩
    have heq : (⟨a.1, ha⟩ : F.gap.Dom) = ⟨(F.root.face b).1,
        by lia⟩ := Subtype.ext hb.symm
    rw [heq]
    exact F.root_gap b ht
  have hs : ∀ a : C.scheme.below (faceIndex F.root.B j), ¬ T a.1 →
      v (CellScheme.below.mono (faceIndex_le F.root.B j) a) < γ := by
    intro a ha
    have hn : F.p ((F.root.faceAt j).symm a).1 ≠ ⊤ := by
      intro ht
      apply ha
      refine ⟨F.root.fullP ((F.root.faceAt j).symm a), ?_, ht⟩
      exact congrArg Subtype.val ((F.root.faceAt j).apply_symm_apply a)
    grind
  obtain ⟨v', hv', hface, hcap, -, -, he'⟩ := F.gap.exists_release hj hv hγ hbot he
    F.root.B_mem F.root_sub T ht hgap hs
  exact ⟨v', hv', hcap, by tauto, he'⟩

/-- The active-grade donor fibre constructs the released private vector. -/
theorem donor_lift {j : ℕ} {S : State P C}
    (hS : F.Admissible j S) {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧ S.CapEq γ S' := by
  obtain ⟨v, hQ, hvcap⟩ := hS.toSource.install_donor F hu hγ hag
  have hface0 := hQ.replaced_shared_at F
  refine F.finish_replacement hS hγ hQ hag hvcap (ok := fun T => T.lowerP j = u)
    (S.replace_lowerP _ _ _) ?_
  intro hj hpos hnon htop hfront
  obtain ⟨v', hv', hv'cap, hface', he'⟩ := F.release_root hj
    (by simpa only [State.replace_lowerC] using hQ.lawfulC) hγ
    (ne_bot_of_gt (hpos.trans_le (min_le_right _ _))) hfront (fun a ha => by
      rw [← hface0]
      exact (hnon _ ha).trans_le (min_le_right _ _))
  refine ⟨S.replace u v' (min S.b γ),
    F.admissible_of_prescribed_tops hj
      (hS.toSource.replace F hu hv' _ (fun a => (hface0 a).trans (hface' a).symm))
      (hS.clip_visible F hγ) ?_, S.replace_lowerP _ _ _,
    S.replace_caps hag (fun d => (hv'cap d).trans (hvcap d)) (clipped_cutoff_cap _ _)⟩
  intro d hd
  rw [he', max_eq_right (min_le_right _ _)]
  exact le_of_capAgree_of_le (hag d).symm (htop d.1 hd)

end

end VaughtConjecture.Knight.LowOnly.Family
