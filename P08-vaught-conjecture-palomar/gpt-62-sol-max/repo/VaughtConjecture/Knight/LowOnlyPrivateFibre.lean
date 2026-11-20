/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyFamily

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

open CappedDonor.Ref.LowRef

noncomputable section

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

include F in
theorem cap_visible {j : ℕ} (hj : K ≤ j) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) : SelfVis K γ := hγ.mono (le_min hj F.gap.K_le)

theorem top_present {j : ℕ} (hj : K ≤ j) {d : Cell P.scheme} (hd : F.p d = ⊤) :
    GradedLe (P.scheme.cell d) (effC n j) :=
  ⟨Finset.subset_univ _, le_min ((F.top_grade d hd).trans hj) (gradeC_le d)⟩

theorem Source.replaced_shared_at {j : ℕ} {S : State P C}
    {u : P.scheme.below (effC n j) → ExtOrd} {v : C.scheme.below (effC n j) → ExtOrd}
    {b : ExtOrd} (hQ : F.Source j (S.replace u v b))
    (a : P.scheme.below (faceIndex F.root.A j)) :
    u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
      v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) := by
  have h := F.root.shared_at hQ.shared a
  change (S.replace u v b).lowerP j (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
    (S.replace u v b).lowerC j (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) at h
  simpa only [State.replace_lowerP, State.replace_lowerC] using h

theorem Admissible.clip_visible {j : ℕ} {S : State P C} (hS : F.Admissible j S)
    {γ : ExtOrd} (hγ : SelfVis (effC n j).2 γ) : SelfVis (min j K) (min S.b γ) :=
  selfVis_min hS.cutoff (hγ.mono
    (le_min (min_le_left _ _) ((min_le_right _ _).trans F.gap.K_le)))

abbrev floor {j : ℕ} (hj : K ≤ j) (S : State P C) : ExtOrd :=
  max S.b (F.gap.eC hj (S.lowerC j))

theorem floor_cap {j : ℕ} (hj : K ≤ j) {S Q : State P C} {γ : ExtOrd}
    (hγ : SelfVis K γ) (hcap : S.CapEq γ Q) : min (F.floor hj Q) γ = min (F.floor hj S) γ :=
  floor_min hcap.2.2 (F.frontier_cap hj hγ (fun d => hcap.2.1 d.1))

/-- No repair is needed unless activation puts the new floor strictly above the cap. -/
theorem admissible_of_floor_le {j : ℕ} {S Q : State P C} {γ : ExtOrd}
    (hS : F.Admissible j S) (hQ : F.Source j Q) (hγ : SelfVis (effC n j).2 γ)
    (hcap : S.CapEq γ Q) (hb : Q.b = min S.b γ)
    (hf : ∀ (hj : K ≤ j), F.maximum Q < Q.b → F.floor hj Q ≤ γ) : F.Admissible j Q := by
  refine ⟨hQ, hb.symm ▸ hS.clip_visible F hγ, fun hj hm d hd => ?_⟩
  have hmold := (clipped_activation hcap.1 (hb ▸ hm)).2.2
  calc
    F.floor hj Q = min (F.floor hj Q) γ := (min_eq_left (hf hj hm)).symm
    _ = min (F.floor hj S) γ := F.floor_cap hj (F.cap_visible hj hγ) hcap
    _ ≤ min (S.u d) γ := min_le_min_right _ (hS.low hj hmold d hd)
    _ = min (Q.u d) γ := (hcap.1 d).symm
    _ ≤ Q.u d := min_le_left _ _

/-- Only an activated replacement whose frontier exceeds the cap needs further work. -/
theorem finish_replacement {j : ℕ} {S : State P C} {γ : ExtOrd}
    {u : P.scheme.below (effC n j) → ExtOrd} {v : C.scheme.below (effC n j) → ExtOrd}
    (hS : F.Admissible j S) (hγ : SelfVis (effC n j).2 γ)
    (hQ : F.Source j (S.replace u v (min S.b γ)))
    (hu : ∀ d, min (u d) γ = min (S.lowerP j d) γ)
    (hv : ∀ d, min (v d) γ = min (S.lowerC j d) γ)
    {ok : State P C → Prop} (hok : ok (S.replace u v (min S.b γ)))
    (repair : ∀ (hj : K ≤ j), ⊥ < min S.b γ →
      (∀ d, F.p d.1 ≠ ⊤ → u d < min S.b γ) → (∀ d, F.p d = ⊤ → γ ≤ S.u d) →
      γ < F.gap.eC hj v → ∃ T, F.Admissible j T ∧ ok T ∧ S.CapEq γ T) :
    ∃ T, F.Admissible j T ∧ ok T ∧ S.CapEq γ T := by
  let Q := S.replace u v (min S.b γ)
  have hcap : S.CapEq γ Q := S.replace_caps hu hv (clipped_cutoff_cap _ _)
  by_cases h : ∃ hj : K ≤ j, F.maximum Q < Q.b ∧ γ < F.floor hj Q
  · obtain ⟨hj, hm, he⟩ := h
    have hmold := (clipped_activation hcap.1 hm).2.2
    have hγfloor : γ ≤ F.floor hj S := min_eq_right_iff.mp
      ((F.floor_cap hj (F.cap_visible hj hγ) hcap).symm.trans (min_eq_right he.le))
    refine repair hj (bot_le.trans_lt hm) (fun d hd => ?_)
      (fun d hd => hγfloor.trans (hS.low hj hmold d hd)) ?_
    · have h := (le_nonTopMax Q.u hd).trans_lt hm
      simpa [Q, State.replace, CellScheme.complete_present] using h
    · change γ < max (min S.b γ) (F.gap.eC hj ((S.replace u v _).lowerC j)) at he
      rw [State.replace_lowerC] at he
      exact (lt_max_iff.mp he).resolve_left (not_lt_of_ge (min_le_right _ _))
  · exact ⟨Q, F.admissible_of_floor_le hS hQ hγ hcap rfl
      (fun hj hm => le_of_not_gt fun he => h ⟨hj, hm, he⟩), hok, hcap⟩

theorem admissible_of_prescribed_tops {j : ℕ} (hj : K ≤ j) {S : State P C}
    {u : P.scheme.below (effC n j) → ExtOrd} {v : C.scheme.below (effC n j) → ExtOrd}
    {b : ExtOrd} (hQ : F.Source j (S.replace u v b)) (hb : SelfVis (min j K) b)
    (htop : ∀ d, F.p d.1 = ⊤ → max b (F.gap.eC hj v) ≤ u d) :
    F.Admissible j (S.replace u v b) := by
  refine ⟨hQ, hb, fun _ _ d hd => ?_⟩
  change max b (F.gap.eC hj ((S.replace u v b).lowerC j)) ≤ CellScheme.complete S.u u d
  rw [State.replace_lowerC, CellScheme.complete_present S.u u ⟨d, F.top_present hj hd⟩]
  exact htop _ hd

/-- A private prescription may raise donor tops while preserving their cap. -/
theorem private_lift {j : ℕ} {S : State P C}
    (hS : F.Admissible j S) {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧ S.CapEq γ S' := by
  obtain ⟨u, hQ, hucap⟩ := hS.toSource.install_private F hv hγ hag
  have hface0 := hQ.replaced_shared_at F
  refine F.finish_replacement hS hγ hQ hucap hag (ok := fun T => T.lowerC j = v)
    (S.replace_lowerC _ _ _) ?_
  intro hj hpos hnon htop hfront
  have hbvis := hS.clip_visible F hγ
  have htopγ (d : P.scheme.below (effC n j)) (hd : F.p d.1 = ⊤) : γ ≤ u d :=
    le_of_capAgree_of_le (hucap d).symm (htop d.1 hd)
  have hRD : RetargetData (p := F.p) (K := K) u (min S.b γ)
      (max (min S.b γ) (F.gap.eC hj v)) :=
    ⟨by simpa only [State.replace_lowerP] using hQ.lawfulP,
      (by simpa only [min_eq_right hj] using hbvis), hpos, hnon,
      (fun d hd => (min_le_right _ _).trans (htopγ d hd)),
      TopSupport.selfVis_max_of (by simpa only [min_eq_right hj] using hbvis)
        (F.gap.e_selfVis (F.gap.lowD_respects hj hv)), le_max_left _ _⟩
  obtain ⟨u', hu', hnon', htop', hface⟩ := hRD.exists_retarget_restore
    F.p_lawful hj F.top_grade
    F.root.A_mem ((F.root.respects_iff _).mp (hv.mono (faceIndex_le F.root.B j)))
    (fun a _ => (hface0 a).symm)
    (fun a ha => max_le
      ((min_le_right _ _).trans
        ((htopγ (CellScheme.below.mono (faceIndex_le F.root.A j) a) ha).trans_eq (hface0 a)))
      (F.frontier_le_root hj hv a ha))
  have hcap' : ∀ d, min (u' d) γ = min (S.lowerP j d) γ := by
    intro d
    by_cases hd : F.p d.1 = ⊤
    · change min (u' d) γ = min (S.u d.1) γ
      rw [min_eq_right ((hfront.le.trans (le_max_right _ _)).trans (htop' d hd)),
        min_eq_right (htop d.1 hd)]
    · rw [hnon' d hd, hucap d]
  exact ⟨S.replace u' v (min S.b γ),
    F.admissible_of_prescribed_tops hj (hS.toSource.replace F hu' hv _ hface) hbvis htop',
    S.replace_lowerC _ _ _, S.replace_caps hcap' hag (clipped_cutoff_cap _ _)⟩

end

end VaughtConjecture.Knight.LowOnly.Family
