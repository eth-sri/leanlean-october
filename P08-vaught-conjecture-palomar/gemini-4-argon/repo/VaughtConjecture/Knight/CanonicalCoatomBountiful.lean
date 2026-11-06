/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSections
public import VaughtConjecture.Knight.CanonicalLowerLift
public import VaughtConjecture.Knight.CanonicalProperDomain
public import VaughtConjecture.Knight.EffectiveGradeLifting
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.WitnessSplice

/-! # Bountifulness of the fixed canonical two-grade coatom carrier

The inputs are old proper-face lifting, old grade-one/two completeness, and
the two-face plan geometry. No completion, locality, serving controller, or
lifting theorem for the output is supplied. Nominal higher grades are handled
at the actual grade ceiling, retaining their original permitted caps.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalCoatomBountiful
open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift CoatomBoundaryExtension AmalgamationPlan GradeTailRestoration

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 2 ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

/-- The old proper-target clauses, including equality of indices. This is
supplied by the two inherited schemes, not by prospective output bountifulness. -/
def OldLifts : Prop :=
  ∀ I J, I ∈ Plan.gradedPlan D.plan → J ∈ Plan.gradedPlan D.plan → J.1 ≠ A →
    (h : GradedLe I J) → CappedLift sem h

variable (hold : OldLifts sem)

include hold in
private theorem overlap_lift {L R : Finset ι} (hR : R ∈ D.plan) (hRA : R ≠ A)
    (hO : L ∩ R ∈ D.plan) {n : ℕ} (hn : 0 < n) (hnR : n ≤ R.card) :
    CappedLift sem (target_le_right (U := (L, n)) (V := (R, n))) := by
  by_cases hne : (L ∩ R).Nonempty
  · exact hold _ _ (target_mem_gradedPlan hO hn hn hne)
      (Plan.mem_gradedPlan.mpr ⟨hR, hn, hnR⟩) hRA target_le_right
  · let := target_empty (D := D) (U := (L, n)) (V := (R, n))
      (Finset.not_nonempty_iff_eq_empty.mp hne)
    exact lift_empty target_le_right

local notation "Tgt" => CanonicalMixedAmbient.target sem 1 (by decide) (by omega) 2 (by decide) hA
local notation "Rws" => rows sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)
local notation "OTgt" => oldTarget sem 1 (by decide) (by omega) hproper 2 hg (by decide) hA (by decide)

include hold in
/-- Complete the full-index same-grade pair when the original face lies
on the designated left input. All numerical inputs remain arbitrary. -/
private theorem full_lift_left {L R C : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ d : Cell D, D.scope d ⊆ L ∨ D.scope d ⊆ R)
    (hC : C ∈ D.plan) (hCA : C ≠ A) (hCL : C ⊆ L)
    (hfull₁ : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    (hfull₂ : 2 ≤ C.card → ∃ c : D.below (C, 2), D.cell c.1 = (C, 2))
    {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) (hnC : n ≤ C.card)
    (h : GradedLe (C, n) (A, n)) :
    CappedLift Rws h := by
  have hCn : (C, n) ∈ Plan.gradedPlan D.plan := Plan.mem_gradedPlan.mpr ⟨hC, hn, hnC⟩
  have hC1 : (C, 1) ∈ Plan.gradedPlan D.plan :=
    Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 1), (Nat.one_le_of_lt hn).trans hnC⟩
  have hCnot : ¬ A ⊆ C := fun ha => hCA (Finset.Subset.antisymm h.1 ha)
  have cover₂ (d : Cell D) : GradedLe (D.cell d) (L, 2) ∨ GradedLe (D.cell d) (R, 2) :=
    (hcover d).imp (fun hd => ⟨hd, hg d⟩) (fun hd => ⟨hd, hg d⟩)
  have cover₁ (d : Cell D) (hd : D.grade d ≤ 1) :
      GradedLe (D.cell d) (L, 1) ∨ GradedLe (D.cell d) (R, 1) :=
    (hcover d).imp (fun hs => ⟨hs, hd⟩) (fun hs => ⟨hs, hd⟩)
  have left₂ : CappedLift sem (show GradedLe (C, n) (L, 2) from ⟨hCL, hn2⟩) :=
    hold _ _ hCn (Plan.mem_gradedPlan.mpr ⟨hL, (by decide : 0 < 2), hLc⟩) hLA ⟨hCL, hn2⟩
  have left₁ : CappedLift sem (show GradedLe (C, 1) (L, 1) from ⟨hCL, le_rfl⟩) :=
    hold (C, 1) (L, 1) hC1 (Plan.mem_gradedPlan.mpr
      ⟨hL, (by decide : 0 < 1), (by decide : 1 ≤ 2).trans hLc⟩) hLA ⟨hCL, le_rfl⟩
  have right₂ := overlap_lift sem hold hR hRA hO (by decide : 0 < 2) hRc
  have right₁ := overlap_lift sem hold hR hRA hO (by decide : 0 < 1) (by omega)
  have inter (m : ℕ) (d : Cell D) (hl : GradedLe (D.cell d) (L, m))
      (hr : GradedLe (D.cell d) (R, m)) :
      GradedLe (D.cell d) (overlapTarget (L, m) (R, m)) := below_target_iff d |>.mpr ⟨hl, hr⟩
  have lift₁ {p₁ : D.below (C, 1) → ExtOrd} (hp₁ : RespectsSemanticsBelow sem (C, 1) p₁)
      {q₁ : (scheme sem 1 (by decide) (by omega) 2 (by decide) hA).below (A, 1) → ExtOrd}
      (hq₁ : RespectsSemanticsBelow Rws (A, 1) q₁)
      {M : ExtOrd} (hM : SelfVis 1 M) (hMb : M ≠ ⊥)
      (hag₁ : ∀ e : D.below (C, 1), min (p₁ e) M =
        min (q₁ (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2)) M) :
      ∃ r : (scheme sem 1 (by decide) (by omega) 2 (by decide) hA).below (A, 1) → ExtOrd,
        RespectsSemanticsBelow Rws (A, 1) r ∧
        (∀ e : D.below (C, 1),
          r (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA e.1 e.2.2) = p₁ e) ∧
        ∀ d, min (r d) M = min (q₁ d) M := by
    let eC := GradeCutBoundary.belowEquiv D 1 (C, 1) le_rfl
    let eA := CanonicalLowerDomain.equiv sem 1 (by decide) (by omega) 2 (by decide) hA (by decide) (A, 1) le_rfl
    obtain ⟨c, hc⟩ := hfull₁
    have hf : ∃ c : (GradeCutBoundary.scheme D 1).below (C, 1),
        (GradeCutBoundary.scheme D 1).cell c.1 = (C, 1) :=
      ⟨eC.symm c, (congrArg (fun z : D.below (C, 1) => D.cell z.1) (eC.apply_symm_apply c)).trans hc⟩
    have hmap (a : (GradeCutBoundary.scheme D 1).below (C, 1)) :
        eA (CanonicalFieldOwnerLift.oldTarget (GradeCutBoundary.rows D 1 sem) 1 (Cell D)
          (GradeCutBoundary.toCell D 1) (by decide) (by omega) (GradeCutBoundary.proper D 1 hproper)
          (GradeCutBoundary.grade_bound D 1) a.1) =
        CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA (eC a).1 (eC a).2.2 := by
      apply Subtype.ext
      change oldCell sem 1 (by decide) (by omega) 2 (by decide) hA
        (GradeCutLayerCarrier.embed D (CanonicalGradeCutSections.Profiles sem 1) 1 (by decide) (by omega)
          (SourceLayerCarrier.toCell (GradeCutBoundary.scheme D 1)
            (CanonicalGradeCutSections.Profiles sem 1) 1 (by decide) (by omega) (.inl a.1))) = _
      rw [GradeCutLayerCarrier.embed_toCell]; rfl
    obtain ⟨r, hr, hread, hcap⟩ := CanonicalGradeOneLift.exists_positive_lift
      (GradeCutBoundary.rows D 1 sem) (Cell D) (GradeCutBoundary.toCell D 1) (by omega)
      (GradeCutBoundary.proper D 1 hproper) (GradeCutBoundary.grade_bound D 1)
      (GradeCutBoundary.toCell D 1).injective hf
      (GradeCutBoundary.pullback_respects D 1 sem le_rfl hp₁)
      (CanonicalLowerDomain.pullback_respects sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) le_rfl hq₁)
      hM hMb (fun a => by change min (p₁ (eC a)) M = min (q₁ (eA _)) M; rw [hmap]; exact hag₁ (eC a))
      (fun d => cover₁ (GradeCutBoundary.toCell D 1 d) (GradeCutBoundary.grade_bound D 1 d))
      ⟨hCL, le_rfl⟩ target_le_left target_le_right
      (fun d => inter 1 (GradeCutBoundary.toCell D 1 d))
      (CanonicalLowerLift.cut_lift (j := 1) _ le_rfl left₁)
      (CanonicalLowerLift.cut_lift (j := 1) _ le_rfl right₁) le_rfl le_rfl
    refine ⟨r ∘ eA.symm,
      (CanonicalLowerDomain.respects_iff sem 1 (by decide) (by omega) hproper 2 hg
        (by decide) hA (by decide) (A, 1) le_rfl r).mp hr, fun a => ?_, fun d => ?_⟩
    · have hm := hmap (eC.symm a)
      rw [eC.apply_symm_apply] at hm
      rw [← hm, Function.comp_apply, eA.symm_apply_apply, hread (eC.symm a)]
      exact congrArg p₁ (eC.apply_symm_apply a)
    · have he := hcap (eA.symm d)
      change min (r (eA.symm d)) M = min (q₁ (eA (eA.symm d))) M at he
      simpa only [Function.comp_apply, eA.apply_symm_apply] using he
  intro p q γ hp hq hγ hag
  let e := CanonicalProperDomain.equiv sem 1 (by decide) (by omega) 2 (by decide) hA
    (C, n) hCnot
  have hp' := CanonicalProperDomain.pullback_respects sem 1 (by decide) (by omega) hproper
    2 hg (by decide) hA (by decide) hCnot hp
  by_cases hγb : γ = ⊥
  · obtain ⟨b, hbread⟩ := section_left ⟨hCL, hn2⟩ target_le_left target_le_right (inter 2)
      left₂ right₂ (p ∘ e) hp'
    obtain ⟨r, hr, hold⟩ := CanonicalSections.exists_whole sem 1 (by decide) (by omega)
      hproper 2 hg (by decide) hA (by decide) (b.whole_respects cover₂)
    let hnA : GradedLe (A, n) (A, 2) := ⟨Finset.Subset.refl _, hn2⟩
    refine ⟨fun d => r (CellScheme.below.mono hnA d), hr.mono hnA,
      fun _ => by simp only [hγb, min_bot_right], fun d => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective d
    exact (hold a.1).trans (hbread a)
  rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
  · obtain ⟨r, hr, hread, hcap⟩ := lift₁ hp' hq hγ hγb (fun d => (hag (e d)).symm)
    refine ⟨r, hr, hcap, fun d => ?_⟩
    have hh := hread (e.symm d)
    change r (CellScheme.below.mono h (e (e.symm d))) = p (e (e.symm d)) at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp' (hfull₂ hnC)
    have hstep : ∃ (M : ExtOrd) (v : Tgt → ExtOrd),
        SelfVis 2 M ∧ M ≠ ⊥ ∧ γ ≤ M ∧
        (∀ a : D.below (C, 2), D.grade a.1 = 2 → p (e a) ≤ M) ∧
        RespectsSemanticsBelow Rws (A, 2) v ∧ (∀ d, v d ≤ M) ∧
        (∀ a : D.below (C, 2), v (OTgt a.1) = min (p (e a)) M) ∧
        ∀ d, min (v d) γ = min (q d) γ := by
      by_cases hpc : γ < p (e c)
      · have hc : D.grade c.1 = 2 := congrArg Prod.snd hci
        have hM : SelfVis 2 (p (e c)) := by simpa only [hc, Function.comp_apply] using (hp'.orderly c).symm
        have hcle : GradedLe (D.cell c.1) (C, 2) := by rw [hci]; exact GradedLe.refl _
        obtain ⟨u, hu, hread, hcap⟩ := exists_owner_capped_lift sem 1 (by decide) (by omega)
          hproper 2 hg (by decide) hA (by decide) c.1 hc (hp'.mono hcle) hq hγ hγb
          (fun a => (hag (e ⟨a.1, a.2.trans hcle⟩)).symm) hpc cover₂
          (hcle.trans ⟨hCL, le_rfl⟩) target_le_left target_le_right (inter 2)
          (by simpa only [hci] using left₂) right₂ le_rfl le_rfl
        refine ⟨p (e c), fun d => min (u d) (p (e c)), hM, (bot_le.trans_lt hpc).ne.symm,
          hpc.le, hmax, hu.cap hM, fun _ => min_le_right _ _, fun a => ?_, fun d => ?_⟩
        · have ha : u (OTgt a.1) = min (p (e a)) (p (e c)) := hread ⟨a.1, by rw [hci]; exact a.2⟩
          change min (u _) (p (e c)) = min (p (e a)) (p (e c))
          rw [ha, min_assoc, min_self]
        · change min (min (u d) (p (e c))) γ = min (q d) γ
          rw [min_assoc, min_eq_right hpc.le]
          exact hcap d
      · refine ⟨γ, fun d => min (q d) γ, hγ, hγb, le_rfl,
          fun a ha => (hmax a ha).trans (not_lt.mp hpc), hq.cap hγ, fun _ => min_le_right _ _,
          fun a => hag (e a), fun d => ?_⟩
        change min (min (q d) γ) γ = min (q d) γ
        rw [min_assoc, min_self]
    obtain ⟨M, v, hM, hMb, hγM, hdom, hv, hvle, hvold, hvcap⟩ := hstep
    let p₁ : D.below (C, 1) → ExtOrd := fun a => p (e ⟨a.1, a.2.1, a.2.2.trans (by decide : 1 ≤ 2)⟩)
    have hp₁ : RespectsSemanticsBelow sem (C, 1) p₁ :=
      hp'.mono (show GradedLe (C, 1) (C, 2) from ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩)
    let q₁ := fun d => v (lowerIncl (by decide : 1 ≤ 2) d)
    have hq₁ : RespectsSemanticsBelow Rws (A, 1) q₁ :=
      hv.mono (show GradedLe (A, 1) (A, 2) from ⟨Finset.Subset.refl _, (by decide : 1 ≤ 2)⟩)
    have hag₁ (a : D.below (C, 1)) : min (p₁ a) M =
        min (q₁ (CanonicalLowerLift.oldLow sem (by omega) 2 (by decide) hA a.1 a.2.2)) M := by
      change min (p₁ a) M = min (v (OTgt a.1)) M
      rw [hvold ⟨a.1, a.2.1, a.2.2.trans (by decide : 1 ≤ 2)⟩, min_assoc, min_self]
    obtain ⟨w, hw, hwold, hwcap⟩ := lift₁ hp₁ hq₁ (hM.mono (by decide)) hMb hag₁
    refine ⟨splice v w, splice_respects (by decide : 1 ≤ 2) hv hw (fun d _ => hvle d) hwcap,
      fun d => (cap_below (splice_cap (by decide : 1 ≤ 2) (u := v) (v := w) hwcap d) hγM).trans (hvcap d),
      fun d => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective d
    change splice v w (OTgt a.1) = p (e a)
    by_cases ha : D.grade a.1 ≤ 1
    · rw [splice_low v w _ (by rw [oldTarget_grade]; exact ha)]
      exact hwold ⟨a.1, a.2.1, ha⟩
    · rw [splice_high v w _ (by rw [oldTarget_grade]; exact ha), hvold]
      have ha₂ : D.grade a.1 = 2 := by have := hg a.1; omega
      exact min_eq_left (hdom a ha₂)

include hold in
/-- Whole-scheme bountifulness on the unchanged two-grade rows. The proper
input faces have room for grade two. Only their actual bountiful clauses,
grade-one/two owner incidences, and two-face geometry are premises.
This does not assert all-grade completeness, coding, or ordered installation. -/
theorem bountiful {L R : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
      ∃ d : Cell D, D.cell d = (C, i)) :
    (Rws).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (fun d => (data sem 1 (by decide) (by omega) hproper 2 hg
      (by decide) hA (by decide)).max_grade d) (by decide : 0 < 2)
  intro C B i hCi hBi hi hCB
  change (C, i) ∈ Plan.gradedPlan D.plan at hCi
  change (B, i) ∈ Plan.gradedPlan D.plan at hBi
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    have hc := Plan.mem_gradedPlan.mp hCi
    obtain ⟨c₁, he₁⟩ := hcomplete C hc.1 hCA 1 (by decide) (hc.2.1.trans_le hc.2.2) (by decide)
    have hfull₁ : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1) :=
      ⟨⟨c₁, by rw [he₁]; exact GradedLe.refl _⟩, he₁⟩
    have hfull₂ (hcard : 2 ≤ C.card) : ∃ c : D.below (C, 2), D.cell c.1 = (C, 2) := by
      obtain ⟨c, he⟩ := hcomplete C hc.1 hCA 2 (by decide) hcard le_rfl
      exact ⟨⟨c, by rw [he]; exact GradedLe.refl _⟩, he⟩
    have cells (d : Cell D) : D.scope d ⊆ L ∨ D.scope d ⊆ R :=
      hcover (D.scope d) (D.scope_mem_plan d) (hproper d)
    rcases hcover C hc.1 hCA with hl | hr
    · exact full_lift_left sem hA hproper hg hold hL hR hLA hRA hLc hRc hO cells
        hc.1 hCA hl hfull₁ hfull₂ hc.2.1 hi hc.2.2 ⟨hCB, le_rfl⟩
    · exact full_lift_left sem hA hproper hg hold hR hL hRA hLA hRc hLc
        (Finset.inter_comm L R ▸ hO) (fun d => (cells d).symm)
        hc.1 hCA hr hfull₁ hfull₂ hc.2.1 hi hc.2.2 ⟨hCB, le_rfl⟩
  · have hBnot : ¬ A ⊆ B := fun hb => hBA (Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hBi).1) hb)
    exact CanonicalProperDomain.lift sem 1 (by decide) (by omega) hproper 2 hg (by decide)
      hA (by decide) (I := (C, i)) (J := (B, i)) ⟨hCB, le_rfl⟩ hBnot
      (hold _ _ hCi hBi hBA ⟨hCB, le_rfl⟩)

