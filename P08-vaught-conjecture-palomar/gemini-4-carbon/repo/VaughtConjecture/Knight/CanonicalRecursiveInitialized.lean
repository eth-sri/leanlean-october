/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLifting
open Transform Value ExtOrd CoatomBoundaryExtension GradeCutBoundary
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ)

theorem lift_iff {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ k) :
    CappedLift (rows D k sem) h ↔ CappedLift sem h := by
  let eI := belowEquiv D k I (h.2.trans hJ)
  let eJ := belowEquiv D k J hJ
  have hm (d : (scheme D k).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  have hi (d : D.below I) :
      eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) := by
    apply eJ.injective
    rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
  constructor
  · intro hl p q γ hp hq hγ hag
    obtain ⟨r, hr, hc, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ
      (pullback_respects D k sem (h.2.trans hJ) hp)
      (pullback_respects D k sem hJ hq) hγ (fun d => hag (eI d))
    refine ⟨r ∘ eJ.symm, (respects_iff D k sem J hJ r).mp hr, ?_, ?_⟩
    · intro d
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc (eJ.symm d)
    · intro d
      rw [Function.comp_apply, hi, hread]
      exact congrArg p (eI.apply_symm_apply d)
  · intro hl p q γ hp hq hγ hag
    obtain ⟨r, hr, hc, hread⟩ := hl (p ∘ eI.symm) (q ∘ eJ.symm) γ
      ((respects_iff D k sem I (h.2.trans hJ) p).mp hp)
      ((respects_iff D k sem J hJ q).mp hq) hγ (fun d => by
        simpa only [Function.comp_apply, hi] using hag (eI.symm d))
    refine ⟨r ∘ eJ, pullback_respects D k sem hJ hr, ?_, ?_⟩
    · intro d
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hc (eJ d)
    · intro d
      rw [Function.comp_apply, hm, hread]
      exact congrArg p (eI.symm_apply_apply d)

end VaughtConjecture.Knight.GradeCutLifting

namespace VaughtConjecture.Knight.CanonicalRecursiveRecurrence
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

def ReadyAt (m : ℕ) (hm : m + 2 ≤ A.card) : Prop :=
  sem.IsConsistent ∧
    (GradeCutBoundary.rows (carrierAt sem m hm) (m + 2)
      (CanonicalRecursiveSemantics.rowsAt sem hp m hm)).IsBountiful

abbrev Ready (n : ℕ) (hm : n + 3 ≤ A.card) : Prop := ReadyAt sem hp (n + 1) hm

end
end VaughtConjecture.Knight.CanonicalRecursiveRecurrence

namespace VaughtConjecture.Knight.CanonicalRecursiveInitialized
open Transform Value ExtOrd SourcePrefixRows CoatomBoundaryExtension AmalgamationPlan
open CanonicalRecursiveContract CanonicalRecursiveSemantics CanonicalRecursiveRecurrence
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

section Step
variable (sem : Semantics D) (m : ℕ) (hA : m + 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)

private abbrev predState := stateAt sem hp m (Nat.le_of_succ_le hA)
private abbrev outRows := stepRows sem m hA hp (predState sem m hA hp)
private abbrev cut := GradeCutBoundary.scheme D (m + 3)
private abbrev cutRows := GradeCutBoundary.rows D (m + 3) sem
private abbrev occ := GradeCutBoundary.toCell D (m + 3)
private abbrev target := (stepCarrier sem m hA).below (A, m + 3)

private def botProfile : Profile sem m :=
  CanonicalRecursiveInventory.encode sem m (p := fun _ => ⊥)
    ((RespectsSemantics.bot sem).toBelow (A, m + 3)) (fun _ => bot_ne_top)

private def oldTarget (d : Cell (cut (D := D) m)) : target sem m hA :=
  ⟨stepBoundary sem m hA (occ (D := D) m d), by
    have he : (stepCarrier sem m hA).cell (stepBoundary sem m hA (occ (D := D) m d)) =
        D.cell (occ (D := D) m d) :=
      CanonicalRecursiveInventory.boundary_cell sem (m + 3) hA _
    rw [he]
    exact ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D _ d⟩⟩

private theorem oldTarget_cell (d : Cell (cut (D := D) m)) :
    (stepCarrier sem m hA).cell (oldTarget sem m hA d).1 = (cut (D := D) m).cell d :=
  CanonicalRecursiveInventory.boundary_cell sem (m + 3) hA _

private theorem exists_amb {q : target sem m hA → ExtOrd}
    (hq : RespectsSemanticsBelow (outRows sem m hA hp) (A, m + 3) q)
    (d : target sem m hA) (hd : (stepCarrier sem m hA).grade d.1 = m + 3)
    {γ : ExtOrd} (hγ : SelfVis (m + 3) γ) (_ : γ ≠ ⊥) (hactive : γ ≤ q d) :
    ∃ (a : Profile sem m) (τ : ExtOrd → ExtOrd),
      Witness (gTop (m + 3)) τ ∧ (∀ z, τ z ≤ γ) ∧
      ∀ x : target sem m hA,
        τ (source sem m hA hp (predState sem m hA hp) a x.1) = min (q x) γ := by
  let F := data sem m hA hp (predState sem m hA hp)
  obtain ⟨c, τ, _, hτ, hbound, _, hread⟩ := ScopedSourcePrefixAmbient.exists_active_source F
    (controller sem m hA (botProfile sem m)) hq d hd hγ hactive
  let a := member sem m hA hp c
  have ha : controller sem m hA a = c := (controllerEquiv sem m hA hp).apply_symm_apply c
  refine ⟨a, τ, hτ, hbound, fun x => ?_⟩
  change τ (F.profile (controller sem m hA a) x.1) = _
  rw [ha]
  exact hread x

private theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ m + 2)
    (hl : CappedLift (predState sem m hA hp).rows h) :
    CappedLift (outRows sem m hA hp) h := by
  have hJn : ¬ GradedLe (A, m + 3) J := fun he => by have := he.2; omega
  have hIn : ¬ GradedLe (A, m + 3) I := fun hi => hJn (hi.trans h)
  let eI := equiv sem m hA I hIn
  let eJ := equiv sem m hA J hJn
  have pull (B : Finset ι × ℕ) (hB : ¬ GradedLe (A, m + 3) B)
      (u : (stepCarrier sem m hA).below B → ExtOrd)
      (hu : RespectsSemanticsBelow (outRows sem m hA hp) B u) :
      RespectsSemanticsBelow (predState sem m hA hp).rows B (u ∘ equiv sem m hA B hB) := by
    apply (respects_iff sem m hA hp (predState sem m hA hp) B hB _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hu
  have hm (d : (predecessor sem m hA).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  intro p q γ hpr hqr hγ hag
  obtain ⟨r, hr, hcap, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ
    (pull I hIn p hpr) (pull J hJn q hqr) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (respects_iff sem m hA hp (predState sem m hA hp) J hJn r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have hd : eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) :=
      eJ.injective (by rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply])
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

private def faceEquiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ m + 3) :
    (cut (D := D) m).below J ≃ (stepCarrier sem m hA).below J :=
  (GradeCutBoundary.belowEquiv D (m + 3) J hj).trans
    (CanonicalRecursiveBoundaryTransport.properEquivAt sem (m + 1) hA J hJ)

private theorem faceEquiv_val (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ m + 3)
    (d : (cut (D := D) m).below J) :
    (faceEquiv sem m hA J hJ hj d).1 = (oldTarget sem m hA d.1).1 :=
  CanonicalRecursiveBoundaryTransport.properEquiv_valAt sem (m + 1) hA J hJ _

private theorem faceEquiv_cell (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (hj : J.2 ≤ m + 3)
    (d : (cut (D := D) m).below J) :
    (stepCarrier sem m hA).cell (faceEquiv sem m hA J hJ hj d).1 =
      (cut (D := D) m).cell d.1 := by
  rw [faceEquiv_val, oldTarget_cell]

private theorem lower_clause
    (hb : (GradeCutBoundary.rows (predecessor sem m hA) (m + 2)
      (predState sem m hA hp).rows).IsBountiful)
    {C : Finset ι} (hC : C ∈ D.plan) (hCc : m + 2 ≤ C.card) :
    CappedLift (outRows sem m hA hp)
      (show GradedLe (C, m + 2) (A, m + 2) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  apply lower_lift sem m hA hp _ le_rfl
  apply (GradeCutLifting.lift_iff (predState sem m hA hp).rows (m + 2) _ le_rfl).mp
  apply lift_of_bountiful hb
  · change (C, m + 2) ∈ Plan.gradedPlan (predecessor sem m hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩
  · change (A, m + 2) ∈ Plan.gradedPlan (predecessor sem m hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]
    exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, by omega, Nat.le_of_succ_le hA⟩

private theorem full_lift_step
    (hb : (GradeCutBoundary.rows (predecessor sem m hA) (m + 2)
      (predState sem m hA hp).rows).IsBountiful)
    {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A) (hCc : m + 3 ≤ C.card)
    (hfull : ∃ c : (cut (D := D) m).below (C, m + 3),
      (cut (D := D) m).cell c.1 = (C, m + 3))
    {U V O : Finset ι × ℕ}
    (hcover : ∀ d : Cell (cut (D := D) m),
      GradedLe ((cut (D := D) m).cell d) U ∨ GradedLe ((cut (D := D) m).cell d) V)
    (hCU : GradedLe (C, m + 3) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d : Cell (cut (D := D) m), GradedLe ((cut (D := D) m).cell d) U →
      GradedLe ((cut (D := D) m).cell d) V → GradedLe ((cut (D := D) m).cell d) O)
    (hleft : CappedLift (cutRows sem m) hCU) (hright : CappedLift (cutRows sem m) hOV)
    (hU : U.2 ≤ m + 3) (hV : V.2 ≤ m + 3) :
    CappedLift (outRows sem m hA hp)
      (show GradedLe (C, m + 3) (A, m + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  have hCnot : ¬ A ⊆ C := fun h => hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  let E := faceEquiv sem m hA (C, m + 3) hCnot le_rfl
  have hcl := lower_clause sem m hA hp hb hC (Nat.le_of_succ_le hCc)
  intro p q γ hpr hqr hγ hag
  have hp₀ : RespectsSemanticsBelow (cutRows sem m) (C, m + 3) (p ∘ E) :=
    GradeCutBoundary.pullback_respects D (m + 3) sem le_rfl
      (CanonicalRecursiveBoundaryTransport.pullback_respectsAt sem hp (m + 1) hA
        (C, m + 3) hCnot hpr)
  by_cases hγb : γ = ⊥
  · obtain ⟨b, hbread⟩ := CoatomBoundaryExtension.section_left
      hCU hOU hOV hinter hleft hright (p ∘ E) hp₀
    let F := GradeCutBoundary.belowEquiv D (m + 3) (A, m + 3) le_rfl
    have hu := (GradeCutBoundary.respects_iff D (m + 3) sem (A, m + 3) le_rfl _).mp
      ((b.whole_respects hcover).toBelow (A, m + 3))
    obtain ⟨r, hr, hread⟩ := CanonicalRecursiveTopSections.exists_sectionAt sem hp (m + 1) hA hu
    refine ⟨r, hr, fun _ => by simp only [hγb, min_bot_right], ?_⟩
    intro e
    obtain ⟨d, rfl⟩ := E.surjective e
    let dA : (cut (D := D) m).below (A, m + 3) :=
      ⟨d.1, d.2.1.trans (D.isPlan.subset_of_mem hC), d.2.2⟩
    have hd : CellScheme.below.mono
        (show GradedLe (C, m + 3) (A, m + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) =
        CanonicalRecursiveTopSections.boundaryTargetAt sem (m + 1) hA (F dA) :=
      Subtype.ext (faceEquiv_val sem m hA _ hCnot le_rfl d)
    rw [hd, hread]
    change b.whole hcover (F.symm (F dA)).1 = p (E d)
    rw [Equiv.symm_apply_apply]
    exact (b.whole_left hcover (CellScheme.below.mono hCU d)).trans
      ((b.value_left _).symm.trans (hbread d))
  by_cases hactive : ∃ d : (stepCarrier sem m hA).below (C, m + 3),
      (stepCarrier sem m hA).grade d.1 = m + 3 ∧ γ < p d
  · obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp₀ hfull
    let p₀ := p ∘ E
    let M := p₀ c
    have hpc : γ < M := by
      obtain ⟨d, hd, hpd⟩ := hactive
      obtain ⟨e, rfl⟩ := E.surjective d
      have he : (cut (D := D) m).grade e.1 = m + 3 := by
        change ((stepCarrier sem m hA).cell (E e).1).2 = m + 3 at hd
        rwa [faceEquiv_cell] at hd
      exact hpd.trans_le (hmax e he)
    have hc : (cut (D := D) m).grade c.1 = m + 3 := congrArg Prod.snd hci
    have hM : SelfVis (m + 3) M := by simpa only [hc] using (hp₀.orderly c).symm
    have hcle : GradedLe ((cut (D := D) m).cell c.1) (C, m + 3) := c.2
    have hag₀ (e : (cut (D := D) m).below (C, m + 3)) :
        min (p₀ e) γ = min (q (oldTarget sem m hA e.1)) γ := by
      have he : CellScheme.below.mono
          (show GradedLe (C, m + 3) (A, m + 3) from
            ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E e) = oldTarget sem m hA e.1 :=
        Subtype.ext (faceEquiv_val sem m hA _ hCnot le_rfl e)
      simpa only [p₀, Function.comp_apply, he] using (hag (E e)).symm
    have hl : CappedLift (cutRows sem m) (hcle.trans hCU) := by simpa only [hci] using hleft
    let Fd := data sem m hA hp (predState sem m hA hp)
    obtain ⟨u, hu, hread, hcap⟩ := CanonicalOwnerBoundary.exists_owner_capped_lift
      (occ (D := D) m).injective (GradeCutBoundary.grade_bound D (m + 3))
      (oldTarget sem m hA)
      (fun d => congrArg Prod.snd (oldTarget_cell sem m hA d))
      (source sem m hA hp (predState sem m hA hp))
      (fun b => Fd.profile_respects (controller sem m hA b))
      (fun b d => source_boundary sem m hA hp (predState sem m hA hp) b (occ (D := D) m d))
      (source_supported sem m hA hp (predState sem m hA hp))
      (source_agreement_all sem m hA hp (predState sem m hA hp))
      (exists_amb sem m hA hp)
      c.1 hc (hp₀.mono hcle) hqr hγ hγb
      (fun e => hag₀ ⟨e.1, e.2.trans hcle⟩) hpc
      hcover (hcle.trans hCU) hOU hOV hinter hl hright hU hV
    have hreadPhys (e : (stepCarrier sem m hA).below (C, m + 3)) :
        u (CellScheme.below.mono
          (show GradedLe (C, m + 3) (A, m + 3) from
            ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = min (p e) M := by
      obtain ⟨d, rfl⟩ := E.surjective e
      have hd : CellScheme.below.mono
          (show GradedLe (C, m + 3) (A, m + 3) from
            ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) = oldTarget sem m hA d.1 :=
        Subtype.ext (faceEquiv_val sem m hA _ hCnot le_rfl d)
      rw [hd]
      exact hread ⟨d.1, by rw [hci]; exact d.2⟩
    have hmaxPhys (e : (stepCarrier sem m hA).below (C, m + 3))
        (he : (stepCarrier sem m hA).grade e.1 = m + 3) : p e ≤ M := by
      obtain ⟨d, rfl⟩ := E.surjective e
      apply hmax d
      change ((stepCarrier sem m hA).cell (E d).1).2 = m + 3 at he
      rwa [faceEquiv_cell] at he
    obtain ⟨r, hr, hrlit, hrM, _⟩ := SingleFaceTailRestoration.exists_restore
      (outRows sem m hA hp) (D.isPlan.subset_of_mem hC) hcl hpr hu hM hreadPhys hmaxPhys
    exact ⟨r, hr, fun d =>
      (GradeTailRestoration.cap_below (hrM d) hpc.le).trans (hcap d), hrlit⟩
  · exact SingleFaceTailRestoration.exists_inactive (outRows sem m hA hp)
      (D.isPlan.subset_of_mem hC) hcl hpr hqr hγ hag
      (fun d hd => not_lt.mp (fun h => hactive ⟨d, hd, h⟩))

private theorem bountiful_step
    (hb : (GradeCutBoundary.rows (predecessor sem m hA) (m + 2)
      (predState sem m hA hp).rows).IsBountiful)
    (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
    (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
    (hLc : m + 3 ≤ L.card) (hRc : m + 3 ≤ R.card) (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → m + 3 ≤ C.card →
      ∃ d : Cell D, D.cell d = (C, m + 3)) :
    (GradeCutBoundary.rows (stepCarrier sem m hA) (m + 3) (outRows sem m hA hp)).IsBountiful := by
  have full_side {U V : Finset ι} (hU : U ∈ D.plan) (hV : V ∈ D.plan)
      (hUA : U ≠ A) (hVA : V ≠ A) (hUc : m + 3 ≤ U.card) (hVc : m + 3 ≤ V.card)
      (hUV : U ∩ V ∈ D.plan) (hcov : ∀ C ∈ D.plan, C ≠ A → C ⊆ U ∨ C ⊆ V)
      {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A) (hCc : m + 3 ≤ C.card) (hCU : C ⊆ U) :
      CappedLift (outRows sem m hA hp)
        (show GradedLe (C, m + 3) (A, m + 3) from ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
    have cov (d : Cell (cut (D := D) m)) :
        GradedLe ((cut (D := D) m).cell d) (U, m + 3) ∨
        GradedLe ((cut (D := D) m).cell d) (V, m + 3) :=
      (hcov _ (D.scope_mem_plan _) (hp (occ (D := D) m d))).imp
        (fun h => ⟨h, GradeCutBoundary.grade_bound D _ d⟩)
        (fun h => ⟨h, GradeCutBoundary.grade_bound D _ d⟩)
    have left : CappedLift (cutRows sem m)
        (show GradedLe (C, m + 3) (U, m + 3) from ⟨hCU, le_rfl⟩) :=
      (GradeCutLifting.lift_iff sem (m + 3) _ le_rfl).mpr
        (hold (C, m + 3) (U, m + 3) (Plan.mem_gradedPlan.mpr ⟨hC, by omega, hCc⟩)
          (Plan.mem_gradedPlan.mpr ⟨hU, by omega, hUc⟩) hUA ⟨hCU, le_rfl⟩)
    have right : CappedLift (cutRows sem m)
        (target_le_right (U := (U, m + 3)) (V := (V, m + 3))) := by
      apply (GradeCutLifting.lift_iff sem (m + 3) _ le_rfl).mpr
      by_cases hne : (U ∩ V).Nonempty
      · exact hold _ _ (target_mem_gradedPlan hUV (by omega) (by omega) hne)
          (Plan.mem_gradedPlan.mpr ⟨hV, by omega, hVc⟩) hVA target_le_right
      · let := target_empty (D := D) (U := (U, m + 3)) (V := (V, m + 3))
          (Finset.not_nonempty_iff_eq_empty.mp hne)
        exact lift_empty target_le_right
    have hfull : ∃ c : (cut (D := D) m).below (C, m + 3),
        (cut (D := D) m).cell c.1 = (C, m + 3) := by
      obtain ⟨d, hd⟩ := hcomplete C hC hCA hCc
      have hgd : D.grade d ≤ m + 3 := (congrArg Prod.snd hd).le
      let c := GradeCutBoundary.fromCell D (m + 3) d hgd
      have hc : (cut (D := D) m).cell c = (C, m + 3) := by
        change D.cell (GradeCutBoundary.toCell D (m + 3) c) = _
        rw [GradeCutBoundary.to_from, hd]
      exact ⟨⟨c, by rw [hc]; exact GradedLe.refl _⟩, hc⟩
    exact full_lift_step sem m hA hp hb hC hCA hCc hfull cov
      ⟨hCU, le_rfl⟩ target_le_left target_le_right
      (fun d hl hr => (below_target_iff d).mpr ⟨hl, hr⟩) left right le_rfl le_rfl
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound (stepCarrier sem m hA) (m + 3)) (by omega)
  intro C B i hC hB hi hCB
  change (C, i) ∈ Plan.gradedPlan (CanonicalRecursiveInventory.scheme sem (m + 3) hA).plan at hC
  change (B, i) ∈ Plan.gradedPlan (CanonicalRecursiveInventory.scheme sem (m + 3) hA).plan at hB
  have hc : (C, i) ∈ Plan.gradedPlan D.plan := by
    rwa [CanonicalRecursiveBoundaryTransport.plan_eq] at hC
  have hb' : (B, i) ∈ Plan.gradedPlan D.plan := by
    rwa [CanonicalRecursiveBoundaryTransport.plan_eq] at hB
  apply (GradeCutLifting.lift_iff (outRows sem m hA hp) (m + 3) _ hi).mpr
  by_cases hil : i ≤ m + 2
  · apply lower_lift sem m hA hp _ hil
    apply (GradeCutLifting.lift_iff (predState sem m hA hp).rows (m + 2) _ hil).mp
    apply lift_of_bountiful hb
    · change (C, i) ∈ Plan.gradedPlan (predecessor sem m hA).plan
      rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hc
    · change (B, i) ∈ Plan.gradedPlan (predecessor sem m hA).plan
      rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hb'
  have hik : i = m + 3 := by omega
  subst i
  by_cases hBA : B = A
  · subst B
    by_cases hCA : C = A
    · subst C; exact lift_refl
    · have hCmem := (Plan.mem_gradedPlan.mp hc).1
      have hCc := (Plan.mem_gradedPlan.mp hc).2.2
      rcases hcover C hCmem hCA with hl | hr
      · exact full_side hL hR hLA hRA hLc hRc hO hcover hCmem hCA hCc hl
      · exact full_side hR hL hRA hLA hRc hLc (Finset.inter_comm L R ▸ hO)
          (fun C hC hCA => (hcover C hC hCA).symm) hCmem hCA hCc hr
  · apply CanonicalRecursiveBoundaryTransport.proper_liftAt sem hp (m + 1) hA _
      (fun h => hBA (Finset.Subset.antisymm
        (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hb').1) h))
    exact hold _ _ hc hb' hBA ⟨hCB, le_rfl⟩

end Step

variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)
variable (hs : sem.IsConsistent) (hold : CanonicalCoatomBountiful.OldLifts sem)
variable {L R : Finset ι} (hL : L ∈ D.plan) (hR : R ∈ D.plan)
variable (hLA : L ≠ A) (hRA : R ≠ A) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

include hs hold hL hR hLA hRA hO hcover in
theorem readyAt (m : ℕ) (hA : m + 2 ≤ A.card)
    (hLc : m + 2 ≤ L.card) (hRc : m + 2 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ m + 2 →
      ∃ d : Cell D, D.cell d = (C, i)) : ReadyAt sem hp m hA := by
  induction m with
  | zero =>
    refine ⟨hs, ?_⟩
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (GradeCutBoundary.grade_bound (carrierAt sem 0 hA) 2) (by decide)
    intro C B i hC hB hi hCB
    apply (GradeCutLifting.lift_iff (rowsAt sem hp 0 hA) 2 _ hi).mpr
    exact CanonicalPairLowerLifting.lower_lift sem hp hA hold
      hL hR hLA hRA hLc hRc hO hcover hcomplete hC hB ⟨hCB, le_rfl⟩ hi
  | succ m ih =>
    have hprev := ih (Nat.le_of_succ_le hA) (Nat.le_of_succ_le hLc) (Nat.le_of_succ_le hRc)
      (fun C hC hCA i hi hic him => hcomplete C hC hCA i hi hic (by omega))
    exact ⟨hs, bountiful_step sem m hA hp hprev.2 hold hL hR hLA hRA hLc hRc hO hcover
      (fun C hC hCA hc => hcomplete C hC hCA (m + 3) (by omega) hc le_rfl)⟩

include hs hold hL hR hLA hRA hO hcover in
theorem liftAt (m : ℕ) (hA : m + 2 ≤ A.card)
    (hLc : m + 2 ≤ L.card) (hRc : m + 2 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ m + 2 →
      ∃ d : Cell D, D.cell d = (C, i))
    {I J : Finset ι × ℕ} (hI : I ∈ Plan.gradedPlan D.plan)
    (hJ : J ∈ Plan.gradedPlan D.plan) (h : GradedLe I J) (hJk : J.2 ≤ m + 2) :
    CappedLift (rowsAt sem hp m hA) h := by
  apply (GradeCutLifting.lift_iff (rowsAt sem hp m hA) (m + 2) h hJk).mp
  apply lift_of_bountiful (readyAt sem hp hs hold hL hR hLA hRA hO hcover
    m hA hLc hRc hcomplete).2
  · change I ∈ Plan.gradedPlan (carrierAt sem m hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hI
  · change J ∈ Plan.gradedPlan (carrierAt sem m hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hJ

include hs hold hL hR hLA hRA hO hcover in
theorem ready (n : ℕ) (hA : n + 3 ≤ A.card)
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 3 →
      ∃ d : Cell D, D.cell d = (C, i)) : Ready sem hp n hA :=
  readyAt sem hp hs hold hL hR hLA hRA hO hcover (n + 1) hA hLc hRc hcomplete

include hs hold hL hR hLA hRA hO hcover in
theorem lift (n : ℕ) (hA : n + 3 ≤ A.card)
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 3 →
      ∃ d : Cell D, D.cell d = (C, i))
    {I J : Finset ι × ℕ} (hI : I ∈ Plan.gradedPlan D.plan)
    (hJ : J ∈ Plan.gradedPlan D.plan) (h : GradedLe I J) (hJk : J.2 ≤ n + 3) :
    CappedLift (rows sem hp n hA) h :=
  liftAt sem hp hs hold hL hR hLA hRA hO hcover (n + 1) hA hLc hRc hcomplete hI hJ h hJk

end
end VaughtConjecture.Knight.CanonicalRecursiveInitialized
