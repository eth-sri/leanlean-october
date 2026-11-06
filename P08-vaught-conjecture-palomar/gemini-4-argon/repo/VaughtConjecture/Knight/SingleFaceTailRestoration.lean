/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice
public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Literal single-face restoration from a predecessor lifting clause

The lower ambient is constructed by restricting the capped lawful section.
Lower values need not be equal, bounded by the owner, visible upstairs, or
proper. The unchanged upper tail is bounded by the restoration cap.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.SingleFaceTailRestoration
open Transform Value ExtOrd GradeTailRestoration CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) {C B : Finset ι} {j : ℕ} (hCB : C ⊆ B)

/-- Internal restoration producer. Only the lower lifting clause is used;
no lifting property of the upper output or scalar unsaturation is assumed. -/
theorem exists_restore
    (hlift : CappedLift sem (show GradedLe (C, j) (B, j) from ⟨hCB, le_rfl⟩))
    {p : D.below (C, j + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (C, j + 1) p)
    {u : D.below (B, j + 1) → ExtOrd}
    (hu : RespectsSemanticsBelow sem (B, j + 1) u)
    {M : ExtOrd} (hM : SelfVis (j + 1) M)
    (hread : ∀ e, u (CellScheme.below.mono
      (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) e) = min (p e) M)
    (hhigh : ∀ e : D.below (C, j + 1), D.grade e.1 = j + 1 → p e ≤ M) :
    ∃ r : D.below (B, j + 1) → ExtOrd,
      RespectsSemanticsBelow sem (B, j + 1) r ∧
      (∀ e, r (CellScheme.below.mono
        (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) e) = p e) ∧
      (∀ d, min (r d) M = min (u d) M) ∧
      ∀ d, j < D.grade d.1 → r d ≤ M := by
  let v := fun d => min (u d) M
  have hv : RespectsSemanticsBelow sem (B, j + 1) v := hu.cap hM
  let hC : GradedLe (C, j) (C, j + 1) := ⟨Finset.Subset.refl _, Nat.le_succ j⟩
  let hB : GradedLe (B, j) (B, j + 1) := ⟨Finset.Subset.refl _, Nat.le_succ j⟩
  let hl : GradedLe (C, j) (B, j) := ⟨hCB, le_rfl⟩
  let pl := p ∘ CellScheme.below.mono hC
  let ql := v ∘ CellScheme.below.mono hB
  have hag (d : D.below (C, j)) :
      min (ql (CellScheme.below.mono hl d)) M = min (pl d) M := by
    change min (min (u _) M) M = min (p _) M
    have hh := congrArg (fun z => min (min z M) M) (hread (CellScheme.below.mono hC d))
    exact hh.trans (by rw [min_assoc, min_self, min_assoc, min_self])
  obtain ⟨w, hw, hwcap, hwread⟩ := hlift pl ql M (hp.mono hC) (hv.mono hB)
    (hM.mono (Nat.le_succ j)) hag
  refine ⟨splice v w, splice_respects (Nat.le_succ j) hv hw
    (fun _ _ => min_le_right _ _) hwcap, ?_, ?_, ?_⟩
  · intro e
    by_cases he : D.grade e.1 ≤ j
    · rw [splice_low v w _ he]
      exact hwread ⟨e.1, e.2.1, he⟩
    · rw [splice_high v w _ he]
      change min (u _) M = p e
      have hg : D.grade e.1 = j + 1 := by
        have hb : D.grade e.1 ≤ j + 1 := e.2.2
        omega
      rw [hread e, min_assoc, min_self, min_eq_left (hhigh e hg)]
  · intro d
    exact (splice_cap (Nat.le_succ j) hwcap d).trans
      (show min (min (u d) M) M = min (u d) M by rw [min_assoc, min_self])
  · intro d hd
    rw [splice_high v w d (not_le.mpr hd)]
    exact min_le_right _ _

/-- Inactive upper prescriptions lift directly from an arbitrary lawful
ambient. This includes bottom and top caps and an empty upper-owner set. -/
theorem exists_inactive
    (hlift : CappedLift sem (show GradedLe (C, j) (B, j) from ⟨hCB, le_rfl⟩))
    {p : D.below (C, j + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow sem (C, j + 1) p)
    {q : D.below (B, j + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (B, j + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (j + 1) γ)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) e)) γ = min (p e) γ)
    (hhigh : ∀ e : D.below (C, j + 1), D.grade e.1 = j + 1 → p e ≤ γ) :
    ∃ r : D.below (B, j + 1) → ExtOrd,
      RespectsSemanticsBelow sem (B, j + 1) r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, j + 1) (B, j + 1) from ⟨hCB, le_rfl⟩) e) = p e := by
  obtain ⟨r, hr, hread, hcap, _⟩ := exists_restore sem hCB hlift hp (hq.cap hγ) hγ hag hhigh
  exact ⟨r, hr, fun d => (hcap d).trans
    (show min (min (q d) γ) γ = min (q d) γ by rw [min_assoc, min_self]), hread⟩

theorem full_lift_of_owner
    {K D_cut : CellScheme A} {Rws : Semantics K} {sem_cut : Semantics D_cut}
    (hCA_sub : C ⊆ A)
    (hlower : CappedLift Rws (show GradedLe (C, j) (A, j) from ⟨hCA_sub, le_rfl⟩))
    (E : D_cut.below (C, j + 1) ≃ K.below (C, j + 1))
    (oldT : Cell D_cut → K.below (A, j + 1))
    (he_val : ∀ d : D_cut.below (C, j + 1), (E d).1 = (oldT d.1).1)
    (holdT_cell : ∀ d : Cell D_cut, K.cell (oldT d).1 = D_cut.cell d)
    (hpull : ∀ {p : K.below (C, j + 1) → ExtOrd},
      RespectsSemanticsBelow Rws (C, j + 1) p → RespectsSemanticsBelow sem_cut (C, j + 1) (p ∘ E))
    (hsec : ∀ {p : K.below (C, j + 1) → ExtOrd},
      RespectsSemanticsBelow Rws (C, j + 1) p →
      ∃ r : K.below (A, j + 1) → ExtOrd,
        RespectsSemanticsBelow Rws (A, j + 1) r ∧
        ∀ e, r (CellScheme.below.mono (show GradedLe (C, j + 1) (A, j + 1) from ⟨hCA_sub, le_rfl⟩) e) = p e)
    {U : Finset ι × ℕ} (hCU : GradedLe (C, j + 1) U) (hleft : CappedLift sem_cut hCU)
    (hfull : ∃ c : D_cut.below (C, j + 1), D_cut.cell c.1 = (C, j + 1))
    (howner : ∀ (c : Cell D_cut), D_cut.grade c = j + 1 →
      ∀ {p : D_cut.below (D_cut.cell c) → ExtOrd}, RespectsSemanticsBelow sem_cut (D_cut.cell c) p →
      ∀ {q : K.below (A, j + 1) → ExtOrd}, RespectsSemanticsBelow Rws (A, j + 1) q →
      ∀ {γ : ExtOrd}, SelfVis (j + 1) γ → γ ≠ ⊥ →
      (∀ e, min (p e) γ = min (q (oldT e.1)) γ) →
      γ < p ⟨c, GradedLe.refl _⟩ →
      ∀ {hcU : GradedLe (D_cut.cell c) U}, CappedLift sem_cut hcU →
      ∃ r : K.below (A, j + 1) → ExtOrd,
        RespectsSemanticsBelow Rws (A, j + 1) r ∧
        (∀ e, r (oldT e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
        ∀ d, min (r d) γ = min (q d) γ) :
    CappedLift Rws (show GradedLe (C, j + 1) (A, j + 1) from ⟨hCA_sub, le_rfl⟩) := by
  intro p q γ hpr hqr hγ hag
  by_cases hγb : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := hsec hpr
    exact ⟨r, hr, fun _ => by simp only [hγb, min_bot_right], hread⟩
  by_cases hactive : ∃ d : K.below (C, j + 1), K.grade d.1 = j + 1 ∧ γ < p d
  · have hp₀ := hpull hpr
    obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp₀ hfull
    let p₀ := p ∘ E
    let M := p₀ c
    have he_cell (d : D_cut.below (C, j + 1)) : K.cell (E d).1 = D_cut.cell d.1 := by
      rw [he_val, holdT_cell]
    have hpc : γ < M := by
      obtain ⟨d, hd, hpd⟩ := hactive
      obtain ⟨e, rfl⟩ := E.surjective d
      exact hpd.trans_le (hmax e (by
        change (K.cell (E e).1).2 = j + 1 at hd
        rwa [he_cell] at hd))
    have hc : D_cut.grade c.1 = j + 1 := congrArg Prod.snd hci
    have hM : SelfVis (j + 1) M := by simpa only [hc] using (hp₀.orderly c).symm
    have hcle : GradedLe (D_cut.cell c.1) (C, j + 1) := c.2
    have hag₀ (e : D_cut.below (C, j + 1)) : min (p₀ e) γ = min (q (oldT e.1)) γ := by
      have he : CellScheme.below.mono (show GradedLe (C, j + 1) (A, j + 1) from ⟨hCA_sub, le_rfl⟩) (E e) =
          oldT e.1 := Subtype.ext (he_val e)
      simpa only [p₀, Function.comp_apply, he] using (hag (E e)).symm
    obtain ⟨u, hu, hread, hcap⟩ := howner c.1 hc (hp₀.mono hcle) hqr hγ hγb
      (fun e => hag₀ ⟨e.1, e.2.trans hcle⟩) hpc (hcU := hcle.trans hCU)
      (by simpa only [hci] using hleft)
    obtain ⟨r, hr, hrlit, hrM, _⟩ := exists_restore Rws hCA_sub hlower hpr hu hM
      (fun e => by
        obtain ⟨d, rfl⟩ := E.surjective e
        rw [show CellScheme.below.mono (show GradedLe (C, j + 1) (A, j + 1) from ⟨hCA_sub, le_rfl⟩) (E d) =
          oldT d.1 from Subtype.ext (he_val d)]
        exact hread ⟨d.1, by rw [hci]; exact d.2⟩)
      fun e he => by
        obtain ⟨d, rfl⟩ := E.surjective e
        apply hmax d
        change (K.cell (E d).1).2 = j + 1 at he
        rwa [he_cell] at he
    exact ⟨r, hr, fun d => (cap_below (hrM d) hpc.le).trans (hcap d), hrlit⟩
  · exact exists_inactive Rws hCA_sub hlower hpr hqr hγ hag
      fun d hd => not_lt.mp fun h => hactive ⟨d, hd, h⟩
