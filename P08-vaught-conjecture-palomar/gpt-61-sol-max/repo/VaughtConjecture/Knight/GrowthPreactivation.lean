/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthFilteredRoot

/-! # Both growth fibres before activation

Only the original schemes are lifted. Every future coordinate of both complete
vectors remains literal, since the literal common-root maps preserve grades.
Bottom caps, top caps and top prescriptions require no separate positivity
argument. The activation relation is not weakened; it is inactive at this cutoff.
-/

namespace VaughtConjecture.Knight.Growth
section

section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {j : ℕ} (u : CellLabels D)
  {p : BelowLabels D (A, j)}

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow sem (A, j)

theorem complete_lawful (hp : RespectsSemanticsBelow₀ p) :
    RespectsSemanticsBelow₀ (fun d => complete u p d.1) := by
  simpa only [complete_present] using hp

theorem complete_visible (hu : ∀ d, SelfVis 1 (u d))
    (hp : RespectsSemanticsBelow₀ p) d : SelfVis 1 (complete u p d) := by
  by_cases hd : D.grade d ≤ j
  · let e : D.below (A, j) := ⟨d, D.scope_subset d, hd⟩
    rw [complete_present u p e]
    have h : SelfVis (D.grade d) (p e) := (hp.orderly e).symm
    exact h.mono (D.grade_pos d)
  · grind [complete_future]

theorem complete_caps {γ} (h : ∀ d, min (p d) γ = min (u d.1) γ)
    d : min (complete u p d) γ = min (u d) γ := by
  by_cases hd : D.grade d ≤ j
  · let e : D.below (A, j) := ⟨d, D.scope_subset d, hd⟩
    rw [complete_present u p e]
    exact h e
  · grind [complete_future]
end

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

namespace RootAttachment

theorem privateIncl j : GradedLe (Finset.univ.image fC, j) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, le_rfl⟩
theorem donorIncl j : GradedLe (Finset.univ.image fP, j) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, le_rfl⟩

local notation "aP" => donorIncl (fP := fP)
local notation "aC" => privateIncl (fC := fC)
local notation "e" => rootMap F fP hvP hP fC hvC hC

include R in
theorem shared_at {S} {j} (hS : Admitted X j S)
    (a : P.scheme.below (Finset.univ.image fP, j)) :
    S.donorValues a.1 = S.privateValues (e j a).1 := by
  rw [R.at_occurrence a]
  exact hS.shared (R.full a)

def replace {j : ℕ} (S : State C.scheme P.scheme)
    (u : BelowLabels C.scheme (Finset.univ, j))
    (v : BelowLabels P.scheme (Finset.univ, j)) : State C.scheme P.scheme :=
  ⟨complete S.privateValues u, complete S.donorValues v⟩

include R

theorem replace_shared {j} {S} (hS : Admitted X j S)
    u
    v
    (he : ∀ a ,
      v (CellScheme.below.mono (aP j) a) = u (CellScheme.below.mono (aC j) (e j a))) :
    ∀ d ,
      (replace S u v).donorValues d.1 = (replace S u v).privateValues (X.κ d).1 := by
  intro d
  by_cases hd : P.scheme.grade d.1 ≤ j
  · let a := R.filtered d hd
    have hc  := R.at_occurrence a
    
    exact (complete_present S.donorValues v (CellScheme.below.mono (aP j) a)).trans
      ((he a).trans ((complete_present S.privateValues u
        (CellScheme.below.mono (aC j) (e j a))).symm.trans
        (congrArg (complete S.privateValues u) hc)))
  · change complete S.donorValues v d.1 = complete S.privateValues u (X.κ d).1
    rw [complete_future S.donorValues v d.1 (not_le.mp hd),
      complete_future S.privateValues u (X.κ d).1 (by rw [R.grade]; exact not_le.mp hd)]
    exact hS.shared d

theorem replace_admitted {j} (hj : j < X.req.N) {S}
    (hS : Admitted X j S)
    {u}
    {v}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    (he : ∀ a ,
      v (CellScheme.below.mono (aP j) a) = u (CellScheme.below.mono (aC j) (e j a))) :
    Admitted X j (replace S u v) where
  private_lawful := complete_lawful _ hu
  donor_lawful := complete_lawful _ hv
  visible f := by
    cases f with
    | inl d => exact complete_visible S.privateValues (fun d => hS.visible (.inl d)) hu d
    | inr d => exact complete_visible S.donorValues (fun d => hS.visible (.inr d)) hv d
  shared := R.replace_shared hS u v he
  correct hN := (not_le.mpr hj hN).elim

/-- Private pre-activation fibre: literal prescription, all complete caps,
and literal future fields on both sides. -/
theorem private_before {j} (hj : j < X.req.N) {S}
    (hS : Admitted X j S) {u}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    {γ} (hγ : SelfVis j γ)
    (hag : ∀ d, min (u d) γ = min (S.privateValues d.1) γ) :
    ∃ T , Admitted X j T ∧
      (∀ d , T.privateValues d.1 = u d) ∧
      S.CapEq γ T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      ∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d := by
  have hlaw := (rootMap_lawful F fP hvP hP fC hvC hC j _).mp (hu.mono (aC j))
  obtain ⟨v, hv, hcap, hread⟩ := extend_cutoff P.bountiful hvP hlaw hS.donor_lawful hγ
    (fun a => by
      change min (S.donorValues a.1) γ = min (u (CellScheme.below.mono (aC j) (e j a))) γ
      rw [R.shared_at hS a]
      exact (hag (CellScheme.below.mono (aC j) (e j a))).symm)
  refine ⟨replace S u v, R.replace_admitted hj hS hu hv hread,
    complete_present S.privateValues u, ?_, complete_future S.privateValues u,
    complete_future S.donorValues v⟩
  intro f
  cases f with
  | inl d => solve_by_elim [complete_caps]
  | inr d => solve_by_elim [complete_caps]

/-- Donor pre-activation fibre uses private bountifulness through the inverse
literal root map. This is not an exchange of the active request relation. -/
theorem donor_before {j} (hj : j < X.req.N) {S}
    (hS : Admitted X j S) {v}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    {γ} (hγ : SelfVis j γ)
    (hag : ∀ d, min (v d) γ = min (S.donorValues d.1) γ) :
    ∃ T , Admitted X j T ∧
      (∀ d , T.donorValues d.1 = v d) ∧
      S.CapEq γ T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      ∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d := by
  let p := fun a => v (CellScheme.below.mono (aP j) ((e j).symm a))
  have hlaw : RespectsSemanticsBelow C.rows (Finset.univ.image fC, j) p := by
    apply (rootMap_lawful F fP hvP hP fC hvC hC j p).mpr
    simpa only [p, Equiv.symm_apply_apply] using hv.mono (aP j)
  obtain ⟨u, hu, hcap, hread⟩ := extend_cutoff C.bountiful hvC hlaw hS.private_lawful hγ
    (fun a => by
      have hs := R.shared_at hS ((e j).symm a)
      rw [Equiv.apply_symm_apply] at hs
      change min (S.privateValues a.1) γ = min (p a) γ
      rw [← hs]
      exact (hag (CellScheme.below.mono (aP j) ((e j).symm a))).symm)
  have he (a : P.scheme.below (Finset.univ.image fP, j)) :
      v (CellScheme.below.mono (aP j) a) = u (CellScheme.below.mono (aC j) (e j a)) := by
    aesop
  refine ⟨replace S u v, R.replace_admitted hj hS hu hv he,
    complete_present S.donorValues v, ?_, complete_future S.privateValues u,
    complete_future S.donorValues v⟩
  intro f
  cases f with
  | inl d => solve_by_elim [complete_caps]
  | inr d => exact complete_caps S.donorValues hag d

