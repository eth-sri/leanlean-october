/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFilteredRoot

@[expose] public section

namespace VaughtConjecture.Knight.Growth

open Transform Value ExtOrd AmalgamationPlan
open CellScheme (complete complete_present complete_future complete_lawful complete_visible complete_cap)

noncomputable section

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

namespace RootAttachment

theorem privateIncl (j : ℕ) : GradedLe (Finset.univ.image fC, j) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, le_rfl⟩

theorem donorIncl (j : ℕ) : GradedLe (Finset.univ.image fP, j) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, le_rfl⟩

local notation "aP" => donorIncl (fP := fP)

local notation "aC" => privateIncl (fC := fC)

local notation "e" => rootMap F fP hvP hP fC hvC hC

include R in
theorem shared_at {S : State C.scheme P.scheme} {j : ℕ} (hS : Admitted X j S)
    (a : P.scheme.below (Finset.univ.image fP, j)) :
    S.donorValues a.1 = S.privateValues (e j a).1 := by
  rw [R.at_occurrence a]
  exact hS.shared (R.full a)

def replace {j : ℕ} (S : State C.scheme P.scheme)
    (u : C.scheme.below (Finset.univ, j) → ExtOrd)
    (v : P.scheme.below (Finset.univ, j) → ExtOrd) : State C.scheme P.scheme :=
  ⟨complete S.privateValues u, complete S.donorValues v⟩

private theorem replace_caps {j : ℕ} {S : State C.scheme P.scheme}
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    {v : P.scheme.below (Finset.univ, j) → ExtOrd} {γ : ExtOrd}
    (hu : ∀ d, min (u d) γ = min (S.privateValues d.1) γ)
    (hv : ∀ d, min (v d) γ = min (S.donorValues d.1) γ) : S.CapEq γ (replace S u v) := by
  rintro (d | d)
  · exact complete_cap _ hu d
  · exact complete_cap _ hv d

include R

theorem replace_shared {j : ℕ} {S : State C.scheme P.scheme} (hS : Admitted X j S)
    (u : C.scheme.below (Finset.univ, j) → ExtOrd)
    (v : P.scheme.below (Finset.univ, j) → ExtOrd)
    (he : ∀ a : P.scheme.below (Finset.univ.image fP, j),
      v (CellScheme.below.mono (aP j) a) = u (CellScheme.below.mono (aC j) (e j a))) :
    ∀ d : P.scheme.below X.root,
      (replace S u v).donorValues d.1 = (replace S u v).privateValues (X.κ d).1 := by
  intro d
  by_cases hd : P.scheme.grade d.1 ≤ j
  · let a := R.filtered d hd
    have hc : (e j a).1 = (X.κ d).1 := R.at_occurrence a
    change complete S.donorValues v d.1 = complete S.privateValues u (X.κ d).1
    exact (complete_present S.donorValues v (CellScheme.below.mono (aP j) a)).trans
      ((he a).trans ((complete_present S.privateValues u
        (CellScheme.below.mono (aC j) (e j a))).symm.trans
        (congrArg (complete S.privateValues u) hc)))
  · change complete S.donorValues v d.1 = complete S.privateValues u (X.κ d).1
    rw [complete_future S.donorValues v d.1 (not_le.mp hd),
      complete_future S.privateValues u (X.κ d).1 (by rw [R.grade]; exact not_le.mp hd)]
    exact hS.shared d

theorem replace_admitted {j : ℕ} (hj : j < X.req.N) {S : State C.scheme P.scheme}
    (hS : Admitted X j S)
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    (he : ∀ a : P.scheme.below (Finset.univ.image fP, j),
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

/-- Before activation, installing a private prescription preserves all caps. -/
theorem private_before {j : ℕ} (hj : j < X.req.N) {S : State C.scheme P.scheme}
    (hS : Admitted X j S) {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (u d) γ = min (S.privateValues d.1) γ) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d) ∧
      S.CapEq γ T := by
  obtain ⟨v, hv, hcap, hread⟩ := P.bountiful.extend hvP P.scheme.isPlan.domain_mem (aP j)
    ((rootMap_lawful F fP hvP hP fC hvC hC j _).mp (hu.mono (aC j))) hS.donor_lawful hγ
    (fun a => (congrArg (min · γ) (R.shared_at hS a)).trans (hag (CellScheme.below.mono (aC j) (e j a))).symm)
  exact ⟨replace S u v, R.replace_admitted hj hS hu hv hread,
    complete_present _ _, replace_caps hag hcap⟩

/-- Donor pre-activation fibre uses private bountifulness through the inverse
literal root map. This is not an exchange of the active request relation. -/
theorem donor_before {j : ℕ} (hj : j < X.req.N) {S : State C.scheme P.scheme}
    (hS : Admitted X j S) {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (v d) γ = min (S.donorValues d.1) γ) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d) ∧
      S.CapEq γ T := by
  obtain ⟨u, hu, hcap, hread⟩ := C.bountiful.extend_inverse hvC C.scheme.isPlan.domain_mem (aC j)
    (e j) (rootMap_lawful F fP hvP hP fC hvC hC j) hS.private_lawful (hv.mono (aP j)) hγ
    (fun a => (congrArg (min · γ) (R.shared_at hS a).symm).trans (hag (CellScheme.below.mono (aP j) a)).symm)
  exact ⟨replace S u v, R.replace_admitted hj hS hu hv (fun a => (hread a).symm),
    complete_present _ _, replace_caps hcap hag⟩

end RootAttachment

end

end VaughtConjecture.Knight.Growth
