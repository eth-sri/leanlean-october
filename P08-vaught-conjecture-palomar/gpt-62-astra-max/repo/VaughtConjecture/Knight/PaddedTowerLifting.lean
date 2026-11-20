/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedTowerGeometry
public import VaughtConjecture.Knight.PlacedFaceRestoration
public import VaughtConjecture.Knight.TwoFaceLifting

/-! # Original-face lifting at all legal cutoffs of a built tower -/

@[expose] public section
namespace VaughtConjecture.Knight.PaddedTower
open CoatomBoundaryExtension
variable {ι X : Type*} [DecidableEq ι] [Fintype X] {A B : Finset ι} {D : CellScheme A}
  {Q : ℕ → Type*} [∀ j, Fintype (Q j)] (F : System D X Q)

/-- Every lower lifting clause persists, since no new owner lies below its target. -/
theorem lowerLift {k} (P : Layer F k) (hk : 1 ≤ k) (ht : k+1 ≤ A.card) {U V : Finset ι × ℕ}
    {h : GradedLe U V} (hv : V.2 ≤ k) (hl : CappedLift P.rows h) : CappedLift (Step.rows P hk ht) h :=
  HighLayerBountiful.transport_lift _ _ _ _ _ (P.separated hk) _ _ (Step.inherited_row P hk ht) h
    (fun he => Nat.not_succ_le_self k (he.2.trans hv)) hl

/-- Induct on the installed layer, generating only grades possible on the prescribed face. -/
theorem buildLift {n : ℕ} (sub : B ⊆ A)
    (base : CappedLift F.baseRows (GradedLe.atGrade sub 1))
    (step : ∀ {k} (P : Layer F k) (hk : 1 ≤ k) (ht : k+1 ≤ A.card), k+1 ≤ n →
      CappedLift (Step.rows P hk ht) (GradedLe.atGrade sub k) →
      CappedLift (Step.rows P hk ht) (GradedLe.atGrade sub (k+1)))
    (t : ℕ) (ht : t+1 ≤ A.card) {j : ℕ} (hj : 1 ≤ j) (hn : j ≤ n) (hlt : j ≤ t+1) :
    CappedLift (build F t ht).rows (GradedLe.atGrade sub j) := by
  induction t generalizing j with
  | zero =>
    obtain rfl : j = 1 := by omega
    exact base
  | succ t ih =>
    let P := build F t (by omega)
    by_cases he : j = t+2
    · subst j
      exact step P (Nat.succ_pos _) ht hn (lowerLift F P (Nat.succ_pos _) ht le_rfl
        (ih _ (Nat.succ_pos _) (by omega) le_rfl))
    · exact lowerLift F P (Nat.succ_pos _) ht (show j ≤ t+1 by omega) (ih _ hj hn (by omega))
end VaughtConjecture.Knight.PaddedTower
