/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourcePrefixRows

@[expose] public section

namespace VaughtConjecture.Knight.ScopedSourcePrefixLayer

open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer

noncomputable section

variable {ι X : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

structure Data (D : CellScheme A) (k : ℕ) (X : Type*) where
  base : Semantics D
  separated : ∀ c : Cell D, D.cell c ≠ (A, k) → ¬ GradedLe (A, k) (D.cell c)
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis k h
  boundary : Controller D k → X → ExtOrd
  lower : Controller D k → Cell D → ExtOrd
  lower_bound : ∀ q d, D.grade d ≤ k → D.cell d ≠ (A, k) → lower q d ≤ ceiling
  lower_lawful : ∀ q c, D.grade c ≤ k → D.cell c ≠ (A, k) →
    RespectsSemanticsBelow base (D.cell c) (fun d => lower q d.1)
  grid_agreement : ∀ p q h, h ∈ grid → Agree (boundary p) (boundary q) h →
    ∀ d, D.grade d ≤ k → D.cell d ≠ (A, k) → min (lower p d) h = min (lower q d) h

namespace Data

variable (F : Data D k X)

include F in
theorem below_old {c : Cell D} (hc : D.cell c ≠ (A, k)) (d : D.below (D.cell c)) :
    D.cell d.1 ≠ (A, k) := fun hd => F.separated c hc (hd ▸ d.2)

def profile (q : Controller D k) (d : Cell D) : ExtOrd :=
  if hd : D.cell d = (A, k) then cut F.grid (F.boundary q) (F.boundary ⟨d, hd⟩)
  else F.lower q d

theorem profile_old (q : Controller D k) {d : Cell D} (hd : D.cell d ≠ (A, k)) :
    F.profile q d = F.lower q d := by grind +locals

theorem profile_new (q p : Controller D k) :
    F.profile q p.1 = cut F.grid (F.boundary q) (F.boundary p) := by grind +locals

theorem profile_diagonal (q : Controller D k) : F.profile q q.1 = F.ceiling := by
  rw [F.profile_new]
  exact cut_refl F.ceiling_mem F.grid_bound _

theorem profile_bound (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    F.profile q d ≤ F.ceiling := by
  by_cases he : D.cell d = (A, k)
  · rw [show d = (⟨d, he⟩ : Controller D k).1 from rfl, F.profile_new]
    exact cut_le F.grid_bound _ _
  · rw [F.profile_old q he]
    exact F.lower_bound q d hd he

theorem profile_visible (q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    SelfVis (D.grade d) (F.profile q d) := by
  by_cases he : D.cell d = (A, k)
  · rw [show D.grade d = k from congrArg Prod.snd he,
      show d = (⟨d, he⟩ : Controller D k).1 from rfl, F.profile_new]
    exact F.grid_visible _ (cut_mem F.bot_mem _ _)
  · rw [F.profile_old q he]
    exact ((F.lower_lawful q d hd he).orderly ⟨d, GradedLe.refl _⟩).symm

theorem profile_agreement (p q : Controller D k) (d : Cell D) (hd : D.grade d ≤ k) :
    min (F.profile p d) (cut F.grid (F.boundary p) (F.boundary q)) =
      min (F.profile q d) (cut F.grid (F.boundary p) (F.boundary q)) := by
  by_cases he : D.cell d = (A, k)
  · rw [show d = (⟨d, he⟩ : Controller D k).1 from rfl, F.profile_new, F.profile_new]
    exact cross_agreement F.bot_mem _ _ _
  · rw [F.profile_old p he, F.profile_old q he]
    exact F.grid_agreement p q _ (cut_mem F.bot_mem _ _) (agree_cut F.bot_mem _ _) d hd he

end Data

end

end VaughtConjecture.Knight.ScopedSourcePrefixLayer
