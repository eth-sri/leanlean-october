/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SlotControllerFamily

/-! # Joint controllers for different finite source profiles

Profiles may order the old occurrences differently. Their cross-reading is
the largest natural cut through which they agree literally. Its ultrametric
identity supplies all new/new localities, with separated grade-one source
codes and explicit witnesses. No common old order or transformation
composition is used. Scope geometry and extension supply are separate.
-/

namespace VaughtConjecture.Knight.FiniteProfileControllers



variable {X Q : Type*}

def Agree (a b : X → ℕ) (k : ℕ) := ∀ d, min (a d) k = min (b d) k

theorem Agree.mono {a b : X → ℕ} {k l} (h : Agree a b k) (hl : l ≤ k) : Agree a b l := by
  intro d
  have hh := congrArg (fun z => min z l) (h d)
  simpa only [min_assoc, min_eq_right hl] using hh

open Classical in
noncomputable def cut H (a b : X → ℕ) :=
  ((Finset.range (H + 1)).filter (Agree a b)).sup id

theorem cut_le {H : ℕ} {a b : X → ℕ} : cut H a b ≤ H := by
  classical
  apply Finset.sup_le
  intro k hk
  have hh := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  exact Nat.le_of_lt_succ hh

theorem le_cut {H k} {a b : X → ℕ} (hk : k ≤ H) (h : Agree a b k) : k ≤ cut H a b := by
  classical
  
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), h⟩)

theorem agree_cut H (a b : X → ℕ) : Agree a b (cut H a b) := by
  classical
  have hn : ((Finset.range (H + 1)).filter (Agree a b)).Nonempty :=
    ⟨0, by simp [Agree]⟩
  obtain ⟨k, hk, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
  have ha := (Finset.mem_filter.mp hk).2
  change k = cut H a b at he
  exact he ▸ ha

theorem cut_symm H (a b : X → ℕ) : cut H a b = cut H b a := by
  apply le_antisymm
  · exact le_cut (cut_le) (fun d => (agree_cut H a b d).symm)
  · exact le_cut (cut_le) (fun d => (agree_cut H b a d).symm)

theorem cut_refl (H : ℕ) (a : X → ℕ) : cut H a a = H :=
  le_antisymm (cut_le) (le_cut le_rfl (fun _ => rfl))

theorem cut_triangle H (a b c : X → ℕ) :
    min (cut H a b) (cut H b c) ≤ cut H a c := by
  apply le_cut ((min_le_left _ _).trans (cut_le))
  intro d
  exact ((agree_cut H a b).mono (min_le_left _ _) d).trans
    ((agree_cut H b c).mono (min_le_right _ _) d)

/-- The exact clipped cross-reading identity, not only a triangle inequality. -/
theorem cross_agreement H (a b c : X → ℕ) :
    min (cut H a c) (cut H a b) = min (cut H b c) (cut H a b) := by grind [cut_triangle, cut_symm]

variable [Finite X] [Finite Q]

