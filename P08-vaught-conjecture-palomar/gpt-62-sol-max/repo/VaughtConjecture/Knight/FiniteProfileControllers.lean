/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotControllerFamily
public import VaughtConjecture.Knight.SourcePrefixRows

@[expose] public section

namespace VaughtConjecture.Knight.FiniteProfileControllers

variable {X : Type*}

abbrev Agree := @SourcePrefixRows.Agree X ℕ _

noncomputable abbrev cut (H : ℕ) (a b : X → ℕ) : ℕ :=
  SourcePrefixRows.cut (Finset.range (H + 1)) a b

private theorem zero_mem (H : ℕ) : 0 ∈ Finset.range (H + 1) := by simp

private theorem mem_range {H k : ℕ} : k ∈ Finset.range (H + 1) ↔ k ≤ H := by simp

theorem cut_le (H : ℕ) (a b : X → ℕ) : cut H a b ≤ H :=
  mem_range.mp (SourcePrefixRows.cut_mem (zero_mem H) a b)

theorem le_cut {H k : ℕ} {a b : X → ℕ} (hk : k ≤ H) (h : Agree a b k) : k ≤ cut H a b :=
  SourcePrefixRows.le_cut (mem_range.mpr hk) h

theorem agree_cut (H : ℕ) (a b : X → ℕ) : Agree a b (cut H a b) :=
  SourcePrefixRows.agree_cut (zero_mem H) a b

theorem cut_symm (H : ℕ) (a b : X → ℕ) : cut H a b = cut H b a :=
  SourcePrefixRows.cut_symm (zero_mem H) a b

theorem cut_refl (H : ℕ) (a : X → ℕ) : cut H a a = H :=
  le_antisymm (cut_le H a a) (le_cut le_rfl (fun _ => rfl))

theorem cut_triangle (H : ℕ) (a b c : X → ℕ) :
    min (cut H a b) (cut H b c) ≤ cut H a c :=
  SourcePrefixRows.cut_triangle (zero_mem H) a b c

theorem cross_agreement (H : ℕ) (a b c : X → ℕ) :
    min (cut H a c) (cut H a b) = min (cut H b c) (cut H a b) :=
  SourcePrefixRows.cross_agreement (zero_mem H) a b c

end VaughtConjecture.Knight.FiniteProfileControllers
