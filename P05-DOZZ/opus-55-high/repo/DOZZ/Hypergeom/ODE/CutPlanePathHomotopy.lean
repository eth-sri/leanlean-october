/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneTopology
public import Mathlib.Topology.Homotopy.Path

/-! A path homotopy in the Gauss cut plane gives the real-square input used by the ODE
homotopy grid. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

theorem subtype_paths_real_homotopy
    {U : Set ℂ} {x y : U} {p q : Path x y} (F : p.Homotopy q) :
    ∃ Γ : ℝ × ℝ → ℂ,
      ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Γ (0, s) = (x : ℂ)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Γ (1, s) = (y : ℂ)) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), Γ (s, 0) = (p ⟨s, hs⟩ : ℂ)) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), Γ (s, 1) = (q ⟨s, hs⟩ : ℂ)) ∧
      ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Γ z ∈ U := by
  let proj : ℝ → unitInterval := fun t => Set.projIcc 0 1 zero_le_one t
  let Γ : ℝ × ℝ → ℂ := fun z => (F (proj z.2, proj z.1) : U)
  have hΓcont : Continuous Γ := by
    fun_prop
  refine ⟨Γ, hΓcont.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · aesop
  · aesop
  · intro s hs
    have hs' : proj s = ⟨s, hs⟩ := Set.projIcc_of_mem zero_le_one hs
    aesop
  · intro s hs
    have hs' : proj s = ⟨s, hs⟩ := Set.projIcc_of_mem zero_le_one hs
    aesop
  aesop


end DOZZ.Proofs
