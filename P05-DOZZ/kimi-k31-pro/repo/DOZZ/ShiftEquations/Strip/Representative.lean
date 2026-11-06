/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Complex.Basic

/-! Narrow-strip representatives with whole-plane codiscrete shift equations. Real translations
preserve both the strip and its exterior. -/

open Filter Topology Set

namespace DOZZ.Proofs

/-- Restricting exceptions to a set whose closure stays in the original open domain makes
them globally codiscrete. The closure condition also covers the new boundary. -/
theorem codiscreteWithin_restrict_closure
    {S T : Set ℂ} (hS : IsOpen S) (hTS : closure T ⊆ S)
    {p : ℂ → Prop} (hp : ∀ᶠ z in codiscreteWithin S, p z) :
    ∀ᶠ z in codiscrete ℂ, z ∈ T → p z := by
  apply mem_codiscrete_iff_forall_mem_nhdsNE.mpr
  intro z
  by_cases hz : z ∈ closure T
  · have hzS := hTS hz
    have hlocal := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hp z hzS
    have hSne : ∀ᶠ w in 𝓝[≠] z, w ∈ S :=
      (show ∀ᶠ w in 𝓝 z, w ∈ S from hS.mem_nhds hzS).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlocal, hSne] with w hw hSw _
    exact hw hSw
  · have hext : ∀ᶠ w in 𝓝[≠] z, w ∉ closure T :=
      (show ∀ᶠ w in 𝓝 z, w ∉ closure T from
        isClosed_closure.isOpen_compl.mem_nhds hz).filter_mono nhdsWithin_le_nhds
    filter_upwards [hext] with w hw hwT
    exact (hw (subset_closure hwT)).elim

end DOZZ.Proofs
