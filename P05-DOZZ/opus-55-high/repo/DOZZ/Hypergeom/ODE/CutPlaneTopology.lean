/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The principal Gauss cut plane is contractible, hence simply connected. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The principal Gauss cut plane is an open subset of the regular plane. -/
theorem gaussCutPlane_isOpen : IsOpen gaussCutPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | 0 < z.re ∧ z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    ((isOpen_Ioo.preimage Complex.continuous_re))

/-- Every point of the principal cut plane avoids the two singularities of the Gauss system. -/
theorem gaussCutPlane_subset_regularPlane : gaussCutPlane ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  aesop

/-- The principal Gauss cut plane is star-convex about its midpoint. -/
theorem gaussCutPlane_starConvex :
    StarConvex ℝ (1 / 2 : ℂ) gaussCutPlane := by
  intro z hz s t hs ht hst
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  change (s • (1 / 2) + t • z).im ≠ 0 ∨
    (0 < (s • (1 / 2) + t • z).re ∧
      (s • (1 / 2) + t • z).re < 1)
  rcases hz with him | ⟨hz0, hz1⟩
  · by_cases ht0 : t = 0
    · right
      have hs1 : s = 1 := by linarith
      bound
    simp_all
  · right
    have hreal : (s • (1 / 2) + t • z).re = s / 2 + t * z.re := by
      aesop
    constructor
    · nlinarith
    nlinarith

/-- Contractibility of the principal Gauss cut plane as a subtype. -/
instance gaussCutPlane_contractible : ContractibleSpace gaussCutPlane := by
  apply gaussCutPlane_starConvex.contractibleSpace
  exact ⟨(1 / 2 : ℂ), by norm_num [gaussCutPlane]⟩


end DOZZ.Proofs
