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
  exact id
    (IsOpen.union (IsOpen.preimage Complex.continuous_im isOpen_compl_singleton)
      (IsOpen.preimage Complex.continuous_re isOpen_Ioo))

/-- Every point of the principal cut plane avoids the two singularities of the Gauss system. -/
theorem gaussCutPlane_subset_regularPlane : gaussCutPlane ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  constructor <;> rintro rfl <;> norm_num [gaussCutPlane] at hz

/-- A convex part of the real axis, together with the nonreal points, is star-convex
about each of its real points. -/
theorem starConvex_complex_with_real_slice {J : Set ℝ} (hJ : Convex ℝ J) {x : ℝ}
    (hx : x ∈ J) : StarConvex ℝ (x : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ J} := by
  intro z hz s t hs ht hst
  change z.im ≠ 0 ∨ z.re ∈ J at hz
  change (s • (x : ℂ) + t • z).im ≠ 0 ∨ (s • (x : ℂ) + t • z).re ∈ J
  rcases hz with him | hre
  · by_cases ht0 : t = 0
    · have hs1 : s = 1 := by linarith
      simp [ht0, hs1, hx]
    · exact Or.inl (by simpa [Complex.add_im] using mul_ne_zero ht0 him)
  · exact Or.inr (by simpa [Complex.add_re] using hJ hx hre hs ht hst)

/-- The principal Gauss cut plane is star-convex about its midpoint. -/
theorem gaussCutPlane_starConvex : StarConvex ℝ (1 / 2 : ℂ) gaussCutPlane := by
  change StarConvex ℝ (1 / 2 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Ioo 0 1}
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    starConvex_complex_with_real_slice (convex_Ioo (0 : ℝ) 1)
      (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)

theorem gaussCutPlane_isPreconnected : IsPreconnected gaussCutPlane :=
  (gaussCutPlane_starConvex.isPathConnected (by norm_num [gaussCutPlane])).isConnected.isPreconnected

end DOZZ.Proofs
