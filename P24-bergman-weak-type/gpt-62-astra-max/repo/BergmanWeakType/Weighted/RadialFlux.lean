/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Linarith
public import BergmanWeakType.Weighted.SmoothCap
public import BergmanWeakType.Weighted.PolarField

/-! # Radial flux and decreasing circular means

This module isolates the one-dimensional consequences of the polar divergence inequality.
-/

@[expose] public section

open MeasureTheory Set

namespace BergmanWeakType.Weighted

/-- Integrating factor for the radial drift. -/
noncomputable def driftWeight (k r : ℝ) := (1 - r ^ 2) ^ k

theorem driftWeight_pos (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1) : 0 < driftWeight k r :=
  Real.rpow_pos_of_pos (sub_pos.mpr hr) _

theorem driftWeight_hasDerivAt (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1) :
    HasDerivAt (driftWeight k) (-(2*k*r/(1-r^2)) * driftWeight k r) r := by
  unfold driftWeight
  scalar_deriv
  grind [Real.rpow_sub_one]

@[fun_prop] theorem continuousOn_driftWeight (k : ℝ) : ContinuousOn (driftWeight k) (Ico 0 1) :=
  fun r hr ↦ (driftWeight_hasDerivAt k (square_lt_one hr)).continuousAt.continuousWithinAt

/-- First and second radial derivatives in the open interval; only the first
derivative and the function itself need to extend continuously to zero. -/
structure Ray where
  v : ℝ → ℝ
  d : ℝ → ℝ
  e : ℝ → ℝ
  cont : ContinuousOn v radii
  contD : ContinuousOn d radii
  jet : ∀ r ∈ unitInterval, JetAt v d (e r) r

attribute [fun_prop] Ray.cont Ray.contD

theorem radial_antitone {f : ℝ → ℝ} (hc : ContinuousOn f radii)
    (h : ∀ r ∈ unitInterval, ∃ d ≤ 0, HasDerivAt f d r) : AntitoneOn f radii := by
  apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1) hc <;> rw [interior_Ico] <;>
    intro r hr <;> obtain ⟨d,hd,H⟩ := h r hr
  · exact H.differentiableAt.differentiableWithinAt
  · rwa [H.deriv]

namespace Ray

noncomputable def err (A : Ray) (k x : ℝ) := A.e x - rhs k x (A.v x) (A.d x)

/-- One weighted Wronskian treats both ordinary comparison (`b = a`) and
Euler's complementary parameters (`a+b = 2`). In the latter case the
extra logarithmic derivative accounts for the factor `(1-x²)^((a-b)/2)`. -/
theorem compare (A B : Ray) (a b c s : ℝ) (shift : 2*c = a-b) (params : c*(a+b-2) = 0)
    (pos : ∀ r ∈ radii, 0 < B.v r)
    (sub : ∀ r ∈ unitInterval, s*(B.v r*A.err a r - A.v r*B.err b r) ≤ 0) :
    AntitoneOn (fun r ↦ s * driftWeight c r * A.v r / B.v r) radii := by
  let w := driftWeight ((a+b)/2)
  let v := driftWeight c
  let D r := A.d r*B.v r - A.v r*B.d r - (a-b)*r/(1-r^2)*A.v r*B.v r
  let P r := r*w r*(s*D r)
  have nz r (hr : r ∈ radii) := (sub_pos.mpr (square_lt_one hr)).ne'
  have H : AntitoneOn P radii := by
    apply radial_antitone (by fun_prop)
    intro r hr
    have := driftWeight_pos ((a+b)/2) (inner_sq hr)
    refine ⟨r*w r*(s*(B.v r*A.err a r-A.v r*B.err b r)), mul_nonpos_of_nonneg_of_nonpos (by have := hr.1; positivity) (sub r hr), ?_⟩
    have hr' := nz r (Ioo_subset_Ico_self hr)
    ; scalar_deriv [(A.jet r hr).1,(A.jet r hr).2,(B.jet r hr).1,(B.jet r hr).2,driftWeight_hasDerivAt ((a+b)/2) (inner_sq hr)]
    dsimp only [err,rhs]; field_simp; grind
  apply radial_antitone (by fun_prop (disch := grind))
  intro r hr
  have hp := driftWeight_pos c (inner_sq hr)
  have h := H (by simp) (Ioo_subset_Ico_self hr) hr.1.le
  simp [P] at h
  have hd := nonpos_of_mul_nonpos_right h (mul_pos hr.1 (driftWeight_pos ((a+b)/2) (inner_sq hr)))
  have hb := (pos r (Ioo_subset_Ico_self hr)).ne'
  refine ⟨v r*(s*D r)/B.v r^2, div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _), ?_⟩
  scalar_deriv [(A.jet r hr).1,(B.jet r hr).1,driftWeight_hasDerivAt c (inner_sq hr)]
  grind

end Ray
end BergmanWeakType.Weighted
