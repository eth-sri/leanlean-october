/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.CompactIntegral
public import BergmanWeakType.Measure
public import BergmanWeakType.Weighted.PolarField
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-! # Pure radial and angular derivatives of the weighted kernel -/

@[expose] public section

noncomputable section

open Real
open scoped Topology

namespace BergmanWeakType.Weighted

open Part

variable (w : ClosedDisk) (r θ : ℝ)

def radialComponent := w.val.re * cos θ + w.val.im * sin θ
def angularComponent := w.val.im * cos θ - w.val.re * sin θ

theorem unit_sq : ‖w.val‖^2 ≤ 1 := by
  have : ‖w.val‖ ≤ 1 := by grind [Metric.mem_closedBall, dist_zero_right]
  simp_all

theorem component_norm_sq : angularComponent w θ ^ 2 = ‖w.val‖^2 - radialComponent w θ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold angularComponent radialComponent
  grind [sin_sq_add_cos_sq]

def polarDenominator := ‖w.val‖^2 * r^2 - 2*r*radialComponent w θ + 1

theorem polarDenominator_pos (hr : r^2 < 1) : 0 < polarDenominator w r θ := by
  have := component_norm_sq w θ
  have := unit_sq w
  have : r * radialComponent w θ < 1 := by nlinarith
  unfold polarDenominator; nlinarith

def denominatorJet : Jet
  | .v => polarDenominator w r θ
  | .r => 2*(‖w.val‖^2*r-radialComponent w θ)
  | .rr => 2*‖w.val‖^2
  | .t => -2*r*angularComponent w θ
  | .tt => 2*r*radialComponent w θ

/-- Kernel and all its pure partials, obtained by powering the denominator jet. -/
def column (q : ℝ) (i : Part) (p : ℝ × ℝ) (w : ClosedDisk) :=
  (denominatorJet w p.1 p.2).map (·^q) (fun x ↦ q*x^(q-1)) (fun x ↦ q*(q-1)*x^(q-1-1)) i

private theorem powerJet (q : ℝ) {x : ℝ} (hp : 0 < x) :
    JetAt (·^q) (fun u ↦ q*u^(q-1)) (q*(q-1)*x^(q-1-1)) x := by
  constructor <;> scalar_deriv <;> ring

theorem column_jet (q : ℝ) (l : Slice) (u : ℝ) (hu : (l.point u).1^2 < 1) :
    l.jet (fun p i ↦ column q i p w) u := by
  apply l.chain (J := fun p ↦ denominatorJet w p.1 p.2) _ (powerJet q (polarDenominator_pos _ _ _ hu))
  cases l <;> constructor <;> dsimp [Slice.point,Slice.first,Slice.second,denominatorJet,polarDenominator,radialComponent,angularComponent] <;>
    scalar_deriv [hasDerivAt_cos,hasDerivAt_sin] <;> ring

abbrev cylinder := {p : ℝ × ℝ | p.1^2 < 1}

theorem column_continuous (q : ℝ) (i : Part) : ContinuousOn (column q i).uncurry (cylinder ×ˢ Set.univ) := by
  have hk (a : ℝ) : ContinuousOn (fun p  ↦ polarDenominator p.2 p.1.1 p.1.2 ^ a) (cylinder ×ˢ Set.univ) :=
    ContinuousOn.rpow_const (by unfold polarDenominator radialComponent; fun_prop) (by grind [polarDenominator_pos])
  unfold Function.uncurry column
  cases i <;> dsimp [Jet.map,denominatorJet,radialComponent,angularComponent] <;> fun_prop

theorem column_period (q : ℝ) (i : Part) : column q i (r,π) w = column q i (r,-π) w := by
  simp_all [column, Jet.map, denominatorJet, polarDenominator, radialComponent, angularComponent]

/-- The error vanishes on the boundary, and is nonpositive throughout the closed disk. -/
theorem column_equation (k : ℝ) (hr : r^2 < 1) (hn : r ≠ 0) :
    Jet.error (fun i ↦ column (-k/2) i (r,θ) w) k r =
      -(k^2*(1-‖w.val‖^2))/((1-r^2)*polarDenominator w r θ) * column (-k/2) .v (r,θ) w := by
  have hd := (polarDenominator_pos w r θ hr).ne'
  simp [Jet.error,rhs,column,Jet.map,denominatorJet,rpow_sub_one hd]
  field_simp [(sub_pos.mpr hr).ne']
  ; grind [component_norm_sq, polarDenominator]

theorem polarDenominator_eq_norm_sq : polarDenominator w r θ = ‖1 - circleMap 0 r θ * star w.val‖^2 := by
  simp [polarDenominator, radialComponent, Complex.sq_norm, Complex.normSq_apply, circleMap_zero_re, circleMap_zero_im]
  grind [cos_sq_add_sin_sq]

theorem column_val (α : ℝ) : column (-(α+2)/2) .v (r,θ) w = ‖weightedKernel α (circleMap 0 r θ) w.val‖ := by
  change polarDenominator w r θ ^ _ = _
  rw [polarDenominator_eq_norm_sq, norm_weightedKernel, ← rpow_natCast_mul (norm_nonneg _) 2]
  ring

end BergmanWeakType.Weighted
