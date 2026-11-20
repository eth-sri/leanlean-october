/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Pure two-jets on the polar cylinder -/
@[expose] public section
noncomputable section
open Real Set

namespace BergmanWeakType.Weighted

/-- Only the pure derivatives appear in the polar equation. -/
inductive Part | v | r | rr | t | tt
open Part
abbrev Jet := Part → ℝ
abbrev PolarFn := ℝ → ℝ → ℝ
/-- The scalar chain rule, simultaneously in both directions. -/
def Jet.map (a : Jet) (g d e : ℝ → ℝ) : Jet :=
  let D i := d (a v) * a i
  let E i j := e (a v) * a i * a i + d (a v) * a j
  fun | v => g (a v) | r => D r | rr => E r rr | t => D t | tt => E t tt

def rhs (k x f d : ℝ) := (2*k*x/(1-x^2)-1/x)*d + k^2/(1-x^2)*f

def Jet.error (a : Jet) (k x : ℝ) := a rr + a tt/x^2 - rhs k x (a v) (a r)

/-- A coordinate line, labeled by its fixed coordinate. -/
inductive Slice | rad (θ : ℝ) | ang (x : ℝ)

def Slice.point : Slice → ℝ → ℝ × ℝ
  | .rad θ, u => (u,θ)
  | .ang x, u => (x,u)

def Slice.first : Slice → Part | .rad _ => .r | .ang _ => .t
def Slice.second : Slice → Part | .rad _ => .rr | .ang _ => .tt

@[fun_prop] theorem Slice.cont (l : Slice) : Continuous l.point := by cases l <;> unfold point <;> fun_prop

abbrev Slice.jet (l : Slice) (J : ℝ × ℝ → Jet) (x : ℝ) :=
  JetAt (fun u ↦ J (l.point u) .v) (fun u ↦ J (l.point u) l.first) (J (l.point x) l.second) x

theorem Slice.chain (l : Slice) {J : ℝ × ℝ → Jet} {x : ℝ} (h : l.jet J x) {g d e : ℝ → ℝ}
    (hg : JetAt g d (e (J (l.point x) .v)) (J (l.point x) .v)) :
    l.jet (fun p ↦ (J p).map g d e) x := by cases l <;> exact h.comp hg

/-- A regular polar field with matching angular edge values. -/
structure Field where
  get : ℝ × ℝ → Jet
  cont : ∀ i, ContinuousOn (fun p ↦ get p i) (radii ×ˢ univ)
  jet : ∀ (l : Slice) x, (l.point x).1^2 < 1 → l.jet get x
  period : ∀ i x, get (x,π) i = get (x,-π) i

namespace Field
abbrev eval (F : Field) (r t : ℝ) := F.get (r,t)
abbrev val (F : Field) (i : Part) (r t : ℝ) := F.eval r t i

def subScaled (F H : Field) (c : ℝ) : Field where
  get p i := F.get p i - c*H.get p i
  cont i := (F.cont i).sub ((H.cont i).const_mul c)
  jet l x h := (F.jet l x h).sub_mul (H.jet l x h) c
  period i x := by rw [F.period, H.period]

theorem error_subScaled (F H : Field) (c k x θ : ℝ) :
    ((F.subScaled H c).eval x θ).error k x = (F.eval x θ).error k x - c*(H.eval x θ).error k x := by
  grind [Jet.error, rhs, subScaled]

def comp (F : Field) {g d e : ℝ → ℝ} (h : ∀ x, JetAt g d (e x) x) (ce : Continuous e) : Field where
  get p := (F.get p).map g d e
  cont i := by
    have cg := continuous_iff_continuousAt.mpr fun x ↦ (h x).1.continuousAt
    have cd := continuous_iff_continuousAt.mpr fun x ↦ (h x).2.continuousAt
    have H := F.cont
    cases i <;> dsimp [Jet.map] <;> fun_prop
  jet l x hx := l.chain (F.jet l x hx) (h _)
  period i x := congrArg (fun a : Jet ↦ a.map g d e i) (funext fun j ↦ F.period j x)

end Field
end BergmanWeakType.Weighted
