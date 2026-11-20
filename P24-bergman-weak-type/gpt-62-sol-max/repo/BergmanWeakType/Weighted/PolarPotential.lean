/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Weighted.AngleMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-! # Polar differential equations under compact source integrals -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType.Weighted

def radialComponent (w : ℂ) (θ : ℝ) : ℝ := w.re * cos θ + w.im * sin θ
def angularComponent (w : ℂ) (θ : ℝ) : ℝ := w.im * cos θ - w.re * sin θ

private theorem radialComponent_hasDerivAt (w : ℂ) (θ : ℝ) :
    HasDerivAt (radialComponent w) (angularComponent w θ) θ := by
  convert ((hasDerivAt_cos θ).const_mul w.re).add ((hasDerivAt_sin θ).const_mul w.im) using 1
  · rfl
  · unfold angularComponent; ring

private theorem angularComponent_hasDerivAt (w : ℂ) (θ : ℝ) :
    HasDerivAt (angularComponent w) (-radialComponent w θ) θ := by
  convert ((hasDerivAt_cos θ).const_mul w.im).sub ((hasDerivAt_sin θ).const_mul w.re) using 1
  · rfl
  · unfold radialComponent; ring

def polarDenominator (w : ℂ) (r θ : ℝ) : ℝ := (‖w‖ ^ 2 * r ^ 2 + 1) + (-2 * r) * radialComponent w θ

theorem polarDenominator_eq_norm_sq (w : ℂ) (r θ : ℝ) :
    polarDenominator w r θ = ‖1 - circleMap 0 r θ * star w‖ ^ 2 := by
  have hn : ‖circleMap 0 r θ * star w‖ ^ 2 = r ^ 2 * ‖w‖ ^ 2 := by
    simp [mul_pow]
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq, norm_one, one_pow, hn, one_mul]
  simp only [Complex.conj_re,
    Complex.mul_re, Complex.star_def, Complex.conj_im,
    circleMap_zero_re, circleMap_zero_im, polarDenominator, radialComponent]
  ring

theorem polarDenominator_pos {w : ℂ} {r : ℝ} (hr : r ^ 2 < 1)
    (hw : ‖w‖ ≤ 1) (θ : ℝ) : 0 < polarDenominator w r θ := by
  rw [polarDenominator_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (kernel_denominator_ne_zero
    (by simp_all) hw))

/-- The two coordinate directions in polar coordinates. -/
inductive Axis | radial | angular

abbrev Axis.slice {A : Type*} (d : Axis) (f : ℝ → ℝ → A) (r θ : ℝ) : ℝ → A :=
  match d with
  | .radial => (f · θ)
  | .angular => f r

abbrev Axis.coord (d : Axis) (r θ : ℝ) : ℝ := match d with
  | .radial => r
  | .angular => θ

abbrev Axis.HasDeriv (d : Axis) (F G : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop :=
  HasDerivAt (d.slice F r θ) (G r θ) (d.coord r θ)

def polarDenominatorD (d : Axis) (w : ℂ) (r θ : ℝ) : ℝ :=
  match d with
  | .radial => 2 * (‖w‖ ^ 2 * r - radialComponent w θ)
  | .angular => -2 * r * angularComponent w θ

def polarDenominatorDD (d : Axis) (w : ℂ) (r θ : ℝ) : ℝ :=
  match d with
  | .radial => 2 * ‖w‖ ^ 2
  | .angular => 2 * r * radialComponent w θ

def polarKernel (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ := polarDenominator w r θ ^ q

def polarKernelD (d : Axis) (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ :=
  polarDenominatorD d w r θ * q * polarKernel (q - 1) w r θ

def polarKernelDD (d : Axis) (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ :=
  polarDenominatorDD d w r θ * q * polarKernel (q - 1) w r θ +
    polarDenominatorD d w r θ * q * polarKernelD d (q - 1) w r θ

private theorem den_hasDerivAt (d : Axis) (w : ℂ) (r θ : ℝ) :
    d.HasDeriv (polarDenominator w) (polarDenominatorD d w) r θ := by
  cases d
  · have h := hasDerivAt_id r
    convert (((h.pow 2).const_mul (‖w‖ ^ 2)).add_const 1).add
      ((h.const_mul (-2)).mul_const (radialComponent w θ)) using 1
    · rfl
    simp [polarDenominatorD]; ring
  · exact ((radialComponent_hasDerivAt w θ).const_mul (-2 * r)).const_add _

private theorem denD_hasDerivAt (d : Axis) (w : ℂ) (r θ : ℝ) :
    d.HasDeriv (polarDenominatorD d w) (polarDenominatorDD d w) r θ := by
  cases d
  · unfold Axis.HasDeriv Axis.slice Axis.coord polarDenominatorD polarDenominatorDD
    simpa using (((hasDerivAt_id r).const_mul (‖w‖ ^ 2)).sub_const (radialComponent w θ)).const_mul 2
  · convert (angularComponent_hasDerivAt w θ).const_mul (-2 * r) using 1
    · rfl
    · simp [polarDenominatorDD]

theorem polarKernel_hasDerivAt (d : Axis) (q : ℝ) (w : ℂ) (r θ : ℝ) (h : 0 < polarDenominator w r θ) :
    d.HasDeriv (polarKernel q w) (polarKernelD d q w) r θ := by
  have hd := den_hasDerivAt d w r θ
  cases d <;> exact hd.rpow_const (p := q) (Or.inl h.ne')

theorem polarKernelD_hasDerivAt (d : Axis) (q : ℝ) (w : ℂ) (r θ : ℝ) (h : 0 < polarDenominator w r θ) :
    d.HasDeriv (polarKernelD d q w) (polarKernelDD d q w) r θ := by
  have hd := denD_hasDerivAt d w r θ
  have hk := polarKernel_hasDerivAt d (q - 1) w r θ h
  cases d <;> exact (hd.mul_const q).mul hk

def radialCoeff (k r : ℝ) : ℝ := 1 - (2 * k + 1) * r ^ 2

/-- The weighted elliptic operator multiplied by `r * (1 - r²)`. -/
def polarOperator (k r F Fr Frr Ftt : ℝ) : ℝ :=
  r * (1 - r ^ 2) * Frr + radialCoeff k r * Fr + ((1 - r ^ 2) / r) * Ftt - k ^ 2 * r * F

theorem polarKernel_eq_norm_weightedKernel (α r θ : ℝ) (w : ℂ) :
    polarKernel (-(α + 2) / 2) w r θ = ‖weightedKernel α (circleMap 0 r θ) w‖ := by
  rw [polarKernel, polarDenominator_eq_norm_sq, norm_weightedKernel,
    ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  congr 1
  ring

lemma continuousOn_radialRpow (k : ℝ) : ContinuousOn (fun r : ℝ ↦ (1 - r ^ 2) ^ k) (radii) :=
  ContinuousOn.rpow_const (by fun_prop) fun _ hx ↦ Or.inl (radial_defect_pos hx).ne'

/-- A finite source measure supported in the closed disk. -/
structure PolarSource where
  μ : Measure ℂ
  supported : ∀ᵐ w ∂μ, w ∈ Metric.closedBall 0 1
  finite : IsFiniteMeasure μ

attribute [instance] PolarSource.finite

namespace PolarSource

abbrev Kernel := ℂ → ℝ → ℝ → ℝ

abbrev eval (H : Kernel) (p : (ℝ × ℝ) × ℂ) : ℝ := H p.2 p.1.1 p.1.2

abbrev ContinuousKernel (H : Kernel) : Prop :=
  ContinuousOn (eval H) {p | p.1.1 ^ 2 < 1 ∧ p.2 ∈ Metric.closedBall 0 1}

private theorem den_pos {r : ℝ} (hr : r ^ 2 < 1) {w : ℂ}
    (hw : w ∈ Metric.closedBall 0 1) (θ : ℝ) : 0 < polarDenominator w r θ :=
  polarDenominator_pos hr (by simpa using hw) θ

theorem cont_kernel (q : ℝ) : ContinuousKernel (polarKernel q) := by
  unfold ContinuousKernel eval at *
  unfold polarKernel polarDenominator radialComponent
  apply ContinuousOn.rpow_const (by fun_prop)
  exact fun p hp ↦ Or.inl (den_pos hp.1 hp.2 _).ne'

theorem cont_kernelD (d : Axis) (q : ℝ) : ContinuousKernel (polarKernelD d q) := by
  have h := cont_kernel (q - 1)
  unfold ContinuousKernel eval at *
  cases d <;> unfold polarKernelD polarDenominatorD radialComponent angularComponent <;> fun_prop

theorem cont_kernelDD (d : Axis) (q : ℝ) : ContinuousKernel (polarKernelDD d q) := by
  have h₁ := cont_kernel (q - 1)
  have h₂ := cont_kernelD d (q - 1)
  unfold ContinuousKernel eval at *
  cases d <;> unfold polarKernelDD polarDenominatorD polarDenominatorDD radialComponent angularComponent <;> fun_prop

variable (S : PolarSource)

def integral (H : Kernel) (r θ : ℝ) : ℝ := ∫ w, eval H ((r, θ), w) ∂S.μ

theorem integrable_kernel {H : Kernel} (hH : ContinuousKernel H)
    {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    Integrable (fun w ↦ eval H ((r, θ), w)) S.μ :=
  integrable_compact_slice (isCompact_closedBall _ _) S.supported
    (F := fun p w ↦ H w p.1 p.2) hH (show (r, θ) ∈ {p : ℝ × ℝ | p.1 ^ 2 < 1} from hr)

theorem cont_integral {H : Kernel} (hH : ContinuousKernel H) {A : Set ℝ} :
    ContinuousOn (fun p : ℝ × ℝ ↦ S.integral H p.1 p.2) (radii ×ˢ A) :=
  continuousOn_integral_of_compact_support (isCompact_closedBall _ _) S.supported
    (hH.mono fun _ h ↦ ⟨sq_lt_one_of_mem_Ico h.1.1, h.2⟩)

/-- Differentiation along either polar coordinate is the same compact-family argument. -/
private theorem integral_hasDerivAt (d : Axis) {H H' : Kernel} (hH : ContinuousKernel H)
    (hH' : ContinuousKernel H') {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ)
    (hd : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ∀ u v, u ^ 2 < 1 → d.HasDeriv (H w) (H' w) u v) :
    d.HasDeriv (S.integral H) (S.integral H') r θ := by
  let γ := d.slice Prod.mk r θ
  let D := {u : ℝ | (γ u).1 ^ 2 < 1}
  have hγ : Continuous γ := by cases d <;> fun_prop
  have hx : d.coord r θ ∈ D := by cases d <;> exact hr
  have hc {F : Kernel} (hF : ContinuousKernel F) :
      ContinuousOn (fun p : ℝ × ℂ ↦ eval F (γ p.1, p.2)) (D ×ˢ Metric.closedBall 0 1) :=
    hF.comp (f := fun p : ℝ × ℂ ↦ (γ p.1, p.2)) (by fun_prop) (fun _ h ↦ h)
  have h := hasDerivAt_integral_of_compact (isCompact_closedBall _ _) S.supported
    (S := D) (F := fun u w ↦ eval H (γ u, w)) (F' := fun u w ↦ eval H' (γ u, w))
    (isOpen_lt ((continuous_fst.comp hγ).pow 2) continuous_const) hx (hc hH) (hc hH')
    (fun w hw u hu ↦ by
      cases d
      · exact hd w hw u θ hu
      · exact hd w hw r u hu)
  cases d <;> exact h

theorem integral_kernel_hasDerivAt (d : Axis) (q : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    d.HasDeriv (S.integral (polarKernel q)) (S.integral (polarKernelD d q)) r θ :=
  S.integral_hasDerivAt d (cont_kernel q) (cont_kernelD d q) hr θ fun w hw u v hu ↦
    polarKernel_hasDerivAt d q w u v (den_pos hu hw v)

theorem integral_kernelD_hasDerivAt (d : Axis) (q : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    d.HasDeriv (S.integral (polarKernelD d q)) (S.integral (polarKernelDD d q)) r θ :=
  S.integral_hasDerivAt d (cont_kernelD d q) (cont_kernelDD d q) hr θ fun w hw u v hu ↦
    polarKernelD_hasDerivAt d q w u v (den_pos hu hw v)

/-- Apply the elliptic operator to an integrated kernel. -/
def potentialOperator (k r θ : ℝ) : ℝ :=
  polarOperator k r (S.integral (polarKernel (-k / 2)) r θ)
    (S.integral (polarKernelD .radial (-k / 2)) r θ) (S.integral (polarKernelDD .radial (-k / 2)) r θ)
    (S.integral (polarKernelDD .angular (-k / 2)) r θ)

theorem operator_eq (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (hr0 : r ≠ 0) (θ : ℝ) :
    S.potentialOperator k r θ =
        -(k ^ 2 * r) * ∫ w, (1 - ‖w‖ ^ 2) * polarKernel (-k / 2 - 1) w r θ ∂S.μ := by
  have hi {H : Kernel} (h : ContinuousKernel H) (c : ℝ) := (S.integrable_kernel h hr θ).const_mul c
  have h1 := hi (cont_kernelDD .radial (-k / 2)) (r * (1 - r ^ 2))
  have h2 := hi (cont_kernelD .radial (-k / 2)) (radialCoeff k r)
  have h3 := hi (cont_kernelDD .angular (-k / 2)) ((1 - r ^ 2) / r)
  unfold potentialOperator polarOperator integral
  simp_rw [← integral_const_mul]
  rw [← integral_add' h1 h2, ← integral_add' (h1.add h2) h3, ← integral_sub' ((h1.add h2).add h3) (hi (cont_kernel _) _)]
  apply integral_congr_ae
  filter_upwards [S.supported] with w hw
  clear h1 h2 h3
  have hd := den_pos hr hw θ
  have step (q : ℝ) : polarKernel q w r θ = polarDenominator w r θ * polarKernel (q - 1) w r θ := by
    rw [polarKernel, polarKernel, rpow_sub_one hd.ne', mul_div_cancel₀ _ hd.ne']
  have hb : angularComponent w θ ^ 2 = ‖w‖ ^ 2 - radialComponent w θ ^ 2 := by
    simp only [radialComponent, angularComponent, Complex.sq_norm, Complex.normSq_apply]
    linear_combination (w.re ^ 2 + w.im ^ 2) * (cos_sq_add_sin_sq θ)
  unfold eval polarKernelDD polarKernelD polarDenominatorD polarDenominatorDD radialCoeff
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [step (-k / 2), step (-k / 2 - 1)]
  unfold polarDenominator
  generalize polarKernel (-k / 2 - 1 - 1) w r θ = b
  grind

end PolarSource
end BergmanWeakType.Weighted
