/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.PolarKernel
import BergmanWeakType.Weighted.AngularMean
import Mathlib.Tactic
import BergmanWeakType.Derivative

variable {r : ℝ}

/-! # Polar differential equations under compact source integrals -/



noncomputable section

open MeasureTheory Set


namespace BergmanWeakType.Weighted

abbrev PolarFamily := ℂ → PolarField

variable {X : Type*} [TopologicalSpace X]

@[fun_prop] theorem continuousOn_polarKernel {Y : Type*} [TopologicalSpace Y]
    {S : Set Y} {a : Y → ℂ} {r θ : Y → ℝ} (q)
    (ha : ContinuousOn a S)
    (hr : ContinuousOn r S) (hθ : ContinuousOn θ S)
    (hsource : ∀ w ∈ S, ‖a w‖ ^ 2 ≤ 1)
    (hunit : ∀ w ∈ S, r w ^ 2 < 1) :
    ContinuousOn (fun w ↦ polarKernel q (a w) (r w) (θ w)) S := by
  apply ContinuousOn.rpow_const
  · fun_prop [polarDenominator, radialComponent]
  · intro p hp
    exact Or.inl (polarDenominator_pos (hunit p hp) (hsource p hp) _).ne'

macro "polar_cont" : tactic => `(tactic|
  fun_prop (disch := grind)
    [polarKernelR, polarKernelRR, polarKernelT, polarKernelTT,
    radialComponent, angularComponent, polarDenominator])

section Integration

variable [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

def polarIntegral (H : PolarFamily) (a : X → ℂ)
    (μ : Measure X) (f : X → ℝ) (r θ : ℝ) : ℝ :=
  ∫ w, H (a w) r θ * f w ∂μ

variable {K : Set X} {a : X → ℂ} {μ : Measure X} {f : X → ℝ} (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hf : Integrable f μ)

local notation "P" => (fun H ↦ polarIntegral H a μ f)

include hK hμ hf

variable (ha : ContinuousOn a K) (hsource : ∀ w ∈ K, ‖a w‖ ^ 2 ≤ 1)

include ha hsource

theorem polarIntegral_regular (q ) :
    PolarRegularity (P (polarKernel q))
      (P (polarKernelR q))
      (P (polarKernelRR q))
      (P (polarKernelT q))
      (P (polarKernelTT q)) := by
  have hr2 (r ) (hr : r ∈ unitIoo) := (sq_lt_one_iff₀ hr.1.le).mpr hr.2
  constructor
  all_goals try
    refine (continuousOn_integral_mul_of_compact hK hμ hf
      (S := {p : ℝ × ℝ | p.1 ^ 2 < 1}) ?_).mono ?_
    · polar_cont
    · rintro ⟨r, θ⟩ ⟨hr, _⟩
      exact (sq_lt_one_iff₀ hr.1).mpr hr.2
  all_goals try
    intro r hr θ
    first
    | unfold polarIntegral
      apply hasDerivAt_integral_mul_of_continuousOn_nhds hK hμ
        ((isOpen_lt (continuous_pow 2) continuous_const).mem_nhds (hr2 r hr)) hf
      all_goals try polar_cont
      intro w hw s hs
      have hp := polarDenominator_pos hs (hsource w hw) θ
    | unfold polarIntegral
      apply hasDerivAt_integral_mul_of_continuousOn_nhds hK hμ  (x := θ)
        Filter.univ_mem hf
      all_goals try polar_cont
      intro w hw t ht
      have hs := hr2 r hr
      have hp := polarDenominator_pos hs (hsource w hw) t
    dsimp [polarKernel, polarKernelR, polarKernelRR, polarKernelT, polarKernelTT,
      polarDenominator, radialComponent, angularComponent] at *
    differentiate
  · simp [polarIntegral, polarKernelT, polarKernel, polarDenominator, radialComponent,
      angularComponent]

def polarIntegral_operator (k q) (hr : r ^ 2 < 1) (θ) :=
  (show (∫ w, polarOperator k r (polarKernel q (a w) r θ)
    (polarKernelR q (a w) r θ) (polarKernelRR q (a w) r θ)
    (polarKernelTT q (a w) r θ) * f w ∂μ) = polarOperator k r (P _ r θ) (P _ r θ) (P _ r θ) (P _ r θ) from by
  simp (disch := with_unfolding_all
    (apply_rules [Integrable.add, Integrable.neg, Integrable.div_const, Integrable.const_mul,
      integrable_mul_of_continuousOn_compact hK hμ hf] <;> polar_cont)) only
    [polarOperator, sub_mul, add_mul, div_mul_eq_mul_div, mul_assoc, polarIntegral,
      integral_add, integral_sub, integral_div, integral_const_mul]
  rfl).symm


end Integration

theorem monotoneOn_angularMean_polarKernel (q) (w : ℂ) (hw : ‖w‖ ^ 2 ≤ 1) :
    MonotoneOn (angularMean (polarKernel q w)) unitIco :=
  by
  have hreg := polarIntegral_regular (K := {0})  
    (μ := Measure.dirac 0)  isCompact_singleton (by simp)
    (integrable_const (-1)) continuousOn_const (fun _ _ ↦ hw) q
  unfold polarIntegral at hreg
  simp at hreg
  have h :=
    antitoneOn_angularMean_of_polar_flux (w := fun _ ↦ 1)  hreg
      continuousOn_const (fun _ _ ↦ hasDerivAt_const _ _) (by continuity) ?_
  · intro r hr s hs hrs
    simpa [angularMean, intervalIntegral.integral_neg] using h hr hs hrs
  intro r hr θ
  have hd := polarDenominator_pos ((sq_lt_one_iff₀ hr.1.le).mpr hr.2) hw θ
  have hn : 0 ≤ polarKernelRR q w r θ + polarKernelR q w r θ / r + polarKernelTT q w r θ / r ^ 2 :=
    by
    rw [polarKernel_laplacian q w r θ hd hr.1.ne']
    unfold polarKernel
    positivity
  convert neg_nonpos.mpr (mul_nonneg hr.1.le hn) using 1 <;> field_simp [hr.1.ne'] <;> ring

end BergmanWeakType.Weighted
