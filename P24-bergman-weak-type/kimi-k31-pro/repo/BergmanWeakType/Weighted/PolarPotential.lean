/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarKernel

/-! # Polar differential equations under compact source integrals -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType.Weighted

variable {X : Type*} [TopologicalSpace X]

def polarSourceDomain (K : Set X) : Set ((ℝ × ℝ) × X) :=
  {p | p.1.1 ^ 2 < 1 ∧ p.2 ∈ K}

section Continuity

variable {K : Set X} {a b : X → ℝ}
  (ha : ContinuousOn a K) (hb : ContinuousOn b K)
  (hsource : ∀ w ∈ K, a w ^ 2 + b w ^ 2 ≤ 1)

include ha hb

@[fun_prop] theorem continuousOn_radialComponent_source :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ radialComponent (a p.2) (b p.2) p.1.2)
      (polarSourceDomain K) := by
  unfold radialComponent
  fun_prop

@[fun_prop] theorem continuousOn_angularComponent_source :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ angularComponent (a p.2) (b p.2) p.1.2)
      (polarSourceDomain K) := by
  unfold angularComponent
  fun_prop

@[fun_prop] theorem continuousOn_polarDenominator_source :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ polarDenominator (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K) := by
  unfold polarDenominator
  fun_prop

include hsource

@[fun_prop] theorem continuousOn_polarKernel_source (q : ℝ) :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ polarKernel q (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K) := by
  apply (continuousOn_polarDenominator_source ha hb).rpow_const
  exact fun p hp ↦ .inl (polarDenominator_pos hp.1 (hsource p.2 hp.2) p.1.2).ne'

@[fun_prop] theorem continuousOn_polarKernelR_source (q : ℝ) :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ polarKernelR q (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K) := by
  unfold polarKernelR
  fun_prop

@[fun_prop] theorem continuousOn_polarKernelRR_source (q : ℝ) :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ polarKernelRR q (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K) := by
  unfold polarKernelRR
  fun_prop

@[fun_prop] theorem continuousOn_polarKernelT_source (q : ℝ) :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ polarKernelT q (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K) := by
  unfold polarKernelT
  fun_prop

@[fun_prop] theorem continuousOn_polarKernelTT_source (q : ℝ) :
    ContinuousOn (fun p : (ℝ × ℝ) × X ↦ polarKernelTT q (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K) := by
  unfold polarKernelTT
  fun_prop

end Continuity

section Integration

variable [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

def polarIntegral (H : ℝ → ℝ → ℝ → ℝ → ℝ) (a b : X → ℝ)
    (μ : Measure X) (f : X → ℝ) (r θ : ℝ) : ℝ :=
  ∫ w, H (a w) (b w) r θ * f w ∂μ

variable {K : Set X} {a b : X → ℝ} {μ : Measure X} {f : X → ℝ}
  (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hf : Integrable f μ)

include hK hμ hf

theorem integrable_polarIntegral_kernel {H : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun p : (ℝ × ℝ) × X ↦ H (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K)) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    Integrable (fun w ↦ H (a w) (b w) r θ * f w) μ := by
  apply integrable_mul_of_continuousOn_compact hK hμ hf
  exact hH.comp ((continuous_const (y := (r, θ))).prodMk continuous_id).continuousOn
    (fun w hw ↦ ⟨hr, hw⟩)

theorem continuousOn_polarIntegral_unit {H : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun p : (ℝ × ℝ) × X ↦ H (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K)) :
    ContinuousOn (fun p : ℝ × ℝ ↦ polarIntegral H a b μ f p.1 p.2)
      (Ico 0 1 ×ˢ univ) := by
  apply ContinuousOn.mono (s := {p : ℝ × ℝ | p.1 ^ 2 < 1})
  · intro p hp
    obtain ⟨S, hS, hpS, hsub⟩ := exists_compact_subset
      (isOpen_lt (continuous_fst.pow 2) continuous_const) hp
    exact ((continuousOn_integral_mul_of_compact hK hμ hS hf
      (hH.mono fun p hp ↦ ⟨hsub hp.1, hp.2⟩)).continuousAt
      (mem_interior_iff_mem_nhds.mp hpS)).continuousWithinAt
  · rintro ⟨r, θ⟩ ⟨hr, _⟩
    exact (sq_lt_one_iff_abs_lt_one r).mpr (abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩)

theorem polarIntegral_hasDerivAt_r {H H' : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun p : (ℝ × ℝ) × X ↦ H (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K))
    (hH' : ContinuousOn (fun p : (ℝ × ℝ) × X ↦ H' (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K))
    (hd : ∀ w ∈ K, ∀ r θ : ℝ, r ^ 2 < 1 →
      HasDerivAt (fun u ↦ H (a w) (b w) u θ) (H' (a w) (b w) r θ) r)
    {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun u ↦ polarIntegral H a b μ f u θ) (polarIntegral H' a b μ f r θ) r := by
  obtain ⟨S, hS, hSr, htarget⟩ := exists_coordinate_interval (show r ^ 2 + 0 ^ 2 < 1 by simpa using hr)
  have hmap : MapsTo (fun p : ℝ × X ↦ ((p.1, θ), p.2)) (S ×ˢ K) (polarSourceDomain K) := by
    intro p hp
    exact ⟨by simpa using htarget p.1 hp.1, hp.2⟩
  have hcont : Continuous (fun p : ℝ × X ↦ ((p.1, θ), p.2)) :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  exact (hasDerivAt_integral_mul_of_continuousOn_compact hK hμ hS hSr hf
    (hH.comp hcont.continuousOn hmap) (hH'.comp hcont.continuousOn hmap)
    (fun w hw u hu ↦ hd w hw u θ (by simpa using htarget u hu))).2

theorem polarIntegral_hasDerivAt_t {H H' : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun p : (ℝ × ℝ) × X ↦ H (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K))
    (hH' : ContinuousOn (fun p : (ℝ × ℝ) × X ↦ H' (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K))
    (hd : ∀ w ∈ K, ∀ r θ : ℝ, r ^ 2 < 1 →
      HasDerivAt (H (a w) (b w) r) (H' (a w) (b w) r θ) θ)
    {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (polarIntegral H a b μ f r) (polarIntegral H' a b μ f r θ) θ := by
  have hmap : MapsTo (fun p : ℝ × X ↦ ((r, p.1), p.2))
      (Metric.closedBall θ 1 ×ˢ K) (polarSourceDomain K) := fun _ hp ↦ ⟨hr, hp.2⟩
  have hcont : Continuous (fun p : ℝ × X ↦ ((r, p.1), p.2)) :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  exact (hasDerivAt_integral_mul_of_continuousOn_compact hK hμ (isCompact_closedBall θ 1)
    (Metric.closedBall_mem_nhds θ (by norm_num)) hf
    (hH.comp hcont.continuousOn hmap) (hH'.comp hcont.continuousOn hmap)
    (fun w hw u _ ↦ hd w hw r u hr)).2

variable (ha : ContinuousOn a K) (hb : ContinuousOn b K)
  (hsource : ∀ w ∈ K, a w ^ 2 + b w ^ 2 ≤ 1)

include ha hb hsource

theorem polarIntegral_kernel_hasDerivAt_r (q : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun u ↦ polarIntegral (polarKernel q) a b μ f u θ)
      (polarIntegral (polarKernelR q) a b μ f r θ) r :=
  polarIntegral_hasDerivAt_r hK hμ hf
    (continuousOn_polarKernel_source ha hb hsource q)
    (continuousOn_polarKernelR_source ha hb hsource q)
    (fun w hw s t hs ↦ polarKernel_hasDerivAt_r q (a w) (b w) s t
      (polarDenominator_pos hs (hsource w hw) t)) hr θ

theorem polarIntegral_kernelR_hasDerivAt_r (q : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun u ↦ polarIntegral (polarKernelR q) a b μ f u θ)
      (polarIntegral (polarKernelRR q) a b μ f r θ) r :=
  polarIntegral_hasDerivAt_r hK hμ hf
    (continuousOn_polarKernelR_source ha hb hsource q)
    (continuousOn_polarKernelRR_source ha hb hsource q)
    (fun w hw s t hs ↦ polarKernelR_hasDerivAt_r q (a w) (b w) s t
      (polarDenominator_pos hs (hsource w hw) t)) hr θ

theorem polarIntegral_kernel_hasDerivAt_t (q : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (polarIntegral (polarKernel q) a b μ f r)
      (polarIntegral (polarKernelT q) a b μ f r θ) θ :=
  polarIntegral_hasDerivAt_t hK hμ hf
    (continuousOn_polarKernel_source ha hb hsource q)
    (continuousOn_polarKernelT_source ha hb hsource q)
    (fun w hw s t hs ↦ polarKernel_hasDerivAt_t q (a w) (b w) s t
      (polarDenominator_pos hs (hsource w hw) t)) hr θ

theorem polarIntegral_kernelT_hasDerivAt_t (q : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (polarIntegral (polarKernelT q) a b μ f r)
      (polarIntegral (polarKernelTT q) a b μ f r θ) θ :=
  polarIntegral_hasDerivAt_t hK hμ hf
    (continuousOn_polarKernelT_source ha hb hsource q)
    (continuousOn_polarKernelTT_source ha hb hsource q)
    (fun w hw s t hs ↦ polarKernelT_hasDerivAt_t q (a w) (b w) s t
      (polarDenominator_pos hs (hsource w hw) t)) hr θ

theorem polarIntegral_operator (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    polarOperator k (polarIntegral (polarKernelRR (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernelR (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernelTT (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernel (-k / 2)) a b μ f r θ) r =
    ∫ w, polarOperator k (polarKernelRR (-k / 2) (a w) (b w) r θ)
      (polarKernelR (-k / 2) (a w) (b w) r θ) (polarKernelTT (-k / 2) (a w) (b w) r θ)
      (polarKernel (-k / 2) (a w) (b w) r θ) r * f w ∂μ := by
  have h0 := integrable_polarIntegral_kernel hK hμ hf
    (continuousOn_polarKernel_source ha hb hsource (-k / 2)) hr θ
  have h1 := integrable_polarIntegral_kernel hK hμ hf
    (continuousOn_polarKernelR_source ha hb hsource (-k / 2)) hr θ
  have h2 := integrable_polarIntegral_kernel hK hμ hf
    (continuousOn_polarKernelRR_source ha hb hsource (-k / 2)) hr θ
  have h3 := integrable_polarIntegral_kernel hK hμ hf
    (continuousOn_polarKernelTT_source ha hb hsource (-k / 2)) hr θ
  have heq (w : X) : (polarOperator k (polarKernelRR (-k / 2) (a w) (b w) r θ)
      (polarKernelR (-k / 2) (a w) (b w) r θ) (polarKernelTT (-k / 2) (a w) (b w) r θ)
      (polarKernel (-k / 2) (a w) (b w) r θ) r) * f w =
      polarKernelRR (-k / 2) (a w) (b w) r θ * f w +
      (polarKernelR (-k / 2) (a w) (b w) r θ * f w) / r +
      (polarKernelTT (-k / 2) (a w) (b w) r θ * f w) / r ^ 2 -
      (2 * k * r / (1 - r ^ 2)) * (polarKernelR (-k / 2) (a w) (b w) r θ * f w) -
      (k ^ 2 / (1 - r ^ 2)) * (polarKernel (-k / 2) (a w) (b w) r θ * f w) := by
    unfold polarOperator
    ring
  unfold polarOperator at heq ⊢
  simp_rw [heq]
  have hs1 := integral_add h2 (h1.div_const r)
  have hs2 := integral_add (h2.add (h1.div_const r)) (h3.div_const (r ^ 2))
  have hs3 := integral_sub ((h2.add (h1.div_const r)).add (h3.div_const (r ^ 2)))
    (h1.const_mul (2 * k * r / (1 - r ^ 2)))
  have hs4 := integral_sub (((h2.add (h1.div_const r)).add (h3.div_const (r ^ 2))).sub
    (h1.const_mul (2 * k * r / (1 - r ^ 2)))) (h0.const_mul (k ^ 2 / (1 - r ^ 2)))
  simp only [Pi.add_apply, Pi.sub_apply] at hs1 hs2 hs3 hs4
  rw [hs4, hs3, hs2, hs1]
  simp only [integral_div, integral_const_mul, polarIntegral]

theorem polarIntegral_operator_nonpos (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1)
    (hr0 : r ≠ 0) (θ : ℝ) (hfn : ∀ᵐ w ∂μ, 0 ≤ f w) :
    polarOperator k (polarIntegral (polarKernelRR (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernelR (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernelTT (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernel (-k / 2)) a b μ f r θ) r ≤ 0 := by
  rw [polarIntegral_operator hK hμ hf ha hb hsource k hr θ]
  apply integral_nonpos_of_ae
  filter_upwards [hμ, hfn] with w hw hfw
  exact mul_nonpos_of_nonpos_of_nonneg (polarKernel_equation_nonpos k (a w) (b w) r θ
    (polarDenominator_pos hr (hsource w hw) θ) hr0 (sub_pos.mpr hr) (hsource w hw)) hfw

theorem polarIntegral_operator_boundary (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1)
    (hr0 : r ≠ 0) (θ : ℝ) (hboundary : ∀ w ∈ K, a w ^ 2 + b w ^ 2 = 1) :
    polarOperator k (polarIntegral (polarKernelRR (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernelR (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernelTT (-k / 2)) a b μ f r θ)
      (polarIntegral (polarKernel (-k / 2)) a b μ f r θ) r = 0 := by
  rw [polarIntegral_operator hK hμ hf ha hb hsource k hr θ]
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with w hw
  rw [polarKernel_equation k (a w) (b w) r θ
    (polarDenominator_pos hr (hsource w hw) θ) hr0 (sub_pos.mpr hr).ne', hboundary w hw]
  simp

end Integration

end BergmanWeakType.Weighted
