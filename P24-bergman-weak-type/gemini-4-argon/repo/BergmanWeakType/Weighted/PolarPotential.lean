/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Order.Compact

/-! # Polar differential equations under compact source integrals -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType.Weighted

theorem antitoneOn_of_radial_flux {M M' w F F' : ℝ → ℝ}
    (hM : ContinuousOn M (Ico 0 1))
    (hMd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt M (M' r) r)
    (hw : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < w r)
    (hF : ContinuousOn F (Ico 0 1)) (hFzero : F 0 = 0)
    (hFd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' r) r)
    (hFnonpos : ∀ r ∈ Ioo (0 : ℝ) 1, F' r ≤ 0)
    (hflux : ∀ r ∈ Ioo (0 : ℝ) 1, F r = r * w r * M' r) :
    AntitoneOn M (Ico 0 1) := by
  have hanti : AntitoneOn F (Ico 0 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) hF
      (fun r hr ↦ (hFd r (by simpa only [interior_Ico] using hr)).hasDerivWithinAt)
      (by simpa only [interior_Ico] using hFnonpos)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) hM
    (fun r hr ↦ (hMd r (by simpa only [interior_Ico] using hr)).hasDerivWithinAt) fun r hr ↦ ?_
  have hr' : r ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using hr
  have hle := hanti (by norm_num : (0 : ℝ) ∈ Ico 0 1) ⟨hr'.1.le, hr'.2⟩ hr'.1.le
  rw [hFzero, hflux r hr'] at hle
  exact nonpos_of_mul_nonpos_right hle (mul_pos hr'.1 (hw r hr'))

theorem integrable_mul_of_continuousOn_compact {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {K : Set X}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) {f g : X → ℝ}
    (hf : Integrable f μ) (hg : ContinuousOn g K) :
    Integrable (fun w ↦ g w * f w) μ := by
  have hm : AEStronglyMeasurable g μ := by
    simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
      hg.aestronglyMeasurable hK.isClosed.measurableSet (μ := μ)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hg.norm
  exact hf.bdd_mul hm (hμ.mono fun w hw ↦ hM (mem_image_of_mem _ hw))

theorem continuousOn_integral_mul_of_compact {X Y : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [FirstCountableTopology Y] {μ : Measure X} {K : Set X} {S : Set Y}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hS : IsCompact S)
    {f : X → ℝ} (hf : Integrable f μ) {F : Y → X → ℝ}
    (hF : ContinuousOn (fun p : Y × X ↦ F p.1 p.2) (S ×ˢ K)) :
    ContinuousOn (fun z ↦ ∫ w, F z w * f w ∂μ) S := by
  have hslice {z : Y} (hz : z ∈ S) : ContinuousOn (F z) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hz, hw⟩
  obtain ⟨M, hM⟩ := (hS.prod hK).bddAbove_image hF.norm
  refine continuousOn_of_dominated (bound := fun w ↦ M * ‖f w‖)
    (fun z hz ↦ (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hz)).aestronglyMeasurable)
    (fun z hz ↦ hμ.mono fun w hw ↦ ?_) (hf.norm.const_mul M)
    (hμ.mono fun w hw ↦ (hF.comp (continuous_id.prodMk continuous_const).continuousOn
      fun z hz ↦ ⟨hz, hw⟩).mul_const _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (hM (mem_image_of_mem (fun p : Y × X ↦ ‖F p.1 p.2‖)
      (show (z, w) ∈ S ×ˢ K from ⟨hz, hw⟩))) (norm_nonneg _)

/-- Continuous kernel derivatives on a compact parameter cylinder can be integrated against any
integrable density. Compactness supplies the common domination needed by differentiation. -/
theorem hasDerivAt_integral_mul_of_continuousOn_compact {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {K : Set X}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) {S : Set ℝ}
    (hS : IsCompact S) {x : ℝ} (hSx : S ∈ nhds x) {f : X → ℝ}
    (hf : Integrable f μ) {F F' : ℝ → X → ℝ}
    (hF : ContinuousOn (fun p : ℝ × X ↦ F p.1 p.2) (S ×ˢ K))
    (hF' : ContinuousOn (fun p : ℝ × X ↦ F' p.1 p.2) (S ×ˢ K))
    (hderiv : ∀ w ∈ K, ∀ u ∈ S, HasDerivAt (fun v ↦ F v w) (F' u w) u) :
    Integrable (fun w ↦ F' x w * f w) μ ∧
      HasDerivAt (fun u ↦ ∫ w, F u w * f w ∂μ) (∫ w, F' x w * f w ∂μ) x := by
  have hx : x ∈ S := mem_of_mem_nhds hSx
  have hslice {G : ℝ → X → ℝ}
      (hG : ContinuousOn (fun p : ℝ × X ↦ G p.1 p.2) (S ×ˢ K))
      {u : ℝ} (hu : u ∈ S) : ContinuousOn (G u) K :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hu, hw⟩
  obtain ⟨M, hM⟩ := (hS.prod hK).bddAbove_image hF'.norm
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u w ↦ F u w * f w) (F' := fun u w ↦ F' u w * f w) hSx
    (Filter.mem_of_superset hSx fun u hu ↦
      (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF hu)).aestronglyMeasurable)
    (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF hx))
    (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF' hx)).aestronglyMeasurable
    (bound := fun w ↦ M * ‖f w‖)
    (hμ.mono fun w hw u hu ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hM (mem_image_of_mem (fun p : ℝ × X ↦ ‖F' p.1 p.2‖)
          (show (u, w) ∈ S ×ˢ K from ⟨hu, hw⟩))) (norm_nonneg _))
    (hf.norm.const_mul M)
    (hμ.mono fun w hw u hu ↦ (hderiv w hw u hu).mul_const (f w))

def radialComponent (a b θ : ℝ) : ℝ := a * cos θ + b * sin θ
def angularComponent (a b θ : ℝ) : ℝ := b * cos θ - a * sin θ

theorem component_norm_sq (a b θ : ℝ) :
    radialComponent a b θ ^ 2 + angularComponent a b θ ^ 2 = a ^ 2 + b ^ 2 := by
  unfold radialComponent angularComponent
  linear_combination (a ^ 2 + b ^ 2) * sin_sq_add_cos_sq θ

def polarDenominator (a b r θ : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2) * r ^ 2 - 2 * r * radialComponent a b θ + 1

def polarKernel (q a b r θ : ℝ) : ℝ := polarDenominator a b r θ ^ q

def polarKernelR (q a b r θ : ℝ) : ℝ :=
  2 * q * ((a ^ 2 + b ^ 2) * r - radialComponent a b θ) * polarKernel (q - 1) a b r θ

def polarKernelRR (q a b r θ : ℝ) : ℝ :=
  2 * q * (a ^ 2 + b ^ 2) * polarKernel (q - 1) a b r θ +
    4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * r - radialComponent a b θ) ^ 2 *
      polarKernel (q - 2) a b r θ

def polarKernelT (q a b r θ : ℝ) : ℝ :=
  -2 * q * r * angularComponent a b θ * polarKernel (q - 1) a b r θ

def polarKernelTT (q a b r θ : ℝ) : ℝ :=
  2 * q * r * radialComponent a b θ * polarKernel (q - 1) a b r θ +
    4 * q * (q - 1) * r ^ 2 * angularComponent a b θ ^ 2 * polarKernel (q - 2) a b r θ

theorem polarDenominator_pos {a b r : ℝ} (hr : r ^ 2 < 1)
    (hw : a ^ 2 + b ^ 2 ≤ 1) (θ : ℝ) : 0 < polarDenominator a b r θ := by
  have h1 : (1 - r * radialComponent a b θ) * (1 + r * radialComponent a b θ) =
      (1 - r ^ 2) + r ^ 2 * (1 - (a ^ 2 + b ^ 2)) + (r * angularComponent a b θ) ^ 2 := by
    linear_combination - r ^ 2 * component_norm_sq a b θ
  have h2 : polarDenominator a b r θ =
      (1 - r * radialComponent a b θ) ^ 2 + (r * angularComponent a b θ) ^ 2 := by
    unfold polarDenominator
    linear_combination - r ^ 2 * component_norm_sq a b θ
  have h3 : (1 - r * radialComponent a b θ) ≠ 0 := fun h0 ↦ by
    rw [h0, zero_mul] at h1
    nlinarith [sq_nonneg r, sq_nonneg (r * angularComponent a b θ)]
  rw [h2]
  positivity

theorem polarKernel_hasDerivAt_r (q a b r θ : ℝ) (hd : 0 < polarDenominator a b r θ) :
    HasDerivAt (fun u ↦ polarKernel q a b u θ) (polarKernelR q a b r θ) r := by
  have hd' : HasDerivAt (fun u ↦ polarDenominator a b u θ)
      (2 * ((a ^ 2 + b ^ 2) * r - radialComponent a b θ)) r := by
    convert (((hasDerivAt_id r).pow 2).const_mul (a ^ 2 + b ^ 2)).sub
      (((hasDerivAt_id r).const_mul 2).mul_const (radialComponent a b θ)) |>.add_const 1 using 1
    · rfl
    · dsimp; ring
  convert hd'.rpow_const (p := q) (Or.inl hd.ne') using 1
  · rfl
  · unfold polarKernelR polarKernel; ring

theorem polarKernel_hasDerivAt_t (q a b r θ : ℝ) (hd : 0 < polarDenominator a b r θ) :
    HasDerivAt (polarKernel q a b r) (polarKernelT q a b r θ) θ := by
  have hr : HasDerivAt (radialComponent a b) (angularComponent a b θ) θ := by
    convert ((hasDerivAt_cos θ).const_mul a).add ((hasDerivAt_sin θ).const_mul b) using 1
    · rfl
    · unfold angularComponent; ring
  have hd' : HasDerivAt (polarDenominator a b r) (-2 * r * angularComponent a b θ) θ := by
    convert (hr.const_mul (-2 * r)).const_add ((a ^ 2 + b ^ 2) * r ^ 2 + 1) using 1
    funext u; unfold polarDenominator; ring
  convert hd'.rpow_const (p := q) (Or.inl hd.ne') using 1
  · rfl
  · unfold polarKernelT polarKernel; ring

theorem polarKernel_eq_norm_weightedKernel (α r θ : ℝ) (w : ℂ) :
    polarKernel (-(α + 2) / 2) w.re w.im r θ = ‖weightedKernel α (circleMap 0 r θ) w‖ := by
  have hsq : polarDenominator w.re w.im r θ = ‖1 - circleMap 0 r θ * star w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.one_im,
      Complex.mul_im, circleMap_zero_re, circleMap_zero_im, polarDenominator, radialComponent]
    linear_combination - (w.re ^ 2 + w.im ^ 2) * r ^ 2 * cos_sq_add_sin_sq θ
  rw [polarKernel, hsq, norm_weightedKernel, ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  congr 1; ring

variable {X : Type*} [TopologicalSpace X]

def polarSourceDomain (K : Set X) : Set ((ℝ × ℝ) × X) :=
  {p | p.1.1 ^ 2 < 1 ∧ p.2 ∈ K}

notation "polarKernelCont " K:arg a:arg b:arg H:arg =>
  ContinuousOn (fun p : (ℝ × ℝ) × _ ↦
    H (a (Prod.snd p)) (b (Prod.snd p)) (Prod.fst (Prod.fst p)) (Prod.snd (Prod.fst p)))
    (polarSourceDomain K)

section Continuity

variable {K : Set X} {a b : X → ℝ}
  (ha : Continuous a) (hb : Continuous b)
  (hsource : ∀ w ∈ K, a w ^ 2 + b w ^ 2 ≤ 1) (q : ℝ)

include ha hb hsource

theorem continuousOn_polarKernel_source :
    polarKernelCont K a b (polarKernel q) :=
  (by unfold polarDenominator radialComponent; fun_prop :
    polarKernelCont K a b polarDenominator).rpow_const
    fun p hp ↦ Or.inl (polarDenominator_pos hp.1 (hsource p.2 hp.2) p.1.2).ne'

theorem continuousOn_polarKernelR_source :
    polarKernelCont K a b (polarKernelR q) := by
  have := continuousOn_polarKernel_source ha hb hsource
  unfold polarKernelR radialComponent; fun_prop

theorem continuousOn_polarKernelRR_source :
    polarKernelCont K a b (polarKernelRR q) := by
  have := continuousOn_polarKernel_source ha hb hsource
  unfold polarKernelRR radialComponent; fun_prop

theorem continuousOn_polarKernelT_source :
    polarKernelCont K a b (polarKernelT q) := by
  have := continuousOn_polarKernel_source ha hb hsource
  unfold polarKernelT angularComponent; fun_prop

theorem continuousOn_polarKernelTT_source :
    polarKernelCont K a b (polarKernelTT q) := by
  have := continuousOn_polarKernel_source ha hb hsource
  unfold polarKernelTT radialComponent angularComponent; fun_prop

end Continuity

section Integration

variable [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

def polarIntegral (H : ℝ → ℝ → ℝ → ℝ → ℝ) (a b : X → ℝ)
    (μ : Measure X) (f : X → ℝ) (r θ : ℝ) : ℝ :=
  ∫ w, H (a w) (b w) r θ * f w ∂μ

variable {K : Set X} {a b : X → ℝ} {μ : Measure X} {f : X → ℝ}
  (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hf : Integrable f μ)

include hK hμ hf

theorem continuousOn_polarIntegral_unit {H : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : polarKernelCont K a b H) :
    ContinuousOn (fun p : ℝ × ℝ ↦ polarIntegral H a b μ f p.1 p.2)
      (Ico 0 1 ×ˢ univ) := by
  rintro ⟨r, θ⟩ ⟨hr, _⟩
  obtain ⟨S, hS, hpS, hsub⟩ := exists_compact_subset
    (isOpen_lt (continuous_fst.pow 2) continuous_const)
    (show (r, θ) ∈ {p : ℝ × ℝ | p.1 ^ 2 < 1} by dsimp; nlinarith [hr.1, hr.2])
  exact ((continuousOn_integral_mul_of_compact hK hμ hS hf
    (hH.mono fun p hp ↦ ⟨hsub hp.1, hp.2⟩)).continuousAt
    (mem_interior_iff_mem_nhds.mp hpS)).continuousWithinAt

theorem polarIntegral_hasDerivAt_r {H H' : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : polarKernelCont K a b H) (hH' : polarKernelCont K a b H')
    (hd : ∀ w ∈ K, ∀ r θ : ℝ, r ^ 2 < 1 →
      HasDerivAt (fun u ↦ H (a w) (b w) u θ) (H' (a w) (b w) r θ) r)
    {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun u ↦ polarIntegral H a b μ f u θ) (polarIntegral H' a b μ f r θ) r := by
  obtain ⟨S, hS, hSr, htarget⟩ := exists_compact_subset
    (isOpen_lt (continuous_pow 2) continuous_const) (show r ∈ {b | b ^ 2 < 1} from hr)
  have hmap : MapsTo (fun p : ℝ × X ↦ ((p.1, θ), p.2)) (S ×ˢ K) (polarSourceDomain K) :=
    fun p hp ↦ ⟨htarget hp.1, hp.2⟩
  have hcont : Continuous (fun p : ℝ × X ↦ ((p.1, θ), p.2)) := by fun_prop
  exact (hasDerivAt_integral_mul_of_continuousOn_compact hK hμ hS
    (mem_interior_iff_mem_nhds.mp hSr) hf
    (hH.comp hcont.continuousOn hmap) (hH'.comp hcont.continuousOn hmap)
    (fun w hw u hu ↦ hd w hw u θ (htarget hu))).2

theorem polarIntegral_hasDerivAt_t {H H' : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hH : polarKernelCont K a b H) (hH' : polarKernelCont K a b H')
    (hd : ∀ w ∈ K, ∀ r θ : ℝ, r ^ 2 < 1 →
      HasDerivAt (H (a w) (b w) r) (H' (a w) (b w) r θ) θ)
    {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (polarIntegral H a b μ f r) (polarIntegral H' a b μ f r θ) θ := by
  have hmap : MapsTo (fun p : ℝ × X ↦ ((r, p.1), p.2))
      (Metric.closedBall θ 1 ×ˢ K) (polarSourceDomain K) := fun _ hp ↦ ⟨hr, hp.2⟩
  have hcont : Continuous (fun p : ℝ × X ↦ ((r, p.1), p.2)) := by fun_prop
  exact (hasDerivAt_integral_mul_of_continuousOn_compact hK hμ (isCompact_closedBall θ 1)
    (Metric.closedBall_mem_nhds θ (by norm_num)) hf
    (hH.comp hcont.continuousOn hmap) (hH'.comp hcont.continuousOn hmap)
    (fun w hw u _ ↦ hd w hw r u hr)).2

variable (ha : Continuous a) (hb : Continuous b)
  (hsource : ∀ w ∈ K, a w ^ 2 + b w ^ 2 ≤ 1)
  (q : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (θ : ℝ)

include ha hb hsource hr

theorem polarIntegral_kernel_hasDerivAt_r :
    HasDerivAt (fun u ↦ polarIntegral (polarKernel q) a b μ f u θ)
      (polarIntegral (polarKernelR q) a b μ f r θ) r :=
  polarIntegral_hasDerivAt_r hK hμ hf
    (continuousOn_polarKernel_source ha hb hsource q)
    (continuousOn_polarKernelR_source ha hb hsource q)
    (fun w hw s t hs ↦ polarKernel_hasDerivAt_r q (a w) (b w) s t
      (polarDenominator_pos hs (hsource w hw) t)) hr θ

theorem polarIntegral_kernelR_hasDerivAt_r :
    HasDerivAt (fun u ↦ polarIntegral (polarKernelR q) a b μ f u θ)
      (polarIntegral (polarKernelRR q) a b μ f r θ) r :=
  polarIntegral_hasDerivAt_r hK hμ hf
    (continuousOn_polarKernelR_source ha hb hsource q)
    (continuousOn_polarKernelRR_source ha hb hsource q)
    (fun w hw s t hs ↦ by
      have hd := polarDenominator_pos hs (hsource w hw) t
      convert ((((hasDerivAt_id s).const_mul (a w ^ 2 + b w ^ 2)).sub_const
        (radialComponent (a w) (b w) t)).mul
        (polarKernel_hasDerivAt_r (q - 1) (a w) (b w) s t hd)).const_mul (2 * q) using 1
      · funext u; unfold polarKernelR; dsimp; ring
      · unfold polarKernelR polarKernelRR; rw [show q - 1 - 1 = q - 2 by ring]; dsimp; ring) hr θ

theorem polarIntegral_kernel_hasDerivAt_t :
    HasDerivAt (polarIntegral (polarKernel q) a b μ f r)
      (polarIntegral (polarKernelT q) a b μ f r θ) θ :=
  polarIntegral_hasDerivAt_t hK hμ hf
    (continuousOn_polarKernel_source ha hb hsource q)
    (continuousOn_polarKernelT_source ha hb hsource q)
    (fun w hw s t hs ↦ polarKernel_hasDerivAt_t q (a w) (b w) s t
      (polarDenominator_pos hs (hsource w hw) t)) hr θ

theorem polarIntegral_kernelT_hasDerivAt_t :
    HasDerivAt (polarIntegral (polarKernelT q) a b μ f r)
      (polarIntegral (polarKernelTT q) a b μ f r θ) θ :=
  polarIntegral_hasDerivAt_t hK hμ hf
    (continuousOn_polarKernelT_source ha hb hsource q)
    (continuousOn_polarKernelTT_source ha hb hsource q)
    (fun w hw s t hs ↦ by
      have hd := polarDenominator_pos hs (hsource w hw) t
      have ha' : HasDerivAt (angularComponent (a w) (b w)) (-radialComponent (a w) (b w) t) t := by
        convert ((hasDerivAt_cos t).const_mul (b w)).sub ((hasDerivAt_sin t).const_mul (a w)) using 1
        · rfl
        · unfold radialComponent; ring
      convert (ha'.mul (polarKernel_hasDerivAt_t (q - 1) (a w) (b w) s t hd)).const_mul
        (-2 * q * s) using 1
      · funext u; unfold polarKernelT; simp only [Pi.mul_apply]; ring
      · unfold polarKernelT polarKernelTT; rw [show q - 1 - 1 = q - 2 by ring]; ring) hr θ

omit hr

def polarOperator (a b : X → ℝ) (μ : Measure X) (f : X → ℝ) (k r θ : ℝ) : ℝ :=
  polarIntegral (polarKernelRR (-k / 2)) a b μ f r θ +
    polarIntegral (polarKernelR (-k / 2)) a b μ f r θ / r +
    polarIntegral (polarKernelTT (-k / 2)) a b μ f r θ / r ^ 2 -
    (2 * k * r / (1 - r ^ 2)) * polarIntegral (polarKernelR (-k / 2)) a b μ f r θ -
    (k ^ 2 / (1 - r ^ 2)) * polarIntegral (polarKernel (-k / 2)) a b μ f r θ

theorem polarIntegral_operator (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (hr0 : r ≠ 0) (θ : ℝ) :
    polarOperator a b μ f k r θ =
    ∫ w, -(k ^ 2 * (1 - (a w ^ 2 + b w ^ 2))) /
      ((1 - r ^ 2) * polarDenominator (a w) (b w) r θ) *
      polarKernel (-k / 2) (a w) (b w) r θ * f w ∂μ := by
  have hint {H : ℝ → ℝ → ℝ → ℝ → ℝ} (hH : polarKernelCont K a b H) :
      Integrable (fun w ↦ H (a w) (b w) r θ * f w) μ :=
    integrable_mul_of_continuousOn_compact hK hμ hf <|
      hH.comp ((continuous_const (y := (r, θ))).prodMk continuous_id).continuousOn
        fun _ hw ↦ ⟨hr, hw⟩
  have h0 := hint (continuousOn_polarKernel_source ha hb hsource (-k / 2))
  have h1 := hint (continuousOn_polarKernelR_source ha hb hsource (-k / 2))
  have h2 := hint (continuousOn_polarKernelRR_source ha hb hsource (-k / 2))
  have h3 := hint (continuousOn_polarKernelTT_source ha hb hsource (-k / 2))
  unfold polarOperator
  simp only [polarIntegral, ← integral_const_mul, ← integral_div]
  rw [← integral_add (by fun_prop) (by fun_prop), ← integral_add (by fun_prop) (by fun_prop),
    ← integral_sub (by fun_prop) (by fun_prop), ← integral_sub (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (hμ.mono fun w hw ↦ ?_)
  dsimp only
  have hd := (polarDenominator_pos hr (hsource w hw) θ).ne'
  have ht : 1 - r ^ 2 ≠ 0 := (sub_pos.mpr hr).ne'
  have hB : angularComponent (a w) (b w) θ ^ 2 =
      a w ^ 2 + b w ^ 2 - radialComponent (a w) (b w) θ ^ 2 := by
    linarith [component_norm_sq (a w) (b w) θ]
  unfold polarKernelRR polarKernelR polarKernelTT polarKernel
  rw [show -k / 2 - 2 = (-k / 2 - 1) - 1 by ring,
    Real.rpow_sub_one hd (-k / 2 - 1), Real.rpow_sub_one hd (-k / 2), hB]
  field_simp [hr0, ht, hd]
  unfold polarDenominator
  ring

theorem polarIntegral_operator_nonpos (k : ℝ) {r : ℝ} (hr : r ^ 2 < 1)
    (hr0 : r ≠ 0) (θ : ℝ) (hfn : ∀ᵐ w ∂μ, 0 ≤ f w) :
    polarOperator a b μ f k r θ ≤ 0 := by
  rw [polarIntegral_operator hK hμ hf ha hb hsource k hr hr0 θ]
  refine integral_nonpos_of_ae ((hμ.and hfn).mono fun w ⟨hw, hfw⟩ ↦ ?_)
  have hd := polarDenominator_pos hr (hsource w hw) θ
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
      (mul_nonneg (sq_nonneg k) (sub_nonneg.mpr (hsource w hw))))
      (mul_nonneg (sub_pos.mpr hr).le hd.le)) (Real.rpow_nonneg hd.le _)) hfw

end Integration

end BergmanWeakType.Weighted
