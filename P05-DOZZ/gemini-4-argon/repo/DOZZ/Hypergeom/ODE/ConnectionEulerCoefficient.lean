/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerSeries
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Evaluation of the first zero-basis connection coefficient from the real Euler integral. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

private theorem intCast_abs_sub_lower_bound q (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℤ) :
    min q (1 - q) ≤ |(n : ℝ) - q| := by
  have hn : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hn with hn | hn
  · have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [abs_of_nonpos (by linarith)]
    exact (min_le_left q (1 - q)).trans (by linarith)
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_right q (1 - q)).trans (by linarith)

private theorem realInterval_accumulates_in_complex (lo x hi : ℝ)
    (hlo : lo < x) (hhi : x < hi) :
    (x : ℂ) ∈ closure
      ((fun y : ℝ => (y : ℂ)) '' (Ioo lo hi \ {x})) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let d : ℝ := min (ε / 2) ((hi - x) / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have : d < hi - x := by
    dsimp [d]
    exact (min_le_right _ _).trans_lt (by linarith)
  have hy : x + d ∈ Ioo lo hi \ {x} := by
    constructor
    · constructor <;> linarith
    · simp [ne_of_gt hd]
  refine ⟨(x + d : ℝ), ?_, ?_⟩
  · exact ⟨x + d, hy, rfl⟩
  · have hdiff : (x : ℂ) - ((x + d : ℝ) : ℂ) = -(d : ℂ) := by push_cast; ring
    rw [dist_eq_norm, hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    exact (by dsimp [d]; exact (min_le_left _ _).trans_lt (by linarith))

private theorem ofReal_interval_subset_ball {lo q hi r : ℝ}
    (hleft : q - r ≤ lo) (hright : hi ≤ q + r)
    {x : ℝ} (hx : x ∈ Ioo lo hi) :
    (x : ℂ) ∈ Metric.ball (q : ℂ) r := by
  rcases hx with ⟨hxlo, hxhi⟩
  rw [Metric.mem_ball, dist_eq_norm]
  rw [(show ‖(x : ℂ) - (q : ℂ)‖ = |x - q| by rw [show (x : ℂ) - (q : ℂ) = ((x - q : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs])]
  exact (by apply abs_lt.mpr; constructor <;> linarith)

private theorem ofReal_ball_subset_integerRange_compl (q r : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hr : r < min q (1 - q)) :
    Metric.ball (q : ℂ) r ⊆ gaussConnectionIntegerRangeᶜ := by
  intro z hz hzInt
  rcases hzInt with ⟨n, hn⟩
  subst z
  have : ‖(n : ℂ) - (q : ℂ)‖ < r := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hz)
  have : min q (1 - q) ≤ ‖(n : ℂ) - (q : ℂ)‖ := by
    have hnormEq : ‖(n : ℂ) - (q : ℂ)‖ = |(n : ℝ) - q| := by
      calc
        ‖(n : ℂ) - (q : ℂ)‖ = ‖(((n : ℝ) - q : ℝ) : ℂ)‖ := by
          congr 1
          push_cast
          ring
        _ = |(n : ℝ) - q| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnormEq]
    exact intCast_abs_sub_lower_bound q hq0 hq1 n
  linarith

private theorem ofReal_mem_integerRange_compl_of_between_zero_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ gaussConnectionIntegerRangeᶜ := by
  rw [gaussConnectionIntegerRange, Set.mem_compl_iff]
  rintro ⟨n, hn⟩
  have hnC : ((n : ℝ) : ℂ) = (x : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hn
  have := Complex.ofReal_injective hnC
  have hnCases : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hnCases with hn | hn
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith


/-- The real first-coefficient identity extends to an open complex parameter box by applying the
one-variable identity theorem successively in `c`, `δ`, and `a`. -/
theorem connectionMinusFirstCramer_eq_gamma_on_open_box
    {H} (hH : IsGaussHypergeometricFamily H) :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
        ∀ a ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
          connectionMinusFirstCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionMinusGammaCoefficient₁ (gaussConnectionCoordinates c δ a) := by
  have connectionMinusFirstCramer_eq_gamma_of_real a (b : ℝ) (c : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < c - a - b) (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ) (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) : connectionMinusFirstCramerCoefficient H (a, b, c) = gaussConnectionMinusGammaCoefficient₁ (a, b, c) := by
    let p : ℂ × ℂ × ℂ := (a, b, c)
    have hcb : 0 < c - b := by linarith
    have hp : p ∈ gaussConnectionParameterDomain := by
      change (∀ n : ℤ, (c : ℂ) ≠ (n : ℂ)) ∧
        ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ)
      constructor
      · intro n heq
        apply hcInt
        exact ⟨n, heq.symm⟩
      · intro n heq
        apply hδInt
        refine ⟨n, ?_⟩
        calc
          (n : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := heq.symm
          _ = ((c - a - b : ℝ) : ℂ) := by push_cast; ring
    have hEulerValue :
        Tendsto (fun x : ℝ =>
          ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) *
            (realGaussEulerKernelIntegral a b c x : ℂ))
          (𝓝[Iio 1] 1)
          (𝓝 ((Real.Gamma c * Real.Gamma (c - a - b) /
            (Real.Gamma (c - a) * Real.Gamma (c - b)) : ℝ) : ℂ)) := by
      convert Complex.continuous_ofReal.continuousAt.tendsto.comp
        (realGaussEulerKernelIntegral_tendsto_gauss_value a b c ha hb hδ) using 1
      · funext x
        change ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) *
            (realGaussEulerKernelIntegral a b c x : ℂ) =
          ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) *
            realGaussEulerKernelIntegral a b c x : ℝ) : ℂ)
        exact (Complex.ofReal_mul _ _).symm
    have hGamma :
        ((Real.Gamma c * Real.Gamma (c - a - b) /
            (Real.Gamma (c - a) * Real.Gamma (c - b)) : ℝ) : ℂ) =
          gaussConnectionMinusGammaCoefficient₁ p := by
      dsimp [gaussConnectionMinusGammaCoefficient₁, p]
      rw [show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by push_cast; ring,
        show (c : ℂ) - (a : ℂ) = ((c - a : ℝ) : ℂ) by push_cast; ring,
        show (c : ℂ) - (b : ℂ) = ((c - b : ℝ) : ℂ) by push_cast; ring,
        Complex.Gamma_ofReal c, Complex.Gamma_ofReal (c - a - b),
        Complex.Gamma_ofReal (c - a), Complex.Gamma_ofReal (c - b)]
      push_cast
      field_simp [((Real.Gamma_pos_of_pos (by linarith)).ne'), ((Real.Gamma_pos_of_pos hδ).ne'), ((Real.Gamma_pos_of_pos (by linarith)).ne'), ((Real.Gamma_pos_of_pos hcb).ne')]
    simpa [p] using (connectionMinusFirstCramer_eq_of_endpoint_limit hH hp (by rw [show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by push_cast; ring]; simp only [Complex.ofReal_re]; exact hδ) (show Tendsto (fun x : ℝ => gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) (𝓝[Iio 1] 1) (𝓝 ((Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b)) : ℝ) : ℂ)) by simpa [gaussFMinus] using Filter.Tendsto.congr' ((show ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) = ((Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) : ℝ) : ℂ) * (realGaussEulerKernelIntegral a b c x : ℂ) by filter_upwards [(Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))), (show ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, x < 1 by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1))] with x hx hx1; simpa [realGaussEulerKernelIntegral] using (realGaussEulerIntegral_eq_family hH a b c x ha hb hcb hx hx1).symm).mono fun x hx => hx.symm) hEulerValue)).trans hGamma
  let SC := Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ)
  let TC := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
  let VC := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
  let SR := Ioo (11 / 16 : ℝ) (13 / 16 : ℝ)
  let TR := Ioo (3 / 16 : ℝ) (5 / 16 : ℝ)
  let VR := Ioo (3 / 16 : ℝ) (5 / 16 : ℝ)
  let f := connectionMinusFirstCramerCoefficient H
  let g := gaussConnectionMinusGammaCoefficient₁
  have hTCReal {x : ℝ} (hx : x ∈ TR) : (x : ℂ) ∈ TC := by
    simpa [TC, Complex.ofReal_div] using
      (ofReal_interval_subset_ball (lo := 3 / 16) (q := 1 / 4)
        (hi := 5 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hVCReal {x : ℝ} (hx : x ∈ VR) : (x : ℂ) ∈ VC := by
    simpa [VC, Complex.ofReal_div] using
      (ofReal_interval_subset_ball (lo := 3 / 16) (q := 1 / 4)
        (hi := 5 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hrealEq : ∀ c ∈ SR, ∀ δ ∈ TR, ∀ a ∈ VR,
      f (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) := by
    intro c hc δ hδ a ha
    have hδpos : 0 < δ := by rcases hδ with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hb : 0 < c - δ - a := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hcLo hcHi hδLo hδHi haLo haHi
      linarith
    have hreal := connectionMinusFirstCramer_eq_gamma_of_real a (c - δ - a) c
      (by rcases ha with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith) hb (by simpa only [show c - a - (c - δ - a) = δ by ring] using hδpos) (ofReal_mem_integerRange_compl_of_between_zero_one (by rcases hc with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith) (show c < 1 by rcases hc with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith)) (by
        rw [show c - a - (c - δ - a) = δ by ring]
        exact (ofReal_mem_integerRange_compl_of_between_zero_one hδpos (by rcases hδ with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith)))
    simpa [f, g, gaussConnectionCoordinates] using hreal
  have hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p := by
    intro p hp
    exact connectionMinusFirstCramerCoefficient_differentiableAt hH hp
  have hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p := by
    intro p hp
    exact gaussConnectionMinusGammaCoefficient₁_differentiableAt hp
  have hcoord c δ a (hc : c ∈ SC) (hδ : δ ∈ TC) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using (⟨(show SC ⊆ gaussConnectionIntegerRangeᶜ by simpa [SC, Complex.ofReal_div] using (ofReal_ball_subset_integerRange_compl (3 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))) hc, (show TC ⊆ gaussConnectionIntegerRangeᶜ by simpa [TC, Complex.ofReal_div] using (ofReal_ball_subset_integerRange_compl (1 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))) hδ⟩ : c ∈ gaussConnectionIntegerRangeᶜ ∧ δ ∈ gaussConnectionIntegerRangeᶜ)
  have hfC δ a (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => f (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      exact ((hf _ (hcoord c δ a hc hδ)).comp c (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgC δ a (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => g (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      exact ((hg _ (hcoord c δ a hc hδ)).comp c (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfD c a (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => f (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      exact ((hf _ (hcoord c δ a hc hδ)).comp δ (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgD c a (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => g (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      exact ((hg _ (hcoord c δ a hc hδ)).comp δ (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfA c δ (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => f (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      exact ((hf _ (hcoord c δ a hc hδ)).comp a (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgA c δ (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => g (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      exact ((hg _ (hcoord c δ a hc hδ)).comp a (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hC (δ : ℝ) (hδ : δ ∈ TR) (a : ℝ) (ha : a ∈ VR) :
      ∀ c ∈ SC, f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) := by
    have hδC := hTCReal hδ
    have haC := hVCReal ha
    have hclosure : (3 / 4 : ℂ) ∈ closure
        ({c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)}) := by
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (SR \ {(3 / 4 : ℝ)})) ⊆
          {c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)} := by
        rintro z ⟨c, ⟨hc, hcn⟩, rfl⟩
        constructor
        · exact hrealEq c hc δ hδ a ha
        · intro heq
          apply hcn
          exact Set.mem_singleton_iff.mpr (Complex.ofReal_injective ((show (c : ℂ) = (3 / 4 : ℂ) by simpa only [Set.mem_singleton_iff] using heq).trans (by norm_num)))
      exact closure_mono hsub (by simpa [SR] using (realInterval_accumulates_in_complex (11 / 16) (3 / 4) (13 / 16) (by norm_num) (by norm_num)))
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfC (δ : ℂ) (a : ℂ) hδC haC) (hgC (δ : ℂ) (a : ℂ) hδC haC)
      (convex_ball (3 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected (by norm_num [SC, Metric.mem_ball, dist_eq_norm]) hclosure
    intro c hc
    exact hEq hc
  have hD c (hc : c ∈ SC) (a : ℝ) (ha : a ∈ VR) :
      ∀ δ ∈ TC, f (gaussConnectionCoordinates c δ (a : ℂ)) =
        g (gaussConnectionCoordinates c δ (a : ℂ)) := by
    have haC := hVCReal ha
    have hclosure : (1 / 4 : ℂ) ∈ closure
        ({δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {(1 / 4 : ℂ)}) := by
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (TR \ {(1 / 4 : ℝ)})) ⊆
          {δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {(1 / 4 : ℂ)} := by
        rintro z ⟨δ, ⟨hδ, hδn⟩, rfl⟩
        constructor
        · exact hC δ hδ a ha c hc
        · intro heq
          apply hδn
          exact Set.mem_singleton_iff.mpr (Complex.ofReal_injective ((show (δ : ℂ) = (1 / 4 : ℂ) by simpa only [Set.mem_singleton_iff] using heq).trans (by norm_num)))
      exact closure_mono hsub (by simpa [TR] using (realInterval_accumulates_in_complex (3 / 16) (1 / 4) (5 / 16) (by norm_num) (by norm_num)))
    intro δ hδ
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure (hfD c (a : ℂ) hc haC) (hgD c (a : ℂ) hc haC) (convex_ball (1 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected (by norm_num [TC, Metric.mem_ball, dist_eq_norm]) hclosure) hδ
  have hA c δ (hc : c ∈ SC) (hδ : δ ∈ TC) :
      ∀ a ∈ VC, f (gaussConnectionCoordinates c δ a) =
        g (gaussConnectionCoordinates c δ a) := by
    have hclosure : (1 / 4 : ℂ) ∈ closure
        ({a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 4 : ℂ)}) := by
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (VR \ {(1 / 4 : ℝ)})) ⊆
          {a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 4 : ℂ)} := by
        rintro z ⟨a, ⟨ha, han⟩, rfl⟩
        constructor
        · exact hD c hc a ha δ hδ
        · intro heq
          apply han
          exact Set.mem_singleton_iff.mpr (Complex.ofReal_injective ((show (a : ℂ) = (1 / 4 : ℂ) by simpa only [Set.mem_singleton_iff] using heq).trans (by norm_num)))
      exact closure_mono hsub (by simpa [VR] using (realInterval_accumulates_in_complex (3 / 16) (1 / 4) (5 / 16) (by norm_num) (by norm_num)))
    intro a ha
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure (hfA c δ hc hδ) (hgA c δ hc hδ) (convex_ball (1 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected (by norm_num [VC, Metric.mem_ball, dist_eq_norm]) hclosure) ha
  intro c hc δ hδ a ha
  exact hA c δ hc hδ a ha

end DOZZ.Proofs
