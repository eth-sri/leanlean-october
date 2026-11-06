/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerPlusCoefficient
public import DOZZ.Hypergeom.ODE.ConnectionEulerSecondCoefficientBox
import DOZZ.Hypergeom.ODE.ConnectionEulerCoefficient

/-! Holomorphic continuation of both powered connection coefficients from real Euler boxes. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

private theorem intCast_abs_sub_lower_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℤ) :
    min q (1 - q) ≤ |(n : ℝ) - q| := by
  have hn : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hn with hn | hn
  · have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    grind
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    grind

private theorem realInterval_accumulates_in_complex (lo x hi : ℝ)
    (hlo : lo < x) (hhi : x < hi) :
    (x : ℂ) ∈ closure
      ((fun y : ℝ => (y : ℂ)) '' (Ioo lo hi \ {x})) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let d := min (ε / 2) ((hi - x) / 2)
  have hd : 0 < d := by positivity
  have hdε : d < ε := by
    aesop
  have hdhi : d < hi - x := by
    aesop
  have hy : x + d ∈ Ioo lo hi \ {x} := by
    grind
  refine ⟨(x + d : ℝ), ?_, ?_⟩
  · grind
  · have hdiff : (x : ℂ) - ((x + d : ℝ) : ℂ) = -(d : ℂ) := by push_cast; ring
    rw [dist_eq_norm, hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    exact hdε

private theorem ofReal_interval_subset_ball {lo q hi r : ℝ}
    (hleft : q - r ≤ lo) (hright : hi ≤ q + r)
    {x : ℝ} (hx : x ∈ Ioo lo hi) :
    (x : ℂ) ∈ Metric.ball (q : ℂ) r := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hbound : |x - q| < r := by
    grind
  rw [Metric.mem_ball, dist_eq_norm]
  norm_cast

private theorem ofReal_mem_integerRange_compl_of_between_zero_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ gaussConnectionIntegerRangeᶜ := by
  rintro ⟨n, hn⟩
  have hnC : (n) = (x : ℂ) := by
    assumption
  have hnR : (n : ℝ) = x := Complex.ofReal_injective hnC
  have hnCases : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hnCases with hn | hn
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

/-- On the real Euler region, the first midpoint Cramer coefficient is the first Gamma
coefficient. Nonintegrality is retained only for the ODE connection-basis hypotheses. -/

private theorem secondCoefficient_realInterval_accumulates (lo x hi : ℝ)
    (hlo : lo < x) (hhi : x < hi) :
    (x : ℂ) ∈ closure
      ((fun y : ℝ => (y : ℂ)) '' (Ioo lo hi \ {x})) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let d := min (ε / 2) ((hi - x) / 2)
  have hd : 0 < d := by positivity
  have hdε : d < ε := by
    aesop
  have hdhi : d < hi - x := by
    aesop
  have hy : x + d ∈ Ioo lo hi \ {x} := by
    grind
  refine ⟨(x + d : ℝ), ?_, ?_⟩
  · grind
  · have hdiff : x - ((x + d : ℝ) : ℂ) = -(d : ℂ) := by push_cast; ring
    rw [dist_eq_norm, hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd]
    exact hdε

private theorem secondCoefficient_ofReal_interval_subset_ball {lo q hi r : ℝ}
    (hleft : q - r ≤ lo) (hright : hi ≤ q + r)
    {x : ℝ} (hx : x ∈ Ioo lo hi) :
    (x : ℂ) ∈ Metric.ball (q : ℂ) r := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hbound : |x - q| < r := by
    grind
  rw [Metric.mem_ball, dist_eq_norm]
  norm_cast

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H)
include hH

/-- The real first-coefficient identity extends to an open complex parameter box by applying the
one-variable identity theorem successively in `c`, `δ`, and `a`. -/
theorem connectionPlusFirstCramer_eq_gamma_on_open_box
    :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
        ∀ a ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
          connectionPlusFirstCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₁ (gaussConnectionCoordinates c δ a) := by
  let SC := Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ)
  let TC := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
  let VC := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
  let SR := Ioo (11 / 16 : ℝ) (13 / 16 : ℝ)
  let TR := Ioo (3 / 16 : ℝ) (5 / 16 : ℝ)
  let VR := Ioo (3 / 16 : ℝ) (5 / 16 : ℝ)
  let f := connectionPlusFirstCramerCoefficient H
  let g := gaussConnectionPlusGammaCoefficient₁
  have hSCInt : SC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [SC, Complex.ofReal_div] using
      (DOZZ.Proofs.ofReal_ball_subset_integerRange_compl (3 / 4) (1 / 8) (by norm_num)
        (by norm_num) (by norm_num))
  have hTCInt : TC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [TC, Complex.ofReal_div] using
      (DOZZ.Proofs.ofReal_ball_subset_integerRange_compl (1 / 4) (1 / 8) (by norm_num)
        (by norm_num) (by norm_num))
  have hSCReal {x : ℝ} (hx : x ∈ SR) : (x : ℂ) ∈ SC := by
    simpa [SC, Complex.ofReal_div] using
      (ofReal_interval_subset_ball (q := 3 / 4)
        (hi := 13 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hTCReal {x : ℝ} (hx : x ∈ TR) : (x : ℂ) ∈ TC := by
    simpa [TC, Complex.ofReal_div] using
      (ofReal_interval_subset_ball (q := 1 / 4)
        (hi := 5 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hVCReal {x : ℝ} (hx : x ∈ VR) : (x : ℂ) ∈ VC := by
    tauto
  have hrealEq : ∀ c ∈ SR, ∀ δ ∈ TR, ∀ a ∈ VR,
      f (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) := by
    intro c hc δ hδ a ha
    have hcpos : 0 < c := by grind
    have hcLt : c < 1 := by grind
    have hδpos : 0 < δ := by grind
    have hδLt : δ < 1 := by grind
    have hap : 0 < a := by grind
    have hb : 0 < c - δ - a := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have hA : 0 < a - c + 1 := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have hB : 0 < (c - δ - a) - c + 1 := by
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have hdelta : 0 < c - a - (c - δ - a) := by linarith
    have hreal := connectionPlusFirstCramer_eq_gamma_of_real hH a _ c
      hA hB hdelta (ofReal_mem_integerRange_compl_of_between_zero_one hcpos hcLt) (by
        rw [show c - a - (c - δ - a) = δ by ring]
        exact (ofReal_mem_integerRange_compl_of_between_zero_one hδpos hδLt))
    simpa [f, g, gaussConnectionCoordinates] using hreal
  have hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p := by
    intro p hp
    exact connectionPlusFirstCramerCoefficient_differentiableAt hH hp
  have hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p := by
    intro p hp
    exact gaussConnectionPlusGammaCoefficient₁_differentiableAt hp
  have hcoord (c δ a : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    have hparams : c ∈ gaussConnectionIntegerRangeᶜ ∧
        δ ∈ gaussConnectionIntegerRangeᶜ := by tauto
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using hparams
  have hfC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => f (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => g (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => f (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => g (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => f (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => g (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hcCenter : (3 / 4 : ℂ) ∈ SC := by norm_num [SC, Metric.mem_ball, dist_eq_norm]
  have hδCenter : (1 / 4 : ℂ) ∈ TC := by norm_num [TC, Metric.mem_ball, dist_eq_norm]
  have haCenter : (1 / 4 : ℂ) ∈ VC := by assumption
  have hC (δ : ℝ) (hδ : δ ∈ TR) (a : ℝ) (ha : a ∈ VR) :
      ∀ c ∈ SC, f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) := by
    have hδC := hTCReal hδ
    have haC := hVCReal ha
    have hclosure : (3 / 4 : ℂ) ∈ closure
        ({c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)}) := by
      have hacc := realInterval_accumulates_in_complex
        (11 / 16) (3 / 4) (13 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (SR \ {(3 / 4 : ℝ)})) ⊆
          {c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)} := by
        rintro z ⟨c, ⟨hc, hcn⟩, rfl⟩
        constructor
        · exact hrealEq c hc δ hδ a ha
        · intro heq
          apply hcn
          have heqC : (c : ℂ) = (3 / 4 : ℂ) := by
            simpa using heq
          have heq' : c = (3 / 4 : ℝ) :=
            Complex.ofReal_injective (heqC.trans (by norm_num))
          exact Set.mem_singleton_iff.mpr heq'
      exact closure_mono hsub (by simpa [SR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfC (δ : ℂ) (a : ℂ) hδC haC) (hgC (δ : ℂ) (a : ℂ) hδC haC)
      (convex_ball (3 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected hcCenter hclosure
    intro c hc
    exact hEq hc
  have hD (c : ℂ) (hc : c ∈ SC) (a : ℝ) (ha : a ∈ VR) :
      ∀ δ ∈ TC, f (gaussConnectionCoordinates c δ (a : ℂ)) =
        g (gaussConnectionCoordinates c δ (a : ℂ)) := by
    have haC := hVCReal ha
    have hclosure : (1 / 4 : ℂ) ∈ closure
        ({δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {(1 / 4 : ℂ)}) := by
      have hacc := realInterval_accumulates_in_complex
        (3 / 16) (1 / 4) (5 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (TR \ {(1 / 4 : ℝ)})) ⊆
          {δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {(1 / 4 : ℂ)} := by
        rintro z ⟨δ, ⟨hδ, hδn⟩, rfl⟩
        constructor
        · exact hC δ hδ a ha c hc
        · intro heq
          apply hδn
          have heqC : (δ : ℂ) = (1 / 4 : ℂ) := by
            simpa using heq
          have heq' : δ = (1 / 4 : ℝ) :=
            Complex.ofReal_injective (heqC.trans (by norm_num))
          exact Set.mem_singleton_iff.mpr heq'
      exact closure_mono hsub (by simpa [TR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfD c (a : ℂ) hc haC) (hgD c (a : ℂ) hc haC)
      (convex_ball (1 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected hδCenter hclosure
    intro δ hδ
    exact hEq hδ
  have hA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      ∀ a ∈ VC, f (gaussConnectionCoordinates c δ a) =
        g (gaussConnectionCoordinates c δ a) := by
    have hclosure : (1 / 4 : ℂ) ∈ closure
        ({a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 4 : ℂ)}) := by
      have hacc := realInterval_accumulates_in_complex
        (3 / 16) (1 / 4) (5 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (VR \ {(1 / 4 : ℝ)})) ⊆
          {a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 4 : ℂ)} := by
        rintro z ⟨a, ⟨ha, han⟩, rfl⟩
        constructor
        · exact hD c hc a ha δ hδ
        · intro heq
          apply han
          have heqC : (a : ℂ) = (1 / 4 : ℂ) := by
            simpa using heq
          have heq' : a = (1 / 4 : ℝ) :=
            Complex.ofReal_injective (heqC.trans (by norm_num))
          exact Set.mem_singleton_iff.mpr heq'
      exact closure_mono hsub (by simpa [VR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfA c δ hc hδ) (hgA c δ hc hδ)
      (convex_ball (1 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected haCenter hclosure
    intro a ha
    exact hEq ha
  intro c hc δ hδ a ha
  exact hA c δ hc hδ a ha

/-- The second midpoint Cramer coefficient agrees with its Gamma value on a nonempty complex
open box. The box is centered in the negative-excess Euler region, then three one-variable
identity theorems continue the real identity in `c`, `δ`, and `a`. -/
theorem connectionPlusSecondCramer_eq_gamma_on_open_box
    :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ),
        ∀ a ∈ Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ),
          connectionPlusSecondCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₂ (gaussConnectionCoordinates c δ a) := by
  let SC := Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ)
  let TC := Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ)
  let VC := Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ)
  let SR := Ioo (11 / 16 : ℝ) (13 / 16 : ℝ)
  let TR := Ioo (-(5 / 16 : ℝ)) (-(3 / 16 : ℝ))
  let VR := Ioo (7 / 16 : ℝ) (9 / 16 : ℝ)
  let f := connectionPlusSecondCramerCoefficient H
  let g := gaussConnectionPlusGammaCoefficient₂
  have hSCInt : SC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [SC, Complex.ofReal_div] using
      (DOZZ.Proofs.ofReal_ball_subset_integerRange_compl (3 / 4) (1 / 8)
        (by norm_num) (by norm_num) (by norm_num))
  have hTCInt : TC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [TC] using DOZZ.Proofs.secondCoefficient_negativeQuarter_ball_avoids_integers
  have hSCReal {x : ℝ} (hx : x ∈ SR) : (x : ℂ) ∈ SC := by
    simpa [SC, Complex.ofReal_div] using
      (secondCoefficient_ofReal_interval_subset_ball (q := 3 / 4)
        (hi := 13 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hTCReal {x : ℝ} (hx : x ∈ TR) : (x : ℂ) ∈ TC := by
    simpa [TC] using
      (secondCoefficient_ofReal_interval_subset_ball (q := -(1 / 4))
        (hi := -(3 / 16)) (r := 1 / 16) (by norm_num) (by norm_num) hx)
  have hVCReal {x : ℝ} (hx : x ∈ VR) : (x : ℂ) ∈ VC := by
    simpa [VC, Complex.ofReal_div] using
      (secondCoefficient_ofReal_interval_subset_ball (q := 1 / 2)
        (hi := 9 / 16) (r := 1 / 16) (by norm_num) (by norm_num) hx)
  have hrealEq : ∀ c ∈ SR, ∀ δ ∈ TR, ∀ a ∈ VR,
      f (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) := by
    intro c hc δ hδ a ha
    have hcpos : 0 < c := by grind
    have hcLt : c < 1 := by grind
    have hδneg : δ < 0 := by grind
    have hap : 0 < a := by grind
    have hca : 0 < c - a := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have hcb : 0 < c - (c - δ - a) := by
      have hδa : 0 < δ + a := by
        rcases hδ with ⟨hδLo, hδHi⟩
        rcases ha with ⟨haLo, haHi⟩
        linarith
      convert hδa using 1
      ring
    have hb : 0 < c - δ - a := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have h1a : 0 < 1 - a := by
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have h1b : 0 < 1 - (c - δ - a) := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have hA : 0 < a - c + 1 := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases ha with ⟨haLo, haHi⟩
      linarith
    have hB : 0 < (c - δ - a) - c + 1 := by
      linarith
    have hδInt : ((c - a - (c - δ - a) : ℝ) : ℂ) ∈
        gaussConnectionIntegerRangeᶜ := by
      rw [show c - a - (c - δ - a) = δ by ring]
      exact hTCInt (hTCReal hδ)
    have hdelta : c - a - (c - δ - a) < 0 := by
      rw [show c - a - (c - δ - a) = δ by ring]
      exact hδneg
    have hreal := connectionPlusSecondCramer_eq_gamma_of_real hH a _ c
      hA hB h1a h1b hdelta (hSCInt (hSCReal hc)) hδInt
    simpa [f, g, gaussConnectionCoordinates] using hreal
  have hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p := by
    intro p hp
    exact connectionPlusSecondCramerCoefficient_differentiableAt hH hp
  have hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p := by
    intro p hp
    exact gaussConnectionPlusGammaCoefficient₂_differentiableAt hp
  have hcoord (c δ a : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    have hparams : c ∈ gaussConnectionIntegerRangeᶜ ∧
        δ ∈ gaussConnectionIntegerRangeᶜ := by tauto
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using hparams
  have hfC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => f (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => g (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => f (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => g (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => f (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => g (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hcCenter : (3 / 4 : ℂ) ∈ SC := by
    norm_num [SC, Metric.mem_ball, dist_eq_norm]
  have hδCenter : -(1 / 4 : ℂ) ∈ TC := by
    norm_num [TC, Metric.mem_ball, dist_eq_norm]
  have haCenter : (1 / 2 : ℂ) ∈ VC := by
    norm_num [VC, Metric.mem_ball, dist_eq_norm]
  have hC (δ : ℝ) (hδ : δ ∈ TR) (a : ℝ) (ha : a ∈ VR) :
      ∀ c ∈ SC, f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) := by
    have hδC := hTCReal hδ
    have haC := hVCReal ha
    have hclosure : (3 / 4 : ℂ) ∈ closure
        ({c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)}) := by
      have hacc := secondCoefficient_realInterval_accumulates
        (11 / 16) (3 / 4) (13 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (SR \ {(3 / 4 : ℝ)})) ⊆
          {c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)} := by
        rintro z ⟨c, ⟨hc, hcn⟩, rfl⟩
        constructor
        · exact hrealEq c hc δ hδ a ha
        · intro heq
          apply hcn
          have heqC : (c : ℂ) = (3 / 4 : ℂ) := by
            simpa using heq
          exact Set.mem_singleton_iff.mpr (Complex.ofReal_injective (heqC.trans (by norm_num)))
      exact closure_mono hsub (by simpa [SR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfC (δ : ℂ) (a : ℂ) hδC haC) (hgC (δ : ℂ) (a : ℂ) hδC haC)
      (convex_ball (3 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected hcCenter hclosure
    intro c hc
    exact hEq hc
  have hD (c : ℂ) (hc : c ∈ SC) (a : ℝ) (ha : a ∈ VR) :
      ∀ δ ∈ TC, f (gaussConnectionCoordinates c δ (a : ℂ)) =
        g (gaussConnectionCoordinates c δ (a : ℂ)) := by
    have haC := hVCReal ha
    have hclosure : (-(1 / 4 : ℂ)) ∈ closure
        ({δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {-(1 / 4 : ℂ)}) := by
      have hacc := secondCoefficient_realInterval_accumulates
        (-(5 / 16)) (-(1 / 4)) (-(3 / 16)) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (TR \ {-(1 / 4 : ℝ)})) ⊆
          {δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {-(1 / 4 : ℂ)} := by
        rintro z ⟨δ, ⟨hδ, hδn⟩, rfl⟩
        constructor
        · exact hC δ hδ a ha c hc
        · intro heq
          apply hδn
          have heqC : (δ : ℂ) = -(1 / 4 : ℂ) := by
            simpa using heq
          exact Set.mem_singleton_iff.mpr
            (Complex.ofReal_injective (heqC.trans (by norm_num)))
      exact closure_mono hsub (by simpa [TR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfD c (a : ℂ) hc haC) (hgD c (a : ℂ) hc haC)
      (convex_ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ)).isPreconnected hδCenter hclosure
    intro δ hδ
    exact hEq hδ
  have hA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      ∀ a ∈ VC, f (gaussConnectionCoordinates c δ a) =
        g (gaussConnectionCoordinates c δ a) := by
    have hclosure : (1 / 2 : ℂ) ∈ closure
        ({a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 2 : ℂ)}) := by
      have hacc := secondCoefficient_realInterval_accumulates
        (7 / 16) (1 / 2) (9 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (VR \ {(1 / 2 : ℝ)})) ⊆
          {a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 2 : ℂ)} := by
        rintro z ⟨a, ⟨ha, han⟩, rfl⟩
        constructor
        · exact hD c hc a ha δ hδ
        · intro heq
          apply han
          have heqC : (a : ℂ) = (1 / 2 : ℂ) := by
            simpa using heq
          exact Set.mem_singleton_iff.mpr (Complex.ofReal_injective (heqC.trans (by norm_num)))
      exact closure_mono hsub (by simpa [VR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfA c δ hc hδ) (hgA c δ hc hδ)
      (convex_ball (1 / 2 : ℂ) (1 / 16 : ℝ)).isPreconnected haCenter hclosure
    intro a ha
    exact hEq ha
  intro c hc δ hδ a ha
  exact hA c δ hc hδ a ha

end

end

end DOZZ.Proofs
