/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerPlusCoefficient
public import DOZZ.Hypergeom.ODE.ConnectionEulerSecondCoefficientBox

/-! Holomorphic continuation of both powered connection coefficients from real Euler boxes. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology


private lemma eq_on_three_balls (q₁ r₁ q₂ r₂ q₃ r₃ : ℝ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hInt₁ : Metric.ball (q₁ : ℂ) r₁ ⊆ gaussConnectionIntegerRangeᶜ)
    (hInt₂ : Metric.ball (q₂ : ℂ) r₂ ⊆ gaussConnectionIntegerRangeᶜ)
    (f g : ℂ × ℂ × ℂ → ℂ)
    (hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p)
    (hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p)
    (hreal : ∀ c : ℝ, |c - q₁| < r₁ → ∀ δ : ℝ, |δ - q₂| < r₂ → ∀ a : ℝ, |a - q₃| < r₃ →
      f (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ))) :
    ∀ c ∈ Metric.ball (q₁ : ℂ) r₁, ∀ δ ∈ Metric.ball (q₂ : ℂ) r₂, ∀ a ∈ Metric.ball (q₃ : ℂ) r₃,
      f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a) := by
  have eq_on_ball_of_real_interval (q r : ℝ) (hr : 0 < r) (F G : ℂ → ℂ) (hF : DifferentiableOn ℂ F (Metric.ball (q : ℂ) r)) (hG : DifferentiableOn ℂ G (Metric.ball (q : ℂ) r)) (hreal : ∀ x : ℝ, |x - q| < r → F (x : ℂ) = G (x : ℂ)) : EqOn F G (Metric.ball (q : ℂ) r) := by
    have hcl : (q : ℂ) ∈ closure ({z | F z = G z} \ {(q : ℂ)}) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      let d := min (ε / 2) (r / 2)
      have hd : 0 < d := lt_min (half_pos hε) (half_pos hr)
      refine ⟨((q + d : ℝ) : ℂ), ⟨hreal (q + d) ?_, fun h => ?_⟩, ?_⟩
      · rw [add_sub_cancel_left, abs_of_pos hd]
        exact (min_le_right _ _).trans_lt (half_lt_self hr)
      · exact hd.ne' (by simpa using Complex.ofReal_injective (Set.mem_singleton_iff.1 h))
      · rw [dist_eq_norm, ← Complex.ofReal_sub, sub_add_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_neg, abs_of_pos hd]
        exact (min_le_left _ _).trans_lt (half_lt_self hε)
    exact (hF.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_mem_closure
      (hG.analyticOnNhd Metric.isOpen_ball) (convex_ball _ _).isPreconnected
      (Metric.mem_ball_self hr) hcl
  have hdom {c δ : ℂ} (hc : c ∈ Metric.ball (q₁ : ℂ) r₁) (hδ : δ ∈ Metric.ball (q₂ : ℂ) r₂) (a : ℂ) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using (⟨hInt₁ hc, hInt₂ hδ⟩ : c ∈ _ ∧ δ ∈ _)
  have hmem_ball {q r x : ℝ} (hx : |x - q| < r) : (x : ℂ) ∈ Metric.ball (q : ℂ) r := by
    rwa [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hC {δ a : ℝ} (hδ : |δ - q₂| < r₂) (ha : |a - q₃| < r₃) :
      ∀ c ∈ Metric.ball (q₁ : ℂ) r₁,
        f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
          g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) :=
    eq_on_ball_of_real_interval q₁ r₁ hr₁ _ _
      (fun c hc => ((hf _ (hdom hc (hmem_ball hδ) (a : ℂ))).comp c
        (by unfold gaussConnectionCoordinates; fun_prop :
          DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x (δ : ℂ) (a : ℂ)) c)).differentiableWithinAt)
      (fun c hc => ((hg _ (hdom hc (hmem_ball hδ) (a : ℂ))).comp c
        (by unfold gaussConnectionCoordinates; fun_prop :
          DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x (δ : ℂ) (a : ℂ)) c)).differentiableWithinAt)
      fun c hc => hreal c hc δ hδ a ha
  have hD {c : ℂ} (hc : c ∈ Metric.ball (q₁ : ℂ) r₁) {a : ℝ} (ha : |a - q₃| < r₃) :
      ∀ δ ∈ Metric.ball (q₂ : ℂ) r₂,
        f (gaussConnectionCoordinates c δ (a : ℂ)) =
          g (gaussConnectionCoordinates c δ (a : ℂ)) :=
    eq_on_ball_of_real_interval q₂ r₂ hr₂ _ _
      (fun δ hδ => ((hf _ (hdom hc hδ (a : ℂ))).comp δ
        (by unfold gaussConnectionCoordinates; fun_prop :
          DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x (a : ℂ)) δ)).differentiableWithinAt)
      (fun δ hδ => ((hg _ (hdom hc hδ (a : ℂ))).comp δ
        (by unfold gaussConnectionCoordinates; fun_prop :
          DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x (a : ℂ)) δ)).differentiableWithinAt)
      fun δ hδ => hC hδ ha c hc
  intro c hc δ hδ a ha
  exact eq_on_ball_of_real_interval q₃ r₃ hr₃ _ _
    (fun z _ => ((hf _ (hdom hc hδ z)).comp z
      (by unfold gaussConnectionCoordinates; fun_prop :
        DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) z)).differentiableWithinAt)
    (fun z _ => ((hg _ (hdom hc hδ z)).comp z
      (by unfold gaussConnectionCoordinates; fun_prop :
        DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) z)).differentiableWithinAt)
    (fun z hz => hD hc hz δ hδ) ha

private lemma ball_avoids_int (q r : ℝ)
    (havoid : ∀ n : ℤ, r ≤ |(n : ℝ) - q|) :
    Metric.ball (q : ℂ) r ⊆ gaussConnectionIntegerRangeᶜ := by
  rintro z hz ⟨n, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm, show (n : ℂ) - (q : ℂ) = (((n : ℝ) - q : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs] at hz
  linarith [havoid n]

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
include hH

/-- The real first-coefficient identity extends to an open complex parameter box. -/
theorem connectionPlusFirstCramer_eq_gamma_on_open_box
 :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
        ∀ a ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
          connectionPlusFirstCramerCoefficient H (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₁ (gaussConnectionCoordinates c δ a) := by
  have hb34 : Metric.ball ((3 / 4 : ℝ) : ℂ) (1 / 8 : ℝ) ⊆ gaussConnectionIntegerRangeᶜ :=
    ball_avoids_int _ _ fun n => by
      rcases (by omega : n ≤ 0 ∨ 1 ≤ n) with hn | hn
      · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
        rw [abs_of_nonpos (by linarith)]; linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]; linarith
  have hb14 : Metric.ball ((1 / 4 : ℝ) : ℂ) (1 / 8 : ℝ) ⊆ gaussConnectionIntegerRangeᶜ :=
    ball_avoids_int _ _ fun n => by
      rcases (by omega : n ≤ 0 ∨ 1 ≤ n) with hn | hn
      · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
        rw [abs_of_nonpos (by linarith)]; linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]; linarith
  have h := eq_on_three_balls (3 / 4) (1 / 8) (1 / 4) (1 / 8) (1 / 4) (1 / 8)
    (by norm_num) (by norm_num) (by norm_num) hb34 hb14
    (connectionPlusFirstCramerCoefficient H) gaussConnectionPlusGammaCoefficient₁
    (fun _ hp => connectionPlusFirstCramerCoefficient_differentiableAt hH hp)
    (fun _ hp => gaussConnectionPlusGammaCoefficient₁_differentiableAt hp)
    fun c hc δ hδ a ha => by
      have hc' := abs_lt.1 hc; have hδ' := abs_lt.1 hδ; have ha' := abs_lt.1 ha
      have hcI : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ := hb34 (by
        rwa [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
      have : (δ : ℂ) ∈ gaussConnectionIntegerRangeᶜ := hb14 (by
        rwa [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
      simpa only [gaussConnectionCoordinates, Complex.ofReal_sub] using
        connectionPlusFirstCramer_eq_gamma_of_real hH a (c - δ - a) c
          (by linarith) (by linarith) (by linarith) hcI
          (by rwa [show c - a - (c - δ - a) = δ by ring])
  intro c hc δ hδ a ha
  exact h c (by simpa [Complex.ofReal_div] using hc) δ (by simpa [Complex.ofReal_div] using hδ)
    a (by simpa [Complex.ofReal_div] using ha)

/-- The second midpoint Cramer coefficient agrees with its Gamma value on a nonempty complex
open box. -/
theorem connectionPlusSecondCramer_eq_gamma_on_open_box
 :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ),
        ∀ a ∈ Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ),
          connectionPlusSecondCramerCoefficient H (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₂ (gaussConnectionCoordinates c δ a) := by
  have hb34 : Metric.ball ((3 / 4 : ℝ) : ℂ) (1 / 8 : ℝ) ⊆ gaussConnectionIntegerRangeᶜ :=
    ball_avoids_int _ _ fun n => by
      rcases (by omega : n ≤ 0 ∨ 1 ≤ n) with hn | hn
      · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
        rw [abs_of_nonpos (by linarith)]; linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]; linarith
  have hbn14 : Metric.ball ((-(1 / 4) : ℝ) : ℂ) (1 / 16 : ℝ) ⊆ gaussConnectionIntegerRangeᶜ :=
    ball_avoids_int _ _ fun n => by
      rcases (by omega : n ≤ -1 ∨ 0 ≤ n) with hn | hn
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn
        rw [abs_of_nonpos (by linarith)]; linarith
      · have : (0 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_nonneg (by linarith)]; linarith
  have h := eq_on_three_balls (3 / 4) (1 / 8) (-(1 / 4)) (1 / 16) (1 / 2) (1 / 16)
    (by norm_num) (by norm_num) (by norm_num) hb34 hbn14
    (connectionPlusSecondCramerCoefficient H) gaussConnectionPlusGammaCoefficient₂
    (fun _ hp => connectionPlusSecondCramerCoefficient_differentiableAt hH hp)
    (fun _ hp => gaussConnectionPlusGammaCoefficient₂_differentiableAt hp)
    fun c hc δ hδ a ha => by
      have hc' := abs_lt.1 hc; have hδ' := abs_lt.1 hδ; have ha' := abs_lt.1 ha
      have hcI : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ := hb34 (by
        rwa [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
      have := hbn14 (by
        rwa [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
      simpa only [gaussConnectionCoordinates, Complex.ofReal_sub] using
        connectionPlusSecondCramer_eq_gamma_of_real hH a (c - δ - a) c
          (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hcI
          (by rwa [show c - a - (c - δ - a) = δ by ring])
  intro c hc δ hδ a ha
  exact h c (by simpa [Complex.ofReal_div] using hc) δ (by simpa [Complex.ofReal_div] using hδ)
    a (by simpa [Complex.ofReal_div] using ha)


end
end DOZZ.Proofs
