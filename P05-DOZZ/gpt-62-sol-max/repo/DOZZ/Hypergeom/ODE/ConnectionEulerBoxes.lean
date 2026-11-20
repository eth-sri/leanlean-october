/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionAnalyticContinuation
import DOZZ.Complex.Identity

/-! A common real-to-complex continuation argument for all four Euler coefficients. -/

public section

open Filter Set

namespace DOZZ.Proofs

private theorem intCast_abs_sub_lower_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
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

theorem gaussConnection_real_ball_avoids_integers (q r : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hr : r < min q (1 - q)) :
    Metric.ball (q : ℂ) r ⊆ gaussConnectionIntegerRangeᶜ := by
  intro z hz hzInt
  rcases hzInt with ⟨n, hn⟩
  subst z
  have hdist : ‖(n : ℂ) - (q : ℂ)‖ < r := by
    have hball := Metric.mem_ball.mp hz
    simpa [dist_eq_norm] using hball
  have hdistLower : min q (1 - q) ≤ ‖(n : ℂ) - (q : ℂ)‖ := by
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

/-- The radius-`1/16` ball centered at `-1/4` avoids the integer lattice. -/
theorem gaussConnection_negativeQuarter_ball_avoids_integers :
    Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ) ⊆ gaussConnectionIntegerRangeᶜ := by
  intro z hz hzInt
  rcases hzInt with ⟨n, hn⟩
  subst z
  have hball := Metric.mem_ball.mp hz
  have hnorm : ‖(n : ℂ) - (-(1 / 4 : ℂ))‖ = |(n : ℝ) + 1 / 4| := by
    rw [show (n : ℂ) - (-(1 / 4 : ℂ)) = (((n : ℝ) + 1 / 4 : ℝ) : ℂ) by
      push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hdist : |(n : ℝ) + 1 / 4| < 1 / 16 := by
    rw [dist_eq_norm, hnorm] at hball
    exact hball
  have hncase : n ≤ -1 ∨ 0 ≤ n := by omega
  rcases hncase with hnneg | hnnonneg
  · have hnR : (n : ℝ) ≤ -1 := by exact_mod_cast hnneg
    have hpos : (n : ℝ) + 1 / 4 ≤ 0 := by linarith
    rw [abs_of_nonpos hpos] at hdist
    norm_num at hdist
    linarith
  · have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hnnonneg
    rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) + 1 / 4)] at hdist
    norm_num at hdist
    linarith

/-- Identity on a complex disk from equality on a possibly smaller real interval. -/
private theorem eqOn_ball_of_real_diameter_subset (a r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (a : ℂ) r))
    (hg : DifferentiableOn ℂ g (Metric.ball (a : ℂ) r))
    (heq : ∀ x : ℝ, |x - a| < s → f x = g x) : EqOn f g (Metric.ball (a : ℂ) r) :=
  (hf.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd Metric.isOpen_ball) (convex_ball _ _).isPreconnected
    (Metric.mem_ball_self hr) (frequently_eq_of_real_interval a s hs f g heq)

private theorem real_mem_complexBall {x a r s : ℝ} (hx : |x - a| < s) (hs : s ≤ r) :
    (x : ℂ) ∈ Metric.ball (a : ℂ) r := by
  simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using hx.trans_le hs

section
variable {f g : ℂ × ℂ × ℂ → ℂ} (hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p)
  (hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p)
include hf hg

/-- Continue an Euler coefficient identity from the real box in `(c, δ, a)` coordinates.
The real intervals need only fit inside the complex disks. -/
theorem gaussConnection_eq_on_box_of_real
    {c₀ δ₀ a₀ rc rd ra s : ℝ} (hs : 0 < s) (hc : s ≤ rc) (hd : s ≤ rd) (ha : s ≤ ra)
    (hC : Metric.ball (c₀ : ℂ) rc ⊆ gaussConnectionIntegerRangeᶜ)
    (hD : Metric.ball (δ₀ : ℂ) rd ⊆ gaussConnectionIntegerRangeᶜ)
    (heq : ∀ c δ a : ℝ, |c - c₀| < s → |δ - δ₀| < s → |a - a₀| < s →
      (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ → (δ : ℂ) ∈ gaussConnectionIntegerRangeᶜ →
      f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a)) :
    ∀ c ∈ Metric.ball (c₀ : ℂ) rc, ∀ δ ∈ Metric.ball (δ₀ : ℂ) rd,
      ∀ a ∈ Metric.ball (a₀ : ℂ) ra,
        f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a) := by
  have hcoord {c δ : ℂ} (a : ℂ) (hc' : c ∈ Metric.ball (c₀ : ℂ) rc)
      (hd' : δ ∈ Metric.ball (δ₀ : ℂ) rd) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using And.intro (hC hc') (hD hd')
  have hcomp (F : ℂ × ℂ × ℂ → ℂ)
      (hF : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ F p)
      (U : Set ℂ) (L : ℂ → ℂ × ℂ × ℂ) (hL : Differentiable ℂ L)
      (hLU : MapsTo L U gaussConnectionParameterDomain) : DifferentiableOn ℂ (F ∘ L) U :=
    fun z hz => ((hF _ (hLU hz)).comp z (hL z)).differentiableWithinAt
  have first (δ a : ℝ) (hδ : |δ - δ₀| < s) (hA : |a - a₀| < s) :
      ∀ c ∈ Metric.ball (c₀ : ℂ) rc,
        f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a) := by
    have hd' := real_mem_complexBall hδ hd
    let L := fun c : ℂ => gaussConnectionCoordinates c δ a
    have hL : Differentiable ℂ L := by dsimp [L, gaussConnectionCoordinates]; fun_prop
    have hLU : MapsTo L (Metric.ball (c₀ : ℂ) rc) gaussConnectionParameterDomain :=
      fun _ hz => hcoord _ hz hd'
    exact eqOn_ball_of_real_diameter_subset c₀ rc s (hs.trans_le hc) hs
      (hcomp f hf _ L hL hLU) (hcomp g hg _ L hL hLU)
      (fun c h => heq c δ a h hδ hA (hC (real_mem_complexBall h hc)) (hD hd'))
  have second (c : ℂ) (hc' : c ∈ Metric.ball (c₀ : ℂ) rc) (a : ℝ) (hA : |a - a₀| < s) :
      ∀ δ ∈ Metric.ball (δ₀ : ℂ) rd,
        f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a) := by
    let L := fun δ : ℂ => gaussConnectionCoordinates c δ a
    have hL : Differentiable ℂ L := by dsimp [L, gaussConnectionCoordinates]; fun_prop
    have hLU : MapsTo L (Metric.ball (δ₀ : ℂ) rd) gaussConnectionParameterDomain :=
      fun _ hz => hcoord _ hc' hz
    exact eqOn_ball_of_real_diameter_subset δ₀ rd s (hs.trans_le hd) hs
      (hcomp f hf _ L hL hLU) (hcomp g hg _ L hL hLU)
      (fun δ hδ => first δ a hδ hA c hc')
  intro c hc' δ hd'
  let L := fun a : ℂ => gaussConnectionCoordinates c δ a
  have hL : Differentiable ℂ L := by dsimp [L, gaussConnectionCoordinates]; fun_prop
  have hLU : MapsTo L (Metric.ball (a₀ : ℂ) ra) gaussConnectionParameterDomain :=
    fun z _ => hcoord z hc' hd'
  exact eqOn_ball_of_real_diameter_subset a₀ ra s (hs.trans_le ha) hs
    (hcomp f hf _ L hL hLU) (hcomp g hg _ L hL hLU)
    (fun a hA => second c hc' a hA δ hd')

/-- Continue the Euler identity from the positive-excess region to its open box. -/
theorem gaussConnection_eq_on_EulerBox1
    (heq : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < a - c + 1 → 0 < b - c + 1 → 0 < c - a - b →
      (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ →
      ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ → f (a, b, c) = g (a, b, c)) :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
        ∀ a ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
          f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a) := by
  have h := gaussConnection_eq_on_box_of_real hf hg
    (c₀ := 3 / 4) (δ₀ := 1 / 4) (a₀ := 1 / 4) (rc := 1 / 8) (rd := 1 / 8) (ra := 1 / 8)
    (s := 1 / 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (gaussConnection_real_ball_avoids_integers _ _ (by norm_num) (by norm_num) (by norm_num))
    (gaussConnection_real_ball_avoids_integers _ _ (by norm_num) (by norm_num) (by norm_num)) (by
      intro c δ a hc hδ ha hcI hδI
      obtain ⟨hc₁, hc₂⟩ := abs_lt.mp hc
      obtain ⟨hδ₁, hδ₂⟩ := abs_lt.mp hδ
      obtain ⟨ha₁, ha₂⟩ := abs_lt.mp ha
      simpa only [gaussConnectionCoordinates, Complex.ofReal_sub] using
        heq a (c - δ - a) c (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hcI (by
        rwa [show c - a - (c - δ - a) = δ by ring]))
  simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] using h

/-- Continue the Euler identity from the negative-excess region to its open box. -/
theorem gaussConnection_eq_on_EulerBox2
    (heq : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c - a → 0 < c - b → 0 < a - c + 1 → 0 < b - c + 1 → 0 < 1 - a → 0 < 1 - b → c - a - b < 0 →
      (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ →
      ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ → f (a, b, c) = g (a, b, c)) :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (-(1 / 4) : ℂ) (1 / 16 : ℝ),
        ∀ a ∈ Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ),
          f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a) := by
  have h := gaussConnection_eq_on_box_of_real hf hg
    (c₀ := 3 / 4) (δ₀ := -(1 / 4)) (a₀ := 1 / 2) (rc := 1 / 8) (rd := 1 / 16) (ra := 1 / 16)
    (s := 1 / 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (gaussConnection_real_ball_avoids_integers _ _ (by norm_num) (by norm_num) (by norm_num))
    (by simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] using
      gaussConnection_negativeQuarter_ball_avoids_integers) (by
      intro c δ a hc hδ ha hcI hδI
      obtain ⟨hc₁, hc₂⟩ := abs_lt.mp hc
      obtain ⟨hδ₁, hδ₂⟩ := abs_lt.mp hδ
      obtain ⟨ha₁, ha₂⟩ := abs_lt.mp ha
      simpa only [gaussConnectionCoordinates, Complex.ofReal_sub] using
        heq a (c - δ - a) c (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hcI (by
        rwa [show c - a - (c - δ - a) = δ by ring]))
  simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] using h

end

end DOZZ.Proofs
