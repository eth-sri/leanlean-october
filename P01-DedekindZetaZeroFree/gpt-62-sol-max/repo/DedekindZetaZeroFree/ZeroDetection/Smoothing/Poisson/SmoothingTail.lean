module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Coefficients

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorTail

noncomputable section

open DedekindZetaZeroFree NumberField Filter Topology
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def smoothedTail (F : Type) [Field F] [NumberField F] (U β γ : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ) then
      (DetectorDef.a F U n : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)
    else 0

private lemma r'_sub_r : DetectorDef.r' - DetectorDef.r = 1 / 200 := by
  norm_num [DetectorDef.r, DetectorDef.r']

lemma exp_neg_mul_cube_le (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t) * t ^ 3 ≤ 6 := by
  rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos t)]
  have h := Real.pow_div_factorial_le_exp t ht 3
  norm_num [Nat.factorial] at h
  linarith

/-- Cubic decay of the exponential weight, with the scale made explicit. -/
lemma exp_neg_div_le (N Y : ℝ) (hN : 0 < N) (hY : 0 < Y) :
    Real.exp (-N / Y) ≤ 6 * Y ^ 3 * N ^ (-3 : ℝ) := by
  rw [Real.rpow_neg hN.le, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (pow_pos hN 3), neg_div]
  have h := mul_le_mul_of_nonneg_right (exp_neg_mul_cube_le (N / Y) (by positivity))
    (pow_nonneg hY.le 3)
  rwa [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hY.ne'] at h

/-- The coefficient and the inverse norm power are uniformly bounded before
applying the exponential weight. -/
lemma coefficient_norm_le (U β γ Ca : ℝ) (hβ : DetectorDef.σ₀ ≤ β) (hCa : 0 ≤ Ca)
    (ω : Detector.PrimitiveFrequencyCharacter F) (n : Ideal (𝓞 F)) (hn : n ≠ ⊥)
    (ha : |DetectorDef.a F U n| ≤ Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ)) :
    ‖(DetectorDef.a F U n : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I))‖ ≤ Ca := by
  have hN : 0 < Ideal.absNorm n := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  have hN₀ : (0 : ℝ) < Ideal.absNorm n := by exact_mod_cast hN
  have hN₁ : (1 : ℝ) ≤ Ideal.absNorm n := by exact_mod_cast hN
  have hω := RayUnitary.ray_character_norm_le_one F _ ω.conductor_ne_zero ω.character n
  have hs : 1 / 10 ≤ DetectorDef.σ₀ := by norm_num [DetectorDef.σ₀]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos hN]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, neg_zero, add_zero]
  calc _ ≤ (Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ) * 1) * (Ideal.absNorm n : ℝ) ^ (-β) := by
        gcongr
    _ = Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 - β) := by
      rw [mul_one, mul_assoc, ← Real.rpow_add hN₀, sub_eq_add_neg]
    _ ≤ Ca * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by linarith)) hCa
    _ = Ca := mul_one _

private lemma term_bound (U β γ : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F)
    (hU : 2 ≤ U) (hβ : DetectorDef.σ₀ ≤ β) (Ca : ℝ) (hCa : 0 < Ca)
    (hA : ∀ n : Ideal (𝓞 F), n ≠ ⊥ →
      |DetectorDef.a F U n| ≤ Ca * (Ideal.absNorm n : ℝ) ^ (1 / 10 : ℝ))
    (n : Ideal (𝓞 F)) :
    ‖(if n ≠ ⊥ ∧ U ^ DetectorDef.r' < (Ideal.absNorm n : ℝ) then
      (DetectorDef.a F U n : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)
      else 0)‖ ≤
      48 * Ca * U ^ (3 * DetectorDef.r) * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) *
        (Ideal.absNorm n : ℝ) ^ (-2 : ℝ) := by
  let N : ℝ := Ideal.absNorm n
  let Y := U ^ DetectorDef.r
  have hU₀ : 0 < U := by linarith
  have hY : 0 < Y := Real.rpow_pos_of_pos hU₀ _
  split_ifs with h
  · obtain ⟨hn, hcut⟩ := h
    have hN₁ : 1 ≤ N := by
      change (1 : ℝ) ≤ (Ideal.absNorm n : ℝ)
      exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)))
    have hN : 0 < N := by linarith
    have hsplit : U ^ DetectorDef.r' = U ^ (1 / 200 : ℝ) * Y := by
      rw [show Y = U ^ DetectorDef.r from rfl, ← Real.rpow_add hU₀, ← r'_sub_r]
      congr 1
      ring
    have hX : U ^ (1 / 200 : ℝ) ≤ N / Y := (le_div_iff₀ hY).2 (hsplit.symm ▸ hcut.le)
    have hm : Real.exp (-N / Y) ≤ Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) *
        (6 * (2 * Y) ^ 3 * N ^ (-2 : ℝ)) := by
      rw [show -N / Y = -N / (2 * Y) + -N / (2 * Y) by ring, Real.exp_add]
      refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply Real.exp_le_exp.mpr
        rw [show -N / (2 * Y) = -(N / Y) / 2 by ring]
        linarith
      · refine (exp_neg_div_le N (2 * Y) hN (by positivity)).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN₁ (by norm_num)) (by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    change _ * Real.exp (-N / Y) ≤ _
    refine (mul_le_mul (coefficient_norm_le U β γ Ca hβ hCa.le ω n hn (hA n hn)) hm
      (by positivity) hCa.le).trans_eq ?_
    have hY₃ : U ^ (3 * DetectorDef.r) = Y ^ 3 := by
      dsimp [Y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU₀.le]
      congr 1
      push_cast
      ring
    rw [hY₃]
    change _ = 48 * Ca * Y ^ 3 * _ * N ^ (-2 : ℝ)
    ring
  · rw [norm_zero]
    positivity

theorem smoothedTail_bound :
    ∃ C A : ℝ, 0 < C ∧ ∀ (U β γ : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F),
      2 ≤ U → DetectorDef.σ₀ ≤ β → β ≤ 1 →
        ‖smoothedTail F U β γ ω‖ ≤ C * U ^ A * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) := by
  obtain ⟨Ca, hCa, hA⟩ := DetectorCoefficients.abs_a_le F (1 / 10 : ℝ) (by norm_num)
  have hsum : Summable (fun n : Ideal (𝓞 F) => (Ideal.absNorm n : ℝ) ^ (-2 : ℝ)) :=
    Odlyzko.summable_ideal_absNorm_rpow F (σ := 2) (by norm_num)
  have hS0 : 0 ≤ ∑' n : Ideal (𝓞 F), (Ideal.absNorm n : ℝ) ^ (-2 : ℝ) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨48 * Ca * (∑' n : Ideal (𝓞 F), (Ideal.absNorm n : ℝ) ^ (-2 : ℝ)) + 1,
    3 * DetectorDef.r, ?_, ?_⟩
  · have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 48) hCa.le) hS0
    linarith
  intro U β γ ω hU hβ hβ1
  have hU0 : (0 : ℝ) < U := by linarith
  have hE : 0 ≤ Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) := (Real.exp_pos _).le
  have hYE : 0 ≤ U ^ (3 * DetectorDef.r) * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) :=
    mul_nonneg (Real.rpow_nonneg hU0.le _) hE
  have hdom := hsum.hasSum.mul_left
    (48 * Ca * U ^ (3 * DetectorDef.r) * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2))
  unfold smoothedTail
  have hb := tsum_of_norm_bounded hdom (fun n =>
    term_bound U β γ ω hU hβ Ca hCa (fun n hn => hA U hU n hn) n)
  refine le_trans hb ?_
  nlinarith [hYE, hS0, hCa]

theorem smoothedTail_tendsto_zero :
    ∀ ε : ℝ, 0 < ε → ∃ U₀ : ℝ, 2 ≤ U₀ ∧
      ∀ (U β γ : ℝ) (ω : Detector.PrimitiveFrequencyCharacter F),
        U₀ ≤ U → DetectorDef.σ₀ ≤ β → β ≤ 1 → ‖smoothedTail F U β γ ω‖ < ε := by
  intro ε hε
  obtain ⟨C, A, hC, hbd⟩ := smoothedTail_bound (F := F)
  have hx : Tendsto (fun U : ℝ => U ^ (1 / 200 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hT : Tendsto (fun x : ℝ => x ^ (200 * A) * Real.exp (-(1 / 2) * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (200 * A) (1 / 2) (by norm_num)
  have hlim : Tendsto (fun U : ℝ => C * ((U ^ (1 / 200 : ℝ)) ^ (200 * A) *
      Real.exp (-(1 / 2) * U ^ (1 / 200 : ℝ)))) atTop (𝓝 0) := by
    have h := (hT.comp hx).const_mul C
    rw [mul_zero] at h
    exact h
  have hev := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp hev
  refine ⟨max U₁ 2, le_max_right _ _, ?_⟩
  intro U β γ ω hU hβ hβ1
  have hU2 : 2 ≤ U := le_trans (le_max_right _ _) hU
  have hU1 : U₁ ≤ U := le_trans (le_max_left _ _) hU
  have hU0 : (0 : ℝ) < U := by linarith
  have e1 : (U ^ (1 / 200 : ℝ)) ^ (200 * A) = U ^ A := by
    rw [← Real.rpow_mul hU0.le]
    congr 1
    ring
  have e2 : -(U ^ (1 / 200 : ℝ)) / 2 = -(1 / 2) * U ^ (1 / 200 : ℝ) := by ring
  calc ‖smoothedTail F U β γ ω‖ ≤ C * U ^ A * Real.exp (-(U ^ (1 / 200 : ℝ)) / 2) :=
        hbd U β γ ω hU2 hβ hβ1
    _ = C * ((U ^ (1 / 200 : ℝ)) ^ (200 * A) * Real.exp (-(1 / 2) * U ^ (1 / 200 : ℝ))) := by
        rw [e1, e2]; ring
    _ < ε := hU₁ U hU1

end

end DedekindZetaZeroFree.Quantitative.DetectorTail
