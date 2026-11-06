module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierSaw

/-!
# The sawtooth series `∑ (-1)^m sin(mα)/m = -α/2` for `|α| < π`

The series is only conditionally convergent.  Its convergence follows from Dirichlet's test
(Mathlib: `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`), and its sum from Abel's
theorem (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`) combined with the closed form
`sawS μ α = -2 arctan (sin α / (e^μ + cos α))` of the Poisson means (`sawS_eq_arctan`).
This is what gives the series of (2.1) for `τ` a meaning as the limit of its partial sums.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- Closed form of the sawtooth Poisson series:
`∑_{m≥1} 2(-1)^m e^{-μ m} sin(mα)/m = -2 arctan (sin α / (e^μ + cos α))`. -/
theorem sawS_eq_arctan {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    sawS μ α = -2 * Real.arctan (Real.sin α / (Real.exp μ + Real.cos α)) := by
  have hE : 1 < Real.exp μ := by simpa using hμ
  have hd (x : ℝ) : HasDerivAt (fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y))) 0 x := by
    have ha : Real.exp μ + Real.cos x ≠ 0 := by linarith [Real.neg_one_le_cos x]
    have h3 := (hasDerivAt_sawS hμ x).add
      (((Real.hasDerivAt_sin x).div ((hasDerivAt_const x (Real.exp μ)).add (Real.hasDerivAt_cos x)) ha).arctan.const_mul 2)
    refine (show HasDerivAt (fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y))) _ x from h3).congr_deriv ?_
    have hs := Real.sin_sq_add_cos_sq x
    unfold Xi
    dsimp only [Pi.div_apply, Pi.add_apply]
    rw [Real.cos_add_pi, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
    set E := Real.exp μ
    set c := Real.cos x
    set s := Real.sin x
    have hE0 : E ≠ 0 := by positivity
    rw [show (E + E⁻¹) / 2 - -c = ((E + c) ^ 2 + s ^ 2) / (2 * E) by
      field_simp; linear_combination -hs, ← sub_eq_zero]
    field_simp
    linear_combination hs
  have hc := is_const_of_deriv_eq_zero
    (f := fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y)))
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) α 0
  simp only [sawS_zero, Real.sin_zero, zero_div, Real.arctan_zero, mul_zero, add_zero] at hc
  linarith

/-! ### Convergence of the sawtooth series (Dirichlet test) -/

/-- Telescoping identity for `∑ sin(kθ)`. -/
theorem two_sin_half_mul_sum_sin (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * ∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * θ) =
      Real.cos (θ / 2) - Real.cos (((n : ℝ) + 1 / 2) * θ) := by
  induction n with
  | zero => simp; ring_nf
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : Real.cos (((n : ℝ) + 1 / 2) * θ) - Real.cos ((((n + 1 : ℕ) : ℝ) + 1 / 2) * θ) =
        2 * Real.sin (θ / 2) * Real.sin (((n + 1 : ℕ) : ℝ) * θ) := by
      rw [show ((n : ℝ) + 1 / 2) * θ = ((n + 1 : ℕ) : ℝ) * θ - θ / 2 by push_cast; ring,
        show (((n + 1 : ℕ) : ℝ) + 1 / 2) * θ = ((n + 1 : ℕ) : ℝ) * θ + θ / 2 by push_cast; ring,
        Real.cos_sub, Real.cos_add]; ring
    linarith

theorem abs_sum_sin_le {θ : ℝ} (h : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    |∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have h2 : |2 * Real.sin (θ / 2) * ∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * θ)| ≤ 2 := by
    rw [two_sin_half_mul_sum_sin]
    exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one (θ / 2), Real.abs_cos_le_one (((n : ℝ) + 1 / 2) * θ)])
  rw [abs_mul, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)] at h2
  rw [le_div_iff₀ (abs_pos.2 h)]
  linarith

theorem cauchySeq_sawtooth {α : ℝ} (hα : |α| < π) :
    CauchySeq (fun N : ℕ => ∑ i ∈ Finset.range N,
      (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)) := by
  have hα' := abs_lt.1 hα
  have hs : 0 < Real.sin ((α + π) / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [show (fun N : ℕ => ∑ i ∈ Finset.range N,
      (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)) =
      fun n : ℕ => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) •
        Real.sin (((i + 1 : ℕ) : ℝ) * (α + π)) by
    funext N; refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, Real.sin_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, smul_eq_mul]; ring]
  exact Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (E := ℝ)
    (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) (z := fun i : ℕ => Real.sin (((i + 1 : ℕ) : ℝ) * (α + π)))
    (b := 1 / |Real.sin ((α + π) / 2)|)
    (fun i j hij => one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))
    (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (fun n => by rw [Real.norm_eq_abs]; exact abs_sum_sin_le hs.ne' n)

theorem arctan_sin_div_one_add_cos {α : ℝ} (hα : |α| < π) :
    Real.arctan (Real.sin α / (1 + Real.cos α)) = α / 2 := by
  have hα' := abs_lt.1 hα
  have hc : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h2 : α = 2 * (α / 2) := by ring
  rw [show Real.sin α / (1 + Real.cos α) = Real.tan (α / 2) by
    conv_lhs => rw [h2, Real.sin_two_mul, Real.cos_two_mul]
    rw [Real.tan_eq_sin_div_cos]; field_simp; ring]
  exact Real.arctan_tan (by linarith) (by linarith)

/-- The classical sawtooth series: `∑_{m≥1} (-1)^m sin(mα)/m = -α/2` for `|α| < π` (as the limit
of the partial sums; the series is only conditionally convergent). -/
theorem tendsto_sawtooth {α : ℝ} (hα : |α| < π) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)) atTop (𝓝 (-α / 2)) := by
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete (cauchySeq_sawtooth hα)
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) / ((n : ℝ) + 1)) hℓ
  let G : ℝ → ℝ := fun x => -x⁻¹ * Real.arctan (Real.sin α / (x⁻¹ + Real.cos α))
  have hev : (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
      ((n : ℝ) + 1) * x ^ n) =ᶠ[𝓝[<] (1 : ℝ)] G := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hx0 : 0 < x := hx.1
    have h1 := sawS_eq_arctan (by linarith [Real.log_neg hx0 hx.2] : 0 < -Real.log x) α
    unfold sawS at h1
    rw [neg_neg, Real.exp_neg, Real.exp_log hx0] at h1
    simp_rw [show ∀ n : ℕ, 2 * (-1 : ℝ) ^ (n + 1) * x ^ (n + 1) / ((n : ℝ) + 1) *
        Real.sin (((n + 1 : ℕ) : ℝ) * α) =
        (2 * x) * ((-1 : ℝ) ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) / ((n : ℝ) + 1) * x ^ n) by
      intro n; rw [pow_succ x n]; ring] at h1
    rw [tsum_mul_left] at h1
    show _ = -x⁻¹ * _
    have : x ≠ 0 := hx0.ne'
    generalize (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
      ((n : ℝ) + 1) * x ^ n) = S at h1 ⊢
    generalize Real.arctan (Real.sin α / (x⁻¹ + Real.cos α)) = A at h1 ⊢
    field_simp at h1 ⊢; linarith
  have hc1 : 0 < 1 + Real.cos α := by
    have h := abs_lt.1 hα
    have hcos : 2 * Real.cos (α / 2) ^ 2 = 1 + Real.cos α := by
      conv_rhs => rw [show α = 2 * (α / 2) by ring, Real.cos_two_mul]
      ring
    have hc : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    linarith [show 0 < 2 * Real.cos (α / 2) ^ 2 by positivity]
  have h1 : ContinuousAt (fun x : ℝ => x⁻¹) 1 := continuousAt_inv₀ one_ne_zero
  have hcont : ContinuousAt G 1 :=
    h1.neg.mul (Real.continuous_arctan.continuousAt.comp
      (continuousAt_const.div (h1.add continuousAt_const) (by simp; linarith)))
  have hlim : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 (-α / 2)) := by
    simpa [G, arctan_sin_div_one_add_cos hα, neg_div] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  rwa [tendsto_nhds_unique (hab.congr' hev) hlim] at hℓ

end PottsDiscontinuity.Bethe
