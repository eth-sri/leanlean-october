module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Defs

/-!
# The sawtooth series, the closed form of `Ψ`, and Dirichlet/Abel convergence
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

private theorem integral_id_mul_sin {m : ℕ} (hm : m ≠ 0) :
    ∫ β in (-π)..π, β * Real.sin (m * β) = -(2 * π * (-1) ^ m / m) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -π) (b := π)
    (u := fun x : ℝ => x) (u' := fun _ => (1 : ℝ)) (v := fun x : ℝ => -(Real.cos (m * x) / m))
    (v' := fun x : ℝ => Real.sin (m * x))
    (fun x _ => hasDerivAt_id x)
    (fun x _ => by
      have h1 : HasDerivAt (fun x : ℝ => (m : ℝ) * x) (m : ℝ) x := by simpa using (hasDerivAt_id x).const_mul (m : ℝ)
      exact ((h1.cos).div_const (m : ℝ)).neg.congr_deriv (by field_simp))
    (by simp) (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h3 : (∫ x in (-π)..π, (1 : ℝ) * -(Real.cos (m * x) / m)) = 0 := by
    simp_rw [show ∀ x : ℝ, (1 : ℝ) * -(Real.cos (m * x) / m) = -(m : ℝ)⁻¹ * Real.cos (m * x) by intro; field_simp]
    rw [intervalIntegral.integral_const_mul, integral_cos_nat_mul hm, mul_zero]
  have h2 : Real.cos (m * -π) = (-1) ^ m := by rw [mul_neg, Real.cos_neg, Real.cos_nat_mul_pi]
  rw [h, h3, Real.cos_nat_mul_pi, h2]; field_simp; ring

noncomputable def sawS (μ α : ℝ) : ℝ :=
  ∑' n : ℕ, 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α)

theorem sawS_zero (μ : ℝ) : sawS μ 0 = 0 := by unfold sawS; simp

theorem hasSum_xiConv_neg_id {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    HasSum (fun n : ℕ => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / ((n : ℝ) + 1) *
      Real.sin (((n + 1 : ℕ) : ℝ) * α)) (xiConv μ (fun β => -β) α) := by
  have hc0 (m : ℕ) : cosCoeff (fun β => -β) m = 0 := by
    unfold cosCoeff; dsimp only
    have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) (fun x => -x * Real.cos ((m : ℝ) * x))
    simp only [neg_neg] at h
    simp_rw [mul_neg, Real.cos_neg, neg_mul] at h
    simp_rw [neg_mul]
    rw [intervalIntegral.integral_neg] at h ⊢; linarith
  have hs0 (n : ℕ) : sinCoeff (fun β => -β) (n + 1) = 2 * π * (-1) ^ (n + 1) / ((n : ℝ) + 1) := by
    unfold sinCoeff
    simp_rw [show ∀ β : ℝ, -β * Real.sin (((n + 1 : ℕ) : ℝ) * β) = -(β * Real.sin (((n + 1 : ℕ) : ℝ) * β)) by intro; ring]
    rw [intervalIntegral.integral_neg, integral_id_mul_sin (by omega)]; push_cast; ring
  have h := hasSum_xiConv hμ (continuous_neg.intervalIntegrable _ _) α
  simp_rw [hc0, hs0] at h
  simp only [mul_zero, zero_add, sub_zero] at h
  refine h.congr_fun fun n => ?_
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  have := Real.pi_pos.ne'; field_simp

theorem xiConv_neg_id {μ : ℝ} (hμ : 0 < μ) (α : ℝ) : xiConv μ (fun β => -β) α = sawS μ α :=
  (hasSum_xiConv_neg_id hμ α).tsum_eq.symm

theorem hasDerivAt_sawS {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    HasDerivAt (sawS μ) (Xi μ (α + π) - 1) α := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hu : Summable (fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hr.le (by rw [Real.exp_lt_one_iff]; linarith)).mul_left (2 * Real.exp (-μ))).congr fun _ => by ring
  have hd := hasDerivAt_tsum (𝕜 := ℝ) (y₀ := 0) hu
    (g := fun (n : ℕ) (y : ℝ) => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * y))
    (g' := fun (n : ℕ) (y : ℝ) => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * y))
    (fun n y => by
      have h1 : HasDerivAt (fun y : ℝ => ((n + 1 : ℕ) : ℝ) * y) ((n + 1 : ℕ) : ℝ) y := by
        simpa using (hasDerivAt_id y).const_mul (((n + 1 : ℕ) : ℝ))
      exact ((h1.sin).const_mul _).congr_deriv (by push_cast; field_simp))
    (fun n y => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_pos two_pos, abs_of_pos (pow_pos hr _), mul_one]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))
    (by simp) α
  have hsum : (∑' n : ℕ, 2 * (-1 : ℝ) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α)) =
      Xi μ (α + π) - 1 :=
    ((hasSum_Xi_cos hμ (α + π)).congr_fun fun n => by
      rw [mul_add, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]; ring).tsum_eq
  rwa [hsum] at hd

theorem PsiFn_eq_neg_sub_sawS {Δ : ℝ} (hΔ : Δ < -1) (α : ℝ) :
    PsiFn Δ α = -α - sawS (2 * lamOf Δ) α := by
  have hlam := lamOf_pos hΔ; have hcosh := cosh_lamOf hΔ
  have hd (x : ℝ) : HasDerivAt (fun y => PsiFn Δ y + y + sawS (2 * lamOf Δ) y) 0 x := by
    have h1 := hasDerivAt_theta_kMap_left hlam hcosh x π
    have h2 := hasDerivAt_theta_kMap_left hlam hcosh x (-π)
    rw [kMap_pi] at h1; rw [kMap_neg_pi, sub_neg_eq_add] at h2
    have hPsi : HasDerivAt (PsiFn Δ) (-Xi (2 * lamOf Δ) (x + π)) x :=
      ((h2.add h1).div_const 2).congr_deriv (by unfold Xi; rw [Real.cos_sub_pi, Real.cos_add_pi]; ring)
    exact ((hPsi.add (hasDerivAt_id x)).add (hasDerivAt_sawS (by linarith) x)).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) α 0
  have hp0 : PsiFn Δ 0 = 0 := by unfold PsiFn; rw [kMap_zero]; simp [theta]
  simp only [hp0, sawS_zero, add_zero] at hc; linarith

theorem sawS_eq_arctan {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    sawS μ α = -2 * Real.arctan (Real.sin α / (Real.exp μ + Real.cos α)) := by
  have hE : 1 < Real.exp μ := by simpa using hμ
  have hd (x : ℝ) : HasDerivAt (fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y))) 0 x := by
    have hEc : Real.exp μ + Real.cos x ≠ 0 := by linarith [Real.neg_one_le_cos x]
    have h1 : HasDerivAt (fun y => Real.sin y / (Real.exp μ + Real.cos y))
        ((Real.cos x * (Real.exp μ + Real.cos x) - Real.sin x * (0 + -Real.sin x)) /
          (Real.exp μ + Real.cos x) ^ 2) x :=
      (Real.hasDerivAt_sin x).div ((hasDerivAt_const x (Real.exp μ)).add (Real.hasDerivAt_cos x)) hEc
    have h2 := h1.arctan.const_mul 2
    have h3 := (hasDerivAt_sawS hμ x).add h2
    rw [show (fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y))) =
      sawS μ + fun y => 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y)) from rfl]
    refine h3.congr_deriv ?_
    unfold Xi; rw [Real.cos_add_pi, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
    set E := Real.exp μ; set c := Real.cos x; set s := Real.sin x
    have hs := Real.sin_sq_add_cos_sq x
    have hE0 : E ≠ 0 := by positivity
    have hQpos : 0 < E ^ 2 + 2 * E * c + 1 := by nlinarith [sq_nonneg (E - 1), Real.neg_one_le_cos x]
    have hQne : E ^ 2 + 2 * E * c + 1 ≠ 0 := hQpos.ne'
    have h4 : (E + E⁻¹) / 2 - -c = (E ^ 2 + 2 * E * c + 1) / (2 * E) := by field_simp; ring
    have h5 : 1 + (s / (E + c)) ^ 2 = (E ^ 2 + 2 * E * c + 1) / (E + c) ^ 2 := by
      field_simp; linear_combination hs
    have h6 : c * (E + c) - s * (0 + -s) = E * c + 1 := by linear_combination hs
    have hQne' : 1 + E * c * 2 + E ^ 2 ≠ 0 := by linarith
    rw [h4, h5, h6]; field_simp [hE0, hEc, hQne, hQne']
    linear_combination inv_mul_cancel₀ hQne'
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) α 0
  simp only [sawS_zero, Real.sin_zero, zero_div, Real.arctan_zero, mul_zero, add_zero] at hc; linarith

theorem tendsto_sawtooth {α : ℝ} (hα : |α| < π) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)) atTop (𝓝 (-α / 2)) := by
  have hα' := abs_lt.1 hα
  have htel (θ : ℝ) (n : ℕ) : 2 * Real.sin (θ / 2) * ∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * θ) =
      Real.cos (θ / 2) - Real.cos (((n : ℝ) + 1 / 2) * θ) := by
    induction n with
    | zero => simp; ring_nf
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have e1 : ((n : ℝ) + 1 / 2) * θ = ((n + 1 : ℕ) : ℝ) * θ - θ / 2 := by push_cast; ring
      have e2 : (((n + 1 : ℕ) : ℝ) + 1 / 2) * θ = ((n + 1 : ℕ) : ℝ) * θ + θ / 2 := by push_cast; ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  have hs : 0 < Real.sin ((α + π) / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcauchy : CauchySeq (fun N : ℕ => ∑ i ∈ Finset.range N,
      (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)) := by
    have key := Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (E := ℝ)
      (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) (z := fun i : ℕ => Real.sin (((i + 1 : ℕ) : ℝ) * (α + π)))
      (b := 1 / Real.sin ((α + π) / 2))
      (fun i j hij => one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))
      (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (fun n => by
        rw [Real.norm_eq_abs, le_div_iff₀ hs]
        have h1 := congrArg abs (htel (α + π) n)
        rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos hs] at h1
        linarith [abs_sub (Real.cos ((α + π) / 2)) (Real.cos (((n : ℝ) + 1 / 2) * (α + π))),
          Real.abs_cos_le_one ((α + π) / 2), Real.abs_cos_le_one (((n : ℝ) + 1 / 2) * (α + π))])
    have heq_fn : (fun N : ℕ => ∑ i ∈ Finset.range N,
        (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)) =
        fun n : ℕ => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) • Real.sin (((i + 1 : ℕ) : ℝ) * (α + π)) := by
      ext N; refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_add, Real.sin_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, smul_eq_mul]; ring
    rwa [heq_fn]
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hℓ
  let G : ℝ → ℝ := fun x => -x⁻¹ * Real.arctan (Real.sin α / (x⁻¹ + Real.cos α))
  have hev : (fun x : ℝ => ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
      ((n : ℝ) + 1) * x ^ n) =ᶠ[𝓝[<] (1 : ℝ)] G := by
    filter_upwards [Ioo_mem_nhdsLT one_pos] with x ⟨hx0, hx1⟩
    have h1 := sawS_eq_arctan (neg_pos.mpr (Real.log_neg hx0 hx1)) α
    unfold sawS at h1
    rw [neg_neg, Real.exp_log hx0, Real.exp_neg, Real.exp_log hx0] at h1
    simp_rw [show ∀ n : ℕ, 2 * (-1 : ℝ) ^ (n + 1) * x ^ (n + 1) / ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      (2 * x) * ((-1 : ℝ) ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) / ((n : ℝ) + 1) * x ^ n)
      by intro n; rw [pow_succ]; ring] at h1
    rw [tsum_mul_left] at h1
    dsimp [G]
    generalize (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) / ((n : ℝ) + 1) * x ^ n) = S at h1 ⊢
    generalize Real.arctan (Real.sin α / (x⁻¹ + Real.cos α)) = A at h1 ⊢
    field_simp [hx0.ne']; linarith
  have hc2 : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h1cos : 1 + Real.cos α = 2 * Real.cos (α / 2) ^ 2 := by
    conv_lhs => rw [show α = 2 * (α / 2) by ring]
    rw [Real.cos_two_mul]; ring
  have hcont : ContinuousAt G 1 :=
    (continuousAt_inv₀ one_ne_zero).neg.mul <| Real.continuous_arctan.continuousAt.comp <|
      continuousAt_const.div ((continuousAt_inv₀ one_ne_zero).add continuousAt_const) (by simp [h1cos, hc2.ne'])
  have hG1 : G 1 = -α / 2 := by
    dsimp [G]; rw [inv_one, h1cos, show Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) by
      conv_lhs => rw [show α = 2 * (α / 2) by ring]; exact Real.sin_two_mul _,
      show 2 * Real.sin (α / 2) * Real.cos (α / 2) / (2 * Real.cos (α / 2) ^ 2) = Real.tan (α / 2) by
        rw [Real.tan_eq_sin_div_cos]; field_simp [hc2.ne'],
      Real.arctan_tan (by linarith) (by linarith)]; ring
  rwa [tendsto_nhds_unique (hab.congr' hev) (hG1 ▸ hcont.tendsto.mono_left nhdsWithin_le_nhds)] at hℓ

end PottsDiscontinuity.Bethe
