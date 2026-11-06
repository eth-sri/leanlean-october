/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationDiagonalConstraint
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients
public import DOZZ.Hypergeom.PhysicalRange
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits

/-! The physical normalization from continuity at the regular puncture. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology



/-- In the strict physical range, continuity at zero fixes the coefficient in
[KRV, (Fundrelation1)] to `T 0`. -/
theorem real_gauss_solution_physical_normalization
    {H} (hH : IsGaussHypergeometricFamily H)
    γ χ α₁ α₂ α₃ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hsum : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    T
    (hT : IsRealGaussSolution (gaussParameterA γ χ α₁ α₂ α₃)
      (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) T)
    (hcont : ContinuousAt T 0) :
    ∀ z ∈ gaussCutPlane,
      T z = T 0 *
        (‖gaussFMinus H (gaussParameterA γ χ α₁ α₂ α₃)
          (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) z‖ ^ 2 +
        gaussCoefficientRatio (gaussParameterA γ χ α₁ α₂ α₃)
          (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) *
          ‖gaussFPlus H (gaussParameterA γ χ α₁ α₂ α₃)
            (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) z‖ ^ 2) := by
  have real_open_unit_not_int {x} (hx0 : 0 < x) (hx1 : x < 1) : ∀ n : ℤ, x ≠ (n : ℝ) := by
    intro n hn
    have hn0 : 0 ≤ n := by exact_mod_cast (show (0 : ℝ) ≤ (n : ℝ) by rw [← hn]; exact hx0.le)
    have hn1 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by rw [← hn]; exact hx1)
    have hnzero : n = 0 := by omega
    subst n
    exact hx0.ne' (by simpa using hn)
  have tendsto_real_positive_cpow_zero (c : ℝ) (hc : c < 1) : Tendsto (fun x : ℝ => (x : ℂ) ^ (1 - (c : ℂ))) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let F : Filter ℝ := nhdsWithin 0 (Ioi 0)
    let e : ℝ := 1 - c
    have he : 0 < e := by dsimp [e]; linarith
    have hnorm : (fun x : ℝ => ‖(x : ℂ) ^ (1 - (c : ℂ))‖) =ᶠ[F]
        (fun x => x ^ e) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [(rfl : (x : ℂ) = (x : ℝ)), Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [e, Complex.sub_re]
    rw [tendsto_congr' hnorm]
    exact (by simpa [Function.comp_def, Real.zero_rpow he.ne'] using ((Real.continuousAt_rpow (0, e) (Or.inr he)).tendsto.comp ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℝ => e) F (nhds e)))))
  let a := gaussParameterA γ χ α₁ α₂ α₃
  let b := gaussParameterB γ χ α₁ α₂ α₃
  let c := gaussParameterC γ χ α₁
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, _, hK₂⟩ :=
    gauss_physical_parameter_range γ χ α₁ α₂ α₃ hγ hγ₂ hχ hsum hα₁ hα₂ hα₃
  have hCpos : 0 < c := by dsimp [c]; linarith [ha, hab, hbc]
  obtain ⟨coeff, δ, hrep, hconstraint⟩ :=
    realGaussSolution_canonical_diagonal_constraint hH a b c (real_open_unit_not_int hCpos hc1) (by exact real_open_unit_not_int hδ hδ1) T hT
  have hcoeff : ∀ z ∈ gaussCutPlane,
      T z = coeff * (‖gaussFMinus H a b c z‖ ^ 2 +
        gaussCoefficientRatio a b c * ‖gaussFPlus H a b c z‖ ^ 2) := fun z hz => by
    rw [hrep z hz, (mul_left_cancel₀ hK₂.ne' (by nlinarith [hconstraint, (congrArg (· * coeff) (gaussCoefficientRatio_mul_K₂_add_K₁_eq_zero a b c hK₂.ne'))]) : δ = gaussCoefficientRatio a b c * coeff)]; ring
  let F : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hrealCast : Tendsto (fun x : ℝ => (x : ℂ)) F (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hcplus : ∀ n : ℕ, (2 - (c : ℂ)) ≠ -(n : ℂ) := by
    intro n hn
    have hnRe : 2 - c = -(n : ℝ) := by
      simpa using (congrArg Complex.re hn)
    linarith [hc1, (show c = 2 + n by linarith)]
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    filter_upwards [self_mem_nhdsWithin, (by exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))] with x hx hxlt
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hx, hxlt⟩
  intro z hz
  change T z = T 0 * (‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2 +
    gaussCoefficientRatio a b c *
      ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2)
  rw [← (tendsto_nhds_unique' (by dsimp [F]; exact (isGLB_Ioi : IsGLB (Ioi (0 : ℝ)) 0).nhdsWithin_neBot ⟨1, by norm_num⟩) (by simpa using tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => ‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2 + gaussCoefficientRatio a b c * ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2) F (nhds 1) by simpa using (show Tendsto (fun x : ℝ => ‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2) F (nhds 1) by simpa using (show Tendsto (fun x : ℝ => ‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖) F (nhds 1) by simpa [Function.comp_def] using continuous_norm.continuousAt.tendsto.comp (show Tendsto (fun x : ℝ => gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) F (nhds 1) by simpa [Function.comp_def, gaussFMinus] using ((gaussFamily_tendsto_one_at_zero hH (a : ℂ) (b : ℂ) (c : ℂ) (by intro n hn; linarith [hCpos, (show c = -(n : ℝ) by exact_mod_cast hn), (neg_nonpos.mpr (Nat.cast_nonneg n) : -(n : ℝ) ≤ 0)])).comp hrealCast))).pow 2).add (tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2) F (nhds 0) by simpa using (show Tendsto (fun x : ℝ => ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖) F (nhds 0) by simpa [Function.comp_def] using continuous_norm.continuousAt.tendsto.comp (show Tendsto (fun x : ℝ => gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) F (nhds 0) by simpa [Function.comp_def, gaussFPlus] using (tendsto_real_positive_cpow_zero c hc1).mul (by exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcplus).comp hrealCast))).pow 2)))) ((hcont.tendsto.comp hrealCast).congr' (by filter_upwards [hcut] with x hx; exact hcoeff (x : ℂ) hx)) : coeff = T 0)]
  exact hcoeff z hz

end DOZZ.Proofs
