/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ConnectionFormulaFromBox
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Real endpoint limits identify the connection Cramer coefficients. -/

@[expose] public section

open Filter Set
open scoped Topology

namespace DOZZ.Proofs


/-- Every characterized family member tends to its normalized value `1` at the regular origin. -/
theorem gaussFamily_tendsto_one_at_zero
    {H} (hH : IsGaussHypergeometricFamily H)
    a b c (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    Tendsto (H a b c) (𝓝 0) (𝓝 1) := by
  have hchar := hH a b c hc
  have hmem : (0 : ℂ) ∈ gaussSlitPlane := by simp [gaussSlitPlane]
  simpa [(by simpa using hchar.2 0 (by norm_num))] using ((hchar.1 0 hmem).differentiableAt ((show IsOpen gaussSlitPlane by change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z : ℂ | z.re < 1}); exact (isOpen_ne.preimage Complex.continuous_im).union (isOpen_Iio.preimage Complex.continuous_re)).mem_nhds hmem)).continuousAt.tendsto

private theorem tendsto_one_sub_ofReal_cpow_zero (δ : ℂ) (hδ : 0 < δ.re) :
    Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ δ) (𝓝[Iio 1] 1) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let F : Filter ℝ := 𝓝[Iio 1] 1
  rw [tendsto_congr' (show (fun x : ℝ => ‖(1 - (x : ℂ)) ^ δ‖) =ᶠ[F] (fun x : ℝ => (1 - x) ^ δ.re) by filter_upwards [self_mem_nhdsWithin] with x hx; rw [(show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring), Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx)])]
  exact (by simpa [Function.comp_def, Real.zero_rpow hδ.ne'] using ((Real.continuousAt_rpow (0, δ.re) (Or.inr hδ)).tendsto.comp ((show Tendsto (fun x => 1 - x) F (𝓝 0) by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1)).sub (tendsto_id.mono_left nhdsWithin_le_nhds)).prodMk_nhds tendsto_const_nhds)))

/-- If the zero-basis solution has a finite real-axis endpoint limit and `Re(c-a-b)>0`,
the first midpoint Cramer coefficient is exactly that limit. The basis limits are `G₋→1` and
`G₊→0`; the separate Euler integral supplies the endpoint value in applications. -/
theorem connectionMinusFirstCramer_eq_of_endpoint_limit
    {H} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L} (hδ : 0 < (p.2.2 - p.1 - p.2.1).re)
    (hF : Tendsto (fun x : ℝ => gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionMinusFirstCramerCoefficient H p = L := by
  let δ : ℂ := p.2.2 - p.1 - p.2.1
  let F : Filter ℝ := 𝓝[Iio 1] 1
  have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
        _ = 1 - (-(n : ℂ)) := by rw [hn]
        _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    exact hp.2 (n + 1) (by simpa [δ] using hδn)
  have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
        _ = -(n : ℂ) - 1 := by rw [hn]
        _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
    apply (hp.2 (-(n + 1 : ℤ)))
    simpa [δ] using hδn
  have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp (show Tendsto (fun x => 1 - x) F (𝓝 0) by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1)).sub (tendsto_id.mono_left nhdsWithin_le_nhds))
  let C₁ := connectionMinusFirstCramerCoefficient H p
  let C₂ := connectionMinusSecondCramerCoefficient H p
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    filter_upwards [(by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)), (by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x; exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num)))] with x hxlt hxpos
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hxpos, hxlt⟩
  exact tendsto_nhds_unique' (by dsimp [F]; exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩) (show Tendsto (fun x : ℝ => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) + C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 C₁) by simpa [C₁, C₂] using (tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) by simpa [gaussGMinus, F, Function.comp_def] using (gaussFamily_tendsto_one_at_zero hH p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) hcMinus).comp harg)).add (tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) by simpa [gaussGPlus, δ, F] using (tendsto_one_sub_ofReal_cpow_zero δ hδ).mul (by exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg)))) (hF.congr' (by filter_upwards [hcut] with x hx; exact gaussFMinus_eq_connectionMidpointCramer hH hp (x : ℂ) hx))

/-- If the singularly rescaled zero-basis solution has a finite real-axis endpoint limit and
`Re(c-a-b)<0`, the second midpoint Cramer coefficient is that limit. The first one-basis term
vanishes after rescaling, while the powered second one-basis term tends to `1`. -/
theorem connectionMinusSecondCramer_eq_of_scaled_endpoint_limit
    {H} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L} (hδ : 0 < (p.1 + p.2.1 - p.2.2).re)
    (hF : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-(p.2.2 - p.1 - p.2.1)) *
        gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionMinusSecondCramerCoefficient H p = L := by
  let δ : ℂ := p.2.2 - p.1 - p.2.1
  let F : Filter ℝ := 𝓝[Iio 1] 1
  have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
        _ = 1 - (-(n : ℂ)) := by rw [hn]
        _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    exact hp.2 (n + 1) (by simpa [δ] using hδn)
  have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
        _ = -(n : ℂ) - 1 := by rw [hn]
        _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
    apply (hp.2 (-(n + 1 : ℤ)))
    simpa [δ] using hδn
  have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp (show Tendsto (fun x : ℝ => 1 - x) F (𝓝 0) by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1)).sub (tendsto_id.mono_left nhdsWithin_le_nhds))
  have hpower : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ)) F (𝓝 0) := by
    apply tendsto_one_sub_ofReal_cpow_zero (-δ)
    rw [(show (-δ).re = p.1.re + p.2.1.re - p.2.2.re by simp [δ]; ring)]
    exact (by simpa only [Complex.sub_re, Complex.add_re] using hδ)
  have hscaledPlus : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
    have heq : (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) =ᶠ[F]
        (fun x => H (p.2.2 - p.2.1) (p.2.2 - p.1)
          (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) := by
      filter_upwards [eventually_mem_nhdsWithin] with x hx
      change (1 - (x : ℂ)) ^ (-δ) *
        ((1 - (x : ℂ)) ^ δ * H (p.2.2 - p.2.1) (p.2.2 - p.1)
          (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) = _
      rw [← mul_assoc, ← Complex.cpow_add _ _ (show (1 : ℂ) - (x : ℂ) ≠ 0 by apply sub_ne_zero.mpr; exact_mod_cast (ne_of_lt (by simpa only [mem_Iio] using hx)).symm), neg_add_cancel,
        Complex.cpow_zero, one_mul]
    exact ((show Tendsto (fun x : ℝ => H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) F (𝓝 1) by exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg).congr' heq.symm)
  let C₁ := connectionMinusFirstCramerCoefficient H p
  let C₂ := connectionMinusSecondCramerCoefficient H p
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    filter_upwards [(by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)), (by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x; exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num)))] with x hxlt hxpos
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hxpos, hxlt⟩
  exact tendsto_nhds_unique' (by dsimp [F]; exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩) (show Tendsto (fun x : ℝ => C₁ * ((1 - (x : ℂ)) ^ (-δ) * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) + C₂ * ((1 - (x : ℂ)) ^ (-δ) * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) F (𝓝 C₂) by simpa [C₁, C₂] using (tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) by simpa using hpower.mul (by simpa [gaussGMinus, F, Function.comp_def] using (gaussFamily_tendsto_one_at_zero hH p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) hcMinus).comp harg))).add (tendsto_const_nhds.mul hscaledPlus)) (by simpa [C₁, C₂, δ] using hF.congr' (by filter_upwards [hcut] with x hx; rw [(gaussFMinus_eq_connectionMidpointCramer hH hp (x : ℂ) hx)]; ring))



/-- The same endpoint extraction applies to the second zero-basis solution `F₊`; its midpoint
Cramer coefficients are thus identified by the corresponding (possibly rescaled) Euler limits. -/
theorem connectionPlusFirstCramer_eq_of_endpoint_limit
    {H} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L} (hδ : 0 < (p.2.2 - p.1 - p.2.1).re)
    (hF : Tendsto (fun x : ℝ => gaussFPlus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionPlusFirstCramerCoefficient H p = L := by
  have firstCramer_eq_of_endpoint_expansion {L} {C₁} {C₂} (δ : ℂ) (hδeq : δ = p.2.2 - p.1 - p.2.1) (hδ : 0 < δ.re) (f : ℂ → ℂ) (hF : Tendsto (fun x : ℝ => f (x : ℂ)) (𝓝[Iio 1] 1) (𝓝 L)) (hExpansion : ∀ z ∈ gaussCutPlane, f z = C₁ * gaussGMinus H p.1 p.2.1 p.2.2 z + C₂ * gaussGPlus H p.1 p.2.1 p.2.2 z) : C₁ = L := by
    let F : Filter ℝ := 𝓝[Iio 1] 1
    have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
      intro n hn
      have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
        rw [hδeq]
        calc
          p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
          _ = 1 - (-(n : ℂ)) := by rw [hn]
          _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      apply hp.2 (n + 1)
      calc
        p.2.2 - p.1 - p.2.1 = δ := hδeq.symm
        _ = ((n + 1 : ℕ) : ℂ) := hδn
    have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
      intro n hn
      have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
        rw [hδeq]
        calc
          p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
          _ = -(n : ℂ) - 1 := by rw [hn]
          _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
      apply (hp.2 (-(n + 1 : ℤ)))
      simpa [hδeq] using hδn
    have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
      simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp (show Tendsto (fun x : ℝ => 1 - x) F (𝓝 0) by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1)).sub (tendsto_id.mono_left nhdsWithin_le_nhds))
    have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
      filter_upwards [(by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)), (by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x; exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num)))] with x hxlt hxpos
      change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
      right
      simp only [Complex.ofReal_re]
      exact ⟨hxpos, hxlt⟩
    exact tendsto_nhds_unique' (by dsimp [F]; exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩) (show Tendsto (fun x : ℝ => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) + C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 C₁) by simpa using (tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) by simpa [gaussGMinus, F, Function.comp_def] using (gaussFamily_tendsto_one_at_zero hH p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) hcMinus).comp harg)).add (tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) by simpa [gaussGPlus, hδeq, F] using (tendsto_one_sub_ofReal_cpow_zero δ hδ).mul (by exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg)))) (hF.congr' (by filter_upwards [hcut] with x hx; exact hExpansion (x : ℂ) hx))
  exact firstCramer_eq_of_endpoint_expansion
    (δ := p.2.2 - p.1 - p.2.1) rfl hδ (gaussFPlus H p.1 p.2.1 p.2.2)
    hF (gaussFPlus_eq_connectionMidpointCramer hH hp)

/-- The rescaled endpoint extraction also identifies the second Cramer coefficient of `F₊`. -/
theorem connectionPlusSecondCramer_eq_of_scaled_endpoint_limit
    {H} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L} (hδ : 0 < (p.1 + p.2.1 - p.2.2).re)
    (hF : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-(p.2.2 - p.1 - p.2.1)) *
        gaussFPlus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionPlusSecondCramerCoefficient H p = L := by
  have secondCramer_eq_of_scaled_endpoint_expansion {L} {C₁} {C₂} δ (hδeq : δ = p.2.2 - p.1 - p.2.1) (hδ : 0 < (-δ).re) (f : ℂ → ℂ) (hF : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) * f (x : ℂ)) (𝓝[Iio 1] 1) (𝓝 L)) (hExpansion : ∀ z ∈ gaussCutPlane, f z = C₁ * gaussGMinus H p.1 p.2.1 p.2.2 z + C₂ * gaussGPlus H p.1 p.2.1 p.2.2 z) : C₂ = L := by
    let F : Filter ℝ := 𝓝[Iio 1] 1
    have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
      intro n hn
      have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
        rw [hδeq]
        calc
          p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
          _ = 1 - (-(n : ℂ)) := by rw [hn]
          _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      apply hp.2 (n + 1)
      calc
        p.2.2 - p.1 - p.2.1 = δ := hδeq.symm
        _ = ((n + 1 : ℕ) : ℂ) := hδn
    have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
      intro n hn
      have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
        rw [hδeq]
        calc
          p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
          _ = -(n : ℂ) - 1 := by rw [hn]
          _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
      apply (hp.2 (-(n + 1 : ℤ)))
      simpa [hδeq] using hδn
    have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
      simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp (show Tendsto (fun x => 1 - x) F (𝓝 0) by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1)).sub (tendsto_id.mono_left nhdsWithin_le_nhds))
    have hscaledPlus : Tendsto
        (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
      have heq : (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) =ᶠ[F]
          (fun x => H (p.2.2 - p.2.1) (p.2.2 - p.1)
            (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) := by
        filter_upwards [eventually_mem_nhdsWithin] with x hx
        simp only [gaussGPlus]
        rw [← hδeq]
        rw [← mul_assoc, ← Complex.cpow_add _ _ (show (1 : ℂ) - (x : ℂ) ≠ 0 by apply sub_ne_zero.mpr; exact_mod_cast (ne_of_lt (by simpa only [mem_Iio] using hx)).symm), neg_add_cancel,
          Complex.cpow_zero, one_mul]
      exact (show Tendsto (fun x : ℝ => H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) F (𝓝 1) by exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg).congr' heq.symm
    have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
      filter_upwards [(by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)), (by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x; exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num)))] with x hxlt hxpos
      change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
      right
      simp only [Complex.ofReal_re]
      exact ⟨hxpos, hxlt⟩
    exact tendsto_nhds_unique' (show NeBot F by dsimp [F]; exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩) (show Tendsto (fun x : ℝ => C₁ * ((1 - (x : ℂ)) ^ (-δ) * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) + C₂ * ((1 - (x : ℂ)) ^ (-δ) * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) F (𝓝 C₂) by simpa using (tendsto_const_nhds.mul (show Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) by simpa using (tendsto_one_sub_ofReal_cpow_zero (-δ) hδ).mul (by simpa [gaussGMinus, F, Function.comp_def] using (gaussFamily_tendsto_one_at_zero hH p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) hcMinus).comp harg))).add (tendsto_const_nhds.mul hscaledPlus)) (hF.congr' (by filter_upwards [hcut] with x hx; rw [hExpansion (x : ℂ) hx]; ring))
  exact secondCramer_eq_of_scaled_endpoint_expansion
    (δ := p.2.2 - p.1 - p.2.1) rfl (by rw [(show (-(p.2.2 - p.1 - p.2.1)).re = (p.1 + p.2.1 - p.2.2).re by simp [Complex.sub_re]; ring)]; exact hδ) (gaussFPlus H p.1 p.2.1 p.2.2)
    hF (gaussFPlus_eq_connectionMidpointCramer hH hp)

end DOZZ.Proofs
