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
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    Tendsto (H a b c) (𝓝 0) (𝓝 1) := by
  have hchar := hH a b c hc
  have hzero : H a b c 0 = 1 := by
    simpa using hchar.2 0 (by norm_num)
  have hmem : (0 : ℂ) ∈ gaussSlitPlane := by simp [gaussSlitPlane]
  have hAt  :=
    (hchar.1 0 hmem).differentiableAt
      (gaussSlitPlane_isOpen.mem_nhds hmem)
  simpa [hzero] using hAt.continuousAt.tendsto

local notation "F₁" => 𝓝[Iio (1 : ℝ)] 1

private theorem tendsto_one_sub_left : Tendsto (fun x : ℝ => 1 - x) F₁ (𝓝 0) := by
  simpa using (show ContinuousAt (fun x : ℝ => 1 - x) 1 from by fun_prop).tendsto.mono_left
    (show F₁ ≤ 𝓝 1 from nhdsWithin_le_nhds)

private theorem tendsto_one_sub_ofReal_cpow_zero (δ : ℂ) (hδ : 0 < δ.re) :
    Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ δ) F₁ (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (Real.continuousAt_rpow (0, δ.re) (Or.inr hδ)).tendsto.comp
    (tendsto_one_sub_left.prodMk_nhds tendsto_const_nhds)
  refine (by simpa [Function.comp_def, Real.zero_rpow hδ.ne'] using h :
    Tendsto (fun x : ℝ => (1 - x) ^ δ.re) F₁ (𝓝 0)).congr' ?_
  filter_upwards [self_mem_nhdsWithin (s := Iio (1 : ℝ)) (a := 1)] with x hx
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx)]

private theorem eventually_ofReal_mem_gaussCutPlane : ∀ᶠ x : ℝ in F₁, (x : ℂ) ∈ gaussCutPlane := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with x hx hpos
  exact Or.inr ⟨by simpa using hpos, by simpa using (show x < 1 from hx)⟩

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
  {a b c : ℂ} (hp : (a, b, c) ∈ gaussConnectionParameterDomain)

local notation "Δ" => c - a - b
local notation "G₁" => (fun x : ℝ => gaussGMinus H a b c (x : ℂ))
local notation "G₂" => (fun x : ℝ => gaussGPlus H a b c (x : ℂ))
local notation "G₂₀" => (fun x : ℝ =>
  H (c - b) (c - a) (1 + c - a - b) (1 - (x : ℂ)))

include hH hp in
private theorem tendsto_gaussG_unpowered : Tendsto G₁ F₁ (𝓝 1) ∧ Tendsto G₂₀ F₁ (𝓝 1) := by
  have harg : Tendsto (fun x : ℝ => 1 - (x : ℂ)) F₁ (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_one_sub_left
  have hm (n : ℕ) (hn : 1 + a + b - c = -(n : ℂ)) : False := by
    apply hp.2 (n + 1)
    push_cast
    linear_combination -hn
  have hplus (n : ℕ) (hn : 1 + c - a - b = -(n : ℂ)) : False := by
    apply hp.2 (-(n + 1 : ℤ))
    push_cast
    linear_combination hn
  exact ⟨(gaussFamily_tendsto_one_at_zero hH _ _ _ hm).comp harg,
    (gaussFamily_tendsto_one_at_zero hH _ _ _ hplus).comp harg⟩

/-- Extract a coefficient using whichever endpoint normalization makes its basis vector tend to one. -/
private theorem coefficient_eq_of_normalized_endpoint {f : ℂ → ℂ} {C₁ C₂ L L₁ L₂ : ℂ}
    {w : ℝ → ℂ}
    (hExpansion : ∀ z ∈ gaussCutPlane,
      f z = C₁ * gaussGMinus H a b c z + C₂ * gaussGPlus H a b c z)
    (hf : Tendsto (fun x : ℝ => w x * f (x : ℂ)) F₁ (𝓝 L))
    (h₁ : Tendsto (fun x => w x * G₁ x) F₁ (𝓝 L₁))
    (h₂ : Tendsto (fun x => w x * G₂ x) F₁ (𝓝 L₂)) : C₁ * L₁ + C₂ * L₂ = L := by
  have hF : NeBot F₁ :=
    (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩
  refine tendsto_nhds_unique ((tendsto_const_nhds.mul h₁).add (tendsto_const_nhds.mul h₂))
    (hf.congr' ?_)
  filter_upwards [eventually_ofReal_mem_gaussCutPlane] with x hx
  rw [hExpansion _ hx]
  ring

include hH hp

section
variable {f : ℂ → ℂ} {C₁ C₂ L : ℂ}

private theorem firstCramer_eq_of_endpoint_expansion
    (hδ : 0 < (Δ).re)
    (hf : Tendsto (fun x : ℝ => f (x : ℂ)) F₁ (𝓝 L))
    (hExpansion : ∀ z ∈ gaussCutPlane,
      f z = C₁ * gaussGMinus H a b c z + C₂ * gaussGPlus H a b c z) :
    C₁ = L := by
  obtain ⟨h₁, h₂⟩ := tendsto_gaussG_unpowered hH hp
  have h₂' : Tendsto G₂ F₁ (𝓝 0) := by
    simpa only [gaussGPlus, zero_mul] using (tendsto_one_sub_ofReal_cpow_zero Δ hδ).mul h₂
  have h := coefficient_eq_of_normalized_endpoint (L₁ := 1) (L₂ := 0)
    (w := fun _ => 1) hExpansion (by simpa using hf) (by simpa using h₁) (by simpa using h₂')
  simpa only [mul_one, mul_zero, add_zero] using h

private theorem secondCramer_eq_of_scaled_endpoint_expansion
    (hδ : 0 < (a + b - c).re)
    (hf : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-Δ) * f (x : ℂ)) F₁ (𝓝 L))
    (hExpansion : ∀ z ∈ gaussCutPlane,
      f z = C₁ * gaussGMinus H a b c z + C₂ * gaussGPlus H a b c z) :
    C₂ = L := by
  obtain ⟨h₁, h₂⟩ := tendsto_gaussG_unpowered hH hp
  have hn : -Δ = a + b - c := by ring
  have hpw := tendsto_one_sub_ofReal_cpow_zero (-Δ) (hn ▸ hδ)
  have h₂' : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-Δ) * G₂ x) F₁ (𝓝 1) := by
    refine h₂.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hbase : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt hx).symm)
    simp only [gaussGPlus, ← mul_assoc, ← Complex.cpow_add _ _ hbase,
      neg_add_cancel, Complex.cpow_zero, one_mul]
  have h := coefficient_eq_of_normalized_endpoint (L₁ := 0) hExpansion hf
    (by simpa only [zero_mul] using hpw.mul h₁) h₂'
  simpa only [mul_zero, mul_one, zero_add] using h

end

end

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ}
  (hp : p ∈ gaussConnectionParameterDomain) {L : ℂ}
include hH hp

/-- If the zero-basis solution has a finite real-axis endpoint limit and `Re(c-a-b)>0`,
the first midpoint Cramer coefficient is exactly that limit. The basis limits are `G₋→1` and
`G₊→0`; the separate Euler integral supplies the endpoint value in applications. -/
theorem connectionMinusFirstCramer_eq_of_endpoint_limit (hδ : 0 < (p.2.2 - p.1 - p.2.1).re)
    (hF : Tendsto (fun x : ℝ => gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ))
      F₁ (𝓝 L)) :
    connectionMinusFirstCramerCoefficient H p = L :=
  firstCramer_eq_of_endpoint_expansion hH hp hδ hF
    (gaussFMinus_eq_connectionMidpointCramer hH hp)

/-- If the singularly rescaled zero-basis solution has a finite real-axis endpoint limit and
`Re(c-a-b)<0`, the second midpoint Cramer coefficient is that limit. The first one-basis term
vanishes after rescaling, while the powered second one-basis term tends to `1`. -/
theorem connectionMinusSecondCramer_eq_of_scaled_endpoint_limit (hδ : 0 < (p.1 + p.2.1 - p.2.2).re)
    (hF : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-(p.2.2 - p.1 - p.2.1)) *
        gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ))
      F₁ (𝓝 L)) :
    connectionMinusSecondCramerCoefficient H p = L :=
  secondCramer_eq_of_scaled_endpoint_expansion hH hp hδ hF
    (gaussFMinus_eq_connectionMidpointCramer hH hp)

/-- The same endpoint extraction applies to the second zero-basis solution `F₊`; its midpoint
Cramer coefficients are thus identified by the corresponding (possibly rescaled) Euler limits. -/
theorem connectionPlusFirstCramer_eq_of_endpoint_limit (hδ : 0 < (p.2.2 - p.1 - p.2.1).re)
    (hF : Tendsto (fun x : ℝ => gaussFPlus H p.1 p.2.1 p.2.2 (x : ℂ))
      F₁ (𝓝 L)) :
    connectionPlusFirstCramerCoefficient H p = L :=
  firstCramer_eq_of_endpoint_expansion hH hp hδ hF
    (gaussFPlus_eq_connectionMidpointCramer hH hp)

/-- The rescaled endpoint extraction also identifies the second Cramer coefficient of `F₊`. -/
theorem connectionPlusSecondCramer_eq_of_scaled_endpoint_limit (hδ : 0 < (p.1 + p.2.1 - p.2.2).re)
    (hF : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-(p.2.2 - p.1 - p.2.1)) *
        gaussFPlus H p.1 p.2.1 p.2.2 (x : ℂ))
      F₁ (𝓝 L)) :
    connectionPlusSecondCramerCoefficient H p = L :=
  secondCramer_eq_of_scaled_endpoint_expansion hH hp hδ hF
    (gaussFPlus_eq_connectionMidpointCramer hH hp)

end

end DOZZ.Proofs
