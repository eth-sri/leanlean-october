/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerTransform
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Euler endpoint evaluations for the two `F₊` connection coefficients. -/

public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

private theorem gaussPlus_power_tendsto_one (c : ℝ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 1) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[Iio 1] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hcont  :=
    Complex.continuousAt_ofReal_cpow_const 1 ((1 - c : ℝ) : ℂ)
      (Or.inr (by norm_num : (1 : ℝ) ≠ 0))
  simpa [Function.comp_def] using hcont.tendsto.comp hid

variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℝ) (hA : 0 < a - c + 1) (hB : 0 < b - c + 1)

include H hH a b c hA hB in
/-- In the positive-excess Euler region, the first midpoint coefficient of `F₊` is its Gamma
value. The ordinary Euler integral applies to the shifted parameters in the definition of `F₊`. -/
theorem connectionPlusFirstCramer_eq_gamma_of_real
    
    (hδ : 0 < c - a - b)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusFirstCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₁ (a, b, c) := by
  let A  := a - c + 1
  let B  := b - c + 1
  let C  := 2 - c
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have hδ' : C - A - B = c - a - b := by dsimp [A, B, C]; ring
  have hCA : C - A = 1 - a := by dsimp [A, C]; ring
  have hCB : C - B = 1 - b := by dsimp [B, C]; ring
  have hCpos : 0 < C := by
    bound
  have hCApos : 0 < C - A := by bound
  have hCBpos : 0 < C - B := by bound
  have hp : p ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, (c : ℂ) ≠ (n : ℂ)) ∧
      ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ)
    constructor
    · intro n hn
      apply hcInt
      exact ⟨n, hn.symm⟩
    · intro n hn
      apply hδInt
      refine ⟨n, ?_⟩
      simp_all
  let K  := realGaussEulerKernelIntegral A B C
  let N  := Real.Gamma C / (Real.Gamma B * Real.Gamma (C - B))
  let L  := Real.Gamma C * Real.Gamma (C - A - B) /
    (Real.Gamma (C - A) * Real.Gamma (C - B))
  have hEuler := realGaussEulerKernelIntegral_tendsto_gauss_value A B C hA hB
    (by rw [hδ']; exact hδ)
  have hEulerC : Tendsto (fun x : ℝ => ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    have hEulerC0 := Complex.continuous_ofReal.continuousAt.tendsto.comp hEuler
    assumption_mod_cast
  have hpow := gaussPlus_power_tendsto_one c
  have hFvalue : Tendsto (fun x : ℝ =>
      (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    simpa using hpow.mul hEulerC
  have hEulerEq : (fun x : ℝ => gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[𝓝[Iio 1] 1]
      (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) := by
    have hxpos : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, 0 < x :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
    have hxlt : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, x < 1 := by
      exact eventually_mem_nhdsWithin
    filter_upwards [hxpos, hxlt] with x hx hx1
    have hEulerFamily := realGaussEulerIntegral_eq_family hH A B C x hA hB hCBpos hx hx1
    have hEulerFamily' : (N : ℂ) * (K x : ℂ) =
        H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) := by
      bound
    have hAc : (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) := by dsimp [A]; push_cast; ring
    have hBc : (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) := by dsimp [B]; push_cast; ring
    have hCc : (2 : ℂ) - (c : ℂ) = (C : ℂ) := by dsimp [C]; push_cast; ring
    rw [show gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
      (x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
        H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) by
          simp only [gaussFPlus]
          simp_all]
    simp_all
  have hF := hFvalue.congr' hEulerEq.symm
  have hδre : 0 < (((c : ℂ) - (a : ℂ) - (b : ℂ)).re) := by
    simp_all
  have hcoeff := connectionPlusFirstCramer_eq_of_endpoint_limit hH hp hδre hF
  have hGamma : (L : ℂ) = gaussConnectionPlusGammaCoefficient₁ p := by
    have hΓC  := (Real.Gamma_pos_of_pos hCpos).ne'
    have hΓδ : Real.Gamma (C - A - B) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by rw [hδ']; exact hδ)).ne'
    have hΓCA  := (Real.Gamma_pos_of_pos hCApos).ne'
    have hΓCB  := (Real.Gamma_pos_of_pos hCBpos).ne'
    dsimp [L, gaussConnectionPlusGammaCoefficient₁, p]
    rw [show (2 : ℂ) - (c : ℂ) = (C : ℂ) by dsimp [C]; push_cast; ring,
      show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) - (a : ℂ) = ((C - A : ℝ) : ℂ) by rw [hCA]; push_cast; ring,
      show (1 : ℂ) - (b : ℂ) = ((C - B : ℝ) : ℂ) by rw [hCB]; push_cast; ring,
      Complex.Gamma_ofReal C, Complex.Gamma_ofReal (c - a - b),
      Complex.Gamma_ofReal (C - A), Complex.Gamma_ofReal (C - B)]
    have hδgamma : Real.Gamma (c - a - b) = Real.Gamma (C - A - B) := by rw [hδ']
    rw [hδgamma]
    push_cast
    field_simp [hΓC, hΓδ, hΓCA, hΓCB]
  exact hcoeff.trans hGamma

include H hH a b c hA hB in
/-- In the negative-excess Euler region, the second midpoint coefficient of `F₊` is its Gamma
value. Euler's transformation moves the shifted integral to positive excess before taking the
endpoint limit. -/
theorem connectionPlusSecondCramer_eq_gamma_of_real
    
    (h1a : 0 < 1 - a) (h1b : 0 < 1 - b) (hδ : c - a - b < 0)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusSecondCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₂ (a, b, c) := by
  let A  := a - c + 1
  let B  := b - c + 1
  let C  := 2 - c
  let A'  := 1 - a
  let B'  := 1 - b
  let p : ℂ × ℂ × ℂ := (a, b, c)
  
  have hCA : C - A = A' := by dsimp [A, A', C]; ring
  have hCB : C - B = B' := by dsimp [B, B', C]; ring
  
  have htransB : C - B' = B := by dsimp [B, B', C]; ring
  have heta : 0 < a + b - c := by linarith
  have heta' : C - A' - B' = a + b - c := by dsimp [A', B', C]; ring
  have hp : p ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, (c : ℂ) ≠ (n : ℂ)) ∧
      ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ)
    constructor
    · intro n hn
      apply hcInt
      exact ⟨n, hn.symm⟩
    · intro n hn
      apply hδInt
      refine ⟨n, ?_⟩
      simp_all
  let K  := realGaussEulerKernelIntegral A' B' C
  let N  := Real.Gamma C / (Real.Gamma B' * Real.Gamma (C - B'))
  let L  := Real.Gamma C * Real.Gamma (C - A' - B') /
    (Real.Gamma (C - A') * Real.Gamma (C - B'))
  have hEuler := realGaussEulerKernelIntegral_tendsto_gauss_value A' B' C h1a h1b
    (by rw [heta']; exact heta)
  have hEulerC : Tendsto (fun x : ℝ => ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    have hEulerC0 := Complex.continuous_ofReal.continuousAt.tendsto.comp hEuler
    assumption_mod_cast
  have hpow := gaussPlus_power_tendsto_one c
  have hFvalue : Tendsto (fun x : ℝ =>
      (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    simpa using hpow.mul hEulerC
  have hxpos : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, 0 < x :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hxlt : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, x < 1 := by
    exact eventually_mem_nhdsWithin
  
  have hEulerEq : (fun x : ℝ =>
      (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
        gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[𝓝[Iio 1] 1]
      (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) := by
    filter_upwards [hxpos, hxlt] with x hx hx1
    have hCApos : 0 < C - A := by rw [hCA]; exact h1a
    have hCBpos : 0 < C - B := by rw [hCB]; exact h1b
    have hCBtranspos : 0 < C - B' := by rw [htransB]; exact hB
    have htransform := realGaussEulerTransform_family hH A B C x
      hA hB hCApos hCBpos hx hx1
    have hfamily := realGaussEulerIntegral_eq_family hH A' B' C x
      h1a h1b hCBtranspos hx hx1
    have hbase : (1 : ℂ) - (x : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (ne_of_lt hx1).symm
    have hdeltaCast : (C : ℂ) - (A : ℂ) - (B : ℂ) =
        (c : ℂ) - (a : ℂ) - (b : ℂ) := by
      have hreal : C - A - B = c - a - b := by
        dsimp [A, B, C]
        ring
      assumption_mod_cast
    have hcancel :
        (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
            H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ)) =
          H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by
      rw [← mul_assoc, ← Complex.cpow_add _ _ hbase,
        neg_add_cancel, Complex.cpow_zero, one_mul]
    have hfamily' : (N : ℂ) * (K x : ℂ) =
        H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by
      bound
    have hAc : (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) := by dsimp [A]; push_cast; ring
    have hBc : (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) := by dsimp [B]; push_cast; ring
    have hCc : (2 : ℂ) - (c : ℂ) = (C : ℂ) := by dsimp [C]; push_cast; ring
    calc
      _ = (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
            ((1 - (x : ℂ)) ^ ((C : ℂ) - (A : ℂ) - (B : ℂ)) *
              H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ))) := by
        rw [show gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
          (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) by
            simp only [gaussFPlus]
            simp_all,
          htransform, hdeltaCast, hCA, hCB]
      _ = (x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
          H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by
        grind
      _ = (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ) := by
        rw [← hfamily', ← Complex.ofReal_mul]
  have hscaled := hFvalue.congr' hEulerEq.symm
  have hδendpoint : 0 < (p.1 + p.2.1 - p.2.2).re := by
    positivity
  have hcoeff := connectionPlusSecondCramer_eq_of_scaled_endpoint_limit
    hH hp hδendpoint (by exact hscaled)
  have hGamma : (L : ℂ) = gaussConnectionPlusGammaCoefficient₂ p := by
    have hΓη  := (Real.Gamma_pos_of_pos heta).ne'
    have hΓA  := (Real.Gamma_pos_of_pos hA).ne'
    have hΓB  := (Real.Gamma_pos_of_pos hB).ne'
    dsimp [L, gaussConnectionPlusGammaCoefficient₂, p]
    rw [show (2 : ℂ) - (c : ℂ) = (C : ℂ) by dsimp [C]; push_cast; ring,
      show (a : ℂ) + (b : ℂ) - (c : ℂ) = ((a + b - c : ℝ) : ℂ) by push_cast; ring,
      show (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) by dsimp [A]; push_cast; ring,
      show (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) by dsimp [B]; push_cast; ring,
      Complex.Gamma_ofReal C, Complex.Gamma_ofReal (a + b - c),
      Complex.Gamma_ofReal A, Complex.Gamma_ofReal B]
    rw [show C - A' - B' = a + b - c by dsimp [A', B', C]; ring,
      show C - A' = A by dsimp [A', A, C]; ring,
      show C - B' = B by dsimp [B', B, C]; ring]
    push_cast
    field_simp [hΓη, hΓA, hΓB]
  exact hcoeff.trans hGamma

end DOZZ.Proofs
