/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerTransform
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Euler endpoint evaluations for the two `F₊` connection coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

private theorem gaussPlus_power_tendsto_one (c : ℝ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 1) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[Iio 1] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hcont :=
    Complex.continuousAt_ofReal_cpow_const 1 ((1 - c))
      (Or.inr (by norm_num))
  simpa [Function.comp_def] using hcont.tendsto.comp hid
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H) (a b c : ℝ) (hA : 0 < a - c + 1) (hB : 0 < b - c + 1)
include hH hA hB

/-- In the positive-excess Euler region, the first midpoint coefficient of `F₊` is its Gamma
value. The ordinary Euler integral applies to the shifted parameters in the definition of `F₊`. -/
theorem connectionPlusFirstCramer_eq_gamma_of_real
    (hδ : 0 < c - a - b)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusFirstCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₁ (a, b, c) := by
  let A : ℝ := a - c + 1
  let B : ℝ := b - c + 1
  let C : ℝ := 2 - c
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have hδ' : C - A - B = c - a - b := by linarith
  have hCA : C - A = 1 - a := by linarith
  have hCB : C - B = 1 - b := by linarith
  have hCpos : 0 < C := by
    linarith
  have hCApos : 0 < C - A := by linarith
  have hCBpos : 0 < C - B := by linarith
  have hp : p ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, (c : ℂ) ≠ (n : ℂ)) ∧
      ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ)
    constructor
    · tauto
    · intro n hn
      apply hδInt
      refine ⟨n, ?_⟩
      simp_all
  let K : ℝ → ℝ := realGaussEulerKernelIntegral A B C
  let N : ℝ := Real.Gamma C / (Real.Gamma B * Real.Gamma (C - B))
  let L : ℝ := Real.Gamma C * Real.Gamma (C - A - B) /
    (Real.Gamma (C - A) * Real.Gamma (C - B))
  have hEuler := realGaussEulerKernelIntegral_tendsto_gauss_value A B C hA hB
    (by linarith)
  have hEulerC : Tendsto (fun x : ℝ => ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    simpa only [Function.comp_def, N, K, L] using (Complex.continuous_ofReal.continuousAt.tendsto.comp hEuler)
  have hFvalue : Tendsto (fun x : ℝ =>
      (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    simpa using (gaussPlus_power_tendsto_one c).mul hEulerC
  have hEulerEq : (fun x : ℝ => gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[𝓝[Iio 1] 1]
      (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) := by
    have hxpos : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, 0 < x :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
    have hxlt : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, x < 1 := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1
      simpa only [mem_Iio] using
        (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
    filter_upwards [hxpos, hxlt] with x hx hx1
    have hEulerFamily' : (N : ℂ) * (K x : ℂ) =
        H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) := by
      simpa [N, K, realGaussEulerKernelIntegral] using (realGaussEulerIntegral_eq_family hH A B C x hA hB hCBpos hx hx1)
    have hAc : (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) := by norm_cast
    have hBc : (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) := by norm_cast
    have hCc : (2 : ℂ) - (c : ℂ) = (C : ℂ) := by norm_cast
    rw [show gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
      (x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
        H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) by
          simp only [gaussFPlus]
          rw [show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by simp,
            hAc, hBc, hCc]]
    rw [← hEulerFamily']
    rw [← Complex.ofReal_mul]
  have hδre : 0 < (((c : ℂ) - (a : ℂ) - (b : ℂ)).re) := by
    rw [show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by simp]
    simp only [Complex.ofReal_re]
    exact hδ
  have hGamma : (L : ℂ) = gaussConnectionPlusGammaCoefficient₁ p := by
    have hΓC : Real.Gamma C ≠ 0 := (Real.Gamma_pos_of_pos hCpos).ne'
    have hΓδ : Real.Gamma (C - A - B) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith)).ne'
    have hΓCA : Real.Gamma (C - A) ≠ 0 := (Real.Gamma_pos_of_pos hCApos).ne'
    have hΓCB : Real.Gamma (C - B) ≠ 0 := (Real.Gamma_pos_of_pos hCBpos).ne'
    dsimp [L, gaussConnectionPlusGammaCoefficient₁, p]
    rw [show (2 : ℂ) - (c : ℂ) = (C : ℂ) by norm_cast,
      show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by simp,
      show (1 : ℂ) - (a : ℂ) = ((C - A : ℝ) : ℂ) by simp_all,
      show (1 : ℂ) - (b : ℂ) = ((C - B : ℝ) : ℂ) by simp_all,
      Complex.Gamma_ofReal C, Complex.Gamma_ofReal _,
      Complex.Gamma_ofReal _, Complex.Gamma_ofReal _]
    have hδgamma : Real.Gamma (c - a - b) = Real.Gamma (C - A - B) := by simp_all
    rw [hδgamma]
    push_cast
    field_simp [hΓC, hΓδ, hΓCA, hΓCB]
  simpa [p] using (connectionPlusFirstCramer_eq_of_endpoint_limit hH hp hδre (hFvalue.congr' hEulerEq.symm)).trans hGamma

/-- In the negative-excess Euler region, the second midpoint coefficient of `F₊` is its Gamma
value. Euler's transformation moves the shifted integral to positive excess before taking the
endpoint limit. -/
theorem connectionPlusSecondCramer_eq_gamma_of_real
    (h1a : 0 < 1 - a) (h1b : 0 < 1 - b) (hδ : c - a - b < 0)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusSecondCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₂ (a, b, c) := by
  let A : ℝ := a - c + 1
  let B : ℝ := b - c + 1
  let C : ℝ := 2 - c
  let A' : ℝ := 1 - a
  let B' : ℝ := 1 - b
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have hδ' : C - A - B = c - a - b := by linarith
  have hCA : C - A = A' := by linarith
  have hCB : C - B = B' := by linarith
  have htransA : C - A' = A := by linarith
  have htransB : C - B' = B := by linarith
  have heta : 0 < a + b - c := by linarith
  have heta' : C - A' - B' = a + b - c := by linarith
  have hp : p ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, (c : ℂ) ≠ (n : ℂ)) ∧
      ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ)
    constructor
    · tauto
    · intro n hn
      apply hδInt
      refine ⟨n, ?_⟩
      simp_all
  let K : ℝ → ℝ := realGaussEulerKernelIntegral A' B' C
  let N : ℝ := Real.Gamma C / (Real.Gamma B' * Real.Gamma (C - B'))
  let L : ℝ := Real.Gamma C * Real.Gamma (C - A' - B') /
    (Real.Gamma (C - A') * Real.Gamma (C - B'))
  have hEuler := realGaussEulerKernelIntegral_tendsto_gauss_value A' B' C h1a h1b
    (by linarith)
  have hEulerC : Tendsto (fun x : ℝ => ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    simpa only [Function.comp_def, N, K, L] using (Complex.continuous_ofReal.continuousAt.tendsto.comp hEuler)
  have hFvalue : Tendsto (fun x : ℝ =>
      (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ))
      (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) := by
    simpa using (gaussPlus_power_tendsto_one c).mul hEulerC
  have hxpos : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, 0 < x :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hxlt : ∀ᶠ x : ℝ in 𝓝[Iio 1] 1, x < 1 := by
    change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1
    simpa only [mem_Iio] using
      (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
  have hδcast : ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := by
    push_cast
    ring
  have hEulerEq : (fun x : ℝ =>
      (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
        gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[𝓝[Iio 1] 1]
      (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) := by
    filter_upwards [hxpos, hxlt] with x hx hx1
    have hCApos : 0 < C - A := by linarith
    have hCBpos : 0 < C - B := by linarith
    have hCBtranspos : 0 < C - B' := by linarith
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
      calc
        (C : ℂ) - (A : ℂ) - (B : ℂ) = ((C - A - B : ℝ) : ℂ) := by
          push_cast
          ring
        _ = ((c - a - b : ℝ) : ℂ) := congrArg Complex.ofReal hreal
        _ = (c : ℂ) - (a : ℂ) - (b : ℂ) := by assumption
    have hcancel :
        (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
            H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ)) =
          H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by
      rw [← mul_assoc, ← Complex.cpow_add _ _ hbase,
        neg_add_cancel, Complex.cpow_zero, one_mul]
    have hfamily' : (N : ℂ) * (K x : ℂ) =
        H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by
      simpa [N, K, realGaussEulerKernelIntegral] using hfamily
    have hAc : (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) := by norm_cast
    have hBc : (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) := by norm_cast
    have hCc : (2 : ℂ) - (c : ℂ) = (C : ℂ) := by grind
    calc
      _ = (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
            ((1 - (x : ℂ)) ^ ((C : ℂ) - (A : ℂ) - (B : ℂ)) *
              H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ))) := by
        rw [show gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
          (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) by
            simp only [gaussFPlus]
            rw [show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by simp,
              hAc, hBc, hCc],
          htransform, hdeltaCast, hCA, hCB]
      _ = (x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
          H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by
        calc
          _ = (x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
              ((1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
                ((1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
                  H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ))) := by
            rw [hdeltaCast]
            ac_rfl
          _ = (x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
              H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by simp_all
      _ = (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ) := by
        rw [← hfamily', ← Complex.ofReal_mul]
  have hδendpoint : 0 < (p.1 + p.2.1 - p.2.2).re := by
    rw [show p.1 + p.2.1 - p.2.2 = ((a + b - c : ℝ) : ℂ) by
      change (a : ℂ) + (b : ℂ) - (c : ℂ) = _
      push_cast
      ring]
    simp only [Complex.ofReal_re]
    exact heta
  have hcoeff := connectionPlusSecondCramer_eq_of_scaled_endpoint_limit
    hH hp hδendpoint (by simpa [p] using (hFvalue.congr' hEulerEq.symm))
  have hGamma : (L : ℂ) = gaussConnectionPlusGammaCoefficient₂ p := by
    have hΓη : Real.Gamma (a + b - c) ≠ 0 := (Real.Gamma_pos_of_pos heta).ne'
    have hΓA : Real.Gamma A ≠ 0 := (Real.Gamma_pos_of_pos hA).ne'
    have hΓB : Real.Gamma B ≠ 0 := (Real.Gamma_pos_of_pos hB).ne'
    dsimp [L, gaussConnectionPlusGammaCoefficient₂, p]
    rw [show (2 : ℂ) - (c : ℂ) = (C : ℂ) by norm_cast,
      show (a : ℂ) + (b : ℂ) - (c : ℂ) = ((a + b - c : ℝ) : ℂ) by simp,
      show (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) by norm_cast,
      show (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) by norm_cast,
      Complex.Gamma_ofReal C, Complex.Gamma_ofReal _,
      Complex.Gamma_ofReal A, Complex.Gamma_ofReal B]
    rw [show C - A' - B' = a + b - c by assumption,
      show C - A' = A by assumption,
      show C - B' = B by assumption]
    push_cast
    field_simp [hΓη, hΓA, hΓB]
  simpa [p] using hcoeff.trans hGamma

end

end

end DOZZ.Proofs
