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
  simpa [Function.comp_def] using (Complex.continuousAt_ofReal_cpow_const 1 ((1 - c : ℝ) : ℂ) (Or.inr (by norm_num : (1 : ℝ) ≠ 0))).tendsto.comp (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- In the positive-excess Euler region, the first midpoint coefficient of `F₊` is its Gamma
value. The ordinary Euler integral applies to the shifted parameters in the definition of `F₊`. -/
theorem connectionPlusFirstCramer_eq_gamma_of_real
    {H} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hA : 0 < a - c + 1) (hB : 0 < b - c + 1)
    (hδ : 0 < c - a - b)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusFirstCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₁ (a, b, c) := by
  let A : ℝ := a - c + 1
  let B : ℝ := b - c + 1
  let C : ℝ := 2 - c
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have hδ' : C - A - B = c - a - b := by dsimp [A, B, C]; ring
  have hCA : C - A = 1 - a := by dsimp [A, C]; ring
  have hCB : C - B = 1 - b := by dsimp [B, C]; ring
  have hCBpos : 0 < C - B := by rw [hCB, show 1 - b = (c - a - b) + A by dsimp [A]; ring]; linarith
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
      calc
        (n : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := hn.symm
        _ = ((c - a - b : ℝ) : ℂ) := by push_cast; ring
  let K := realGaussEulerKernelIntegral A B C
  let N := Real.Gamma C / (Real.Gamma B * Real.Gamma (C - B))
  let L := Real.Gamma C * Real.Gamma (C - A - B) /
    (Real.Gamma (C - A) * Real.Gamma (C - B))
  have hEulerEq : (fun x : ℝ => gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[𝓝[Iio 1] 1]
      (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) := by
    filter_upwards [(Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))), (by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1))] with x hx hx1
    rw [show gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
      (x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
        H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) by
          simp only [gaussFPlus]
          rw [show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring,
            (show (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) by dsimp [A]; push_cast; ring), (show (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) by dsimp [B]; push_cast; ring), (show (2 : ℂ) - (c : ℂ) = (C : ℂ) by dsimp [C]; push_cast; ring)]]
    rw [← (show (N : ℂ) * (K x : ℂ) = H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) by simpa [N, K, realGaussEulerKernelIntegral] using (realGaussEulerIntegral_eq_family hH A B C x hA hB hCBpos hx hx1)), ← Complex.ofReal_mul]
  have hGamma : (L : ℂ) = gaussConnectionPlusGammaCoefficient₁ p := by
    have hΓC := (Real.Gamma_pos_of_pos (show 0 < C by linarith)).ne'
    have hΓCA := (Real.Gamma_pos_of_pos (show 0 < C - A by rw [hCA, show 1 - a = (c - a - b) + B by dsimp [B]; ring]; linarith)).ne'
    dsimp [L, gaussConnectionPlusGammaCoefficient₁, p]
    rw [show (2 : ℂ) - (c : ℂ) = (C : ℂ) by dsimp [C]; push_cast; ring,
      show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) - (a : ℂ) = ((C - A : ℝ) : ℂ) by rw [hCA]; push_cast; ring,
      show (1 : ℂ) - (b : ℂ) = ((C - B : ℝ) : ℂ) by rw [hCB]; push_cast; ring,
      Complex.Gamma_ofReal C, Complex.Gamma_ofReal (c - a - b),
      Complex.Gamma_ofReal (C - A), Complex.Gamma_ofReal (C - B)]
    rw [(show Real.Gamma (c - a - b) = Real.Gamma (C - A - B) by rw [hδ'])]
    push_cast
    field_simp [hΓC, ((Real.Gamma_pos_of_pos (by rw [hδ']; exact hδ)).ne' : Real.Gamma (C - A - B) ≠ 0), hΓCA, ((Real.Gamma_pos_of_pos hCBpos).ne')]
  simpa [p] using (connectionPlusFirstCramer_eq_of_endpoint_limit hH hp (by rw [show (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) by push_cast; ring]; simp only [Complex.ofReal_re]; exact hδ) ((show Tendsto (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) by simpa using (gaussPlus_power_tendsto_one c).mul (show Tendsto (fun x : ℝ => ((N * K x : ℝ) : ℂ)) (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) by simpa only [Function.comp_def, N, K, L] using (Complex.continuous_ofReal.continuousAt.tendsto.comp (realGaussEulerKernelIntegral_tendsto_gauss_value A B C hA hB (by rw [hδ']; exact hδ))))).congr' hEulerEq.symm)).trans hGamma

/-- In the negative-excess Euler region, the second midpoint coefficient of `F₊` is its Gamma
value. Euler's transformation moves the shifted integral to positive excess before taking the
endpoint limit. -/
theorem connectionPlusSecondCramer_eq_gamma_of_real
    {H} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hA : 0 < a - c + 1) (hB : 0 < b - c + 1)
    (h1a : 0 < 1 - a) (h1b : 0 < 1 - b) (hδ : c - a - b < 0)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionPlusSecondCramerCoefficient H (a, b, c) =
      gaussConnectionPlusGammaCoefficient₂ (a, b, c) := by
  let A := a - c + 1
  let B := b - c + 1
  let C : ℝ := 2 - c
  let A' : ℝ := 1 - a
  let B' : ℝ := 1 - b
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have hCA : C - A = A' := by dsimp [A, A', C]; ring
  have hCB : C - B = B' := by dsimp [B, B', C]; ring
  have heta : 0 < a + b - c := by linarith
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
      calc
        (n : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := hn.symm
        _ = ((c - a - b : ℝ) : ℂ) := by push_cast; ring
  let K := realGaussEulerKernelIntegral A' B' C
  let N := Real.Gamma C / (Real.Gamma B' * Real.Gamma (C - B'))
  let L := Real.Gamma C * Real.Gamma (C - A' - B') /
    (Real.Gamma (C - A') * Real.Gamma (C - B'))
  have hEulerEq : (fun x : ℝ =>
      (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
        gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[𝓝[Iio 1] 1]
      (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) := by
    filter_upwards [(Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))), (by change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1; simpa only [mem_Iio] using (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1))] with x hx hx1
    have hdeltaCast : (C : ℂ) - (A : ℂ) - (B : ℂ) =
        (c : ℂ) - (a : ℂ) - (b : ℂ) := by
      calc
        (C : ℂ) - (A : ℂ) - (B : ℂ) = ((C - A - B : ℝ) : ℂ) := by
          push_cast
          ring
        _ = ((c - a - b : ℝ) : ℂ) := congrArg Complex.ofReal (by dsimp [A, B, C]; ring)
        _ = (c : ℂ) - (a : ℂ) - (b : ℂ) := by push_cast; ring
    calc
      _ = (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((x : ℂ) ^ ((1 - c : ℝ) : ℂ) *
            ((1 - (x : ℂ)) ^ ((C : ℂ) - (A : ℂ) - (B : ℂ)) *
              H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ))) := by
        rw [show gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
          (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * H (A : ℂ) (B : ℂ) (C : ℂ) (x : ℂ) by
            simp only [gaussFPlus]
            rw [show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring,
              (show (a : ℂ) - (c : ℂ) + 1 = (A : ℂ) by dsimp [A]; push_cast; ring), (show (b : ℂ) - (c : ℂ) + 1 = (B : ℂ) by dsimp [B]; push_cast; ring), (show (2 : ℂ) - (c : ℂ) = (C : ℂ) by dsimp [C]; push_cast; ring)],
          (realGaussEulerTransform_family hH A B C x hA hB (by rw [hCA]; exact h1a) (show 0 < C - B by rw [hCB]; exact h1b) hx hx1), hdeltaCast, hCA, hCB]
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
              H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) := by rw [(show (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) * ((1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) * H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ)) = H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) by rw [← mul_assoc, ← Complex.cpow_add _ _ (show (1 : ℂ) - (x : ℂ) ≠ 0 by apply sub_ne_zero.mpr; exact_mod_cast (ne_of_lt hx1).symm), neg_add_cancel, Complex.cpow_zero, one_mul])]
      _ = (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ) := by
        rw [← (show (N : ℂ) * (K x : ℂ) = H (A' : ℂ) (B' : ℂ) (C : ℂ) (x : ℂ) by simpa [N, K, realGaussEulerKernelIntegral] using (realGaussEulerIntegral_eq_family hH A' B' C x h1a h1b (show 0 < C - B' by rw [(show C - B' = B by dsimp [B, B', C]; ring)]; exact hB) hx hx1)), ← Complex.ofReal_mul]
  have hδendpoint : 0 < (p.1 + p.2.1 - p.2.2).re := by
    rw [show p.1 + p.2.1 - p.2.2 = ((a + b - c : ℝ) : ℂ) by
      change (a : ℂ) + (b : ℂ) - (c : ℂ) = _
      push_cast
      ring]
    simp only [Complex.ofReal_re]
    exact heta
  have hGamma : (L : ℂ) = gaussConnectionPlusGammaCoefficient₂ p := by
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
    field_simp [((Real.Gamma_pos_of_pos heta).ne'), ((Real.Gamma_pos_of_pos hA).ne'), ((Real.Gamma_pos_of_pos hB).ne')]
  simpa [p] using (connectionPlusSecondCramer_eq_of_scaled_endpoint_limit hH hp hδendpoint (by simpa [p] using ((show Tendsto (fun x : ℝ => (x : ℂ) ^ ((1 - c : ℝ) : ℂ) * ((N * K x : ℝ) : ℂ)) (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) by simpa using (gaussPlus_power_tendsto_one c).mul (show Tendsto (fun x : ℝ => ((N * K x : ℝ) : ℂ)) (𝓝[Iio 1] 1) (𝓝 (L : ℂ)) by simpa only [Function.comp_def, N, K, L] using (Complex.continuous_ofReal.continuousAt.tendsto.comp (realGaussEulerKernelIntegral_tendsto_gauss_value A' B' C h1a h1b (by rw [(show C - A' - B' = a + b - c by dsimp [A', B', C]; ring)]; exact heta))))).congr' hEulerEq.symm))).trans hGamma

end DOZZ.Proofs
