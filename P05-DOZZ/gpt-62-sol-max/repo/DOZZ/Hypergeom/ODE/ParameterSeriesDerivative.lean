/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesBounds
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-! Fréchet derivatives of the successive-term multiplier in the Gauss parameter series. -/

@[expose] public section

namespace DOZZ.Proofs

open Nat Polynomial

noncomputable abbrev gaussParamProjectionA : (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
  ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)

noncomputable abbrev gaussParamProjectionB : (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))

noncomputable abbrev gaussParamProjectionC : (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))

/-- Explicit Fréchet derivative of the successive-term multiplier. -/
noncomputable def gaussParameterSeriesRatioDeriv
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) :
    (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
  let A := (n : ℂ) + p.1
  let B := (n : ℂ) + p.2.1
  let C := (n : ℂ) + p.2.2



  let d := z / (n + 1 : ℂ)
  d • ((A * B) • (-(C⁻¹ ^ 2) • gaussParamProjectionC) +
    C⁻¹ • (A • gaussParamProjectionB + B • gaussParamProjectionA))

section
variable (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ)

theorem gaussParameterSeriesRatio_hasFDerivAt
    (hc : (n : ℂ) + p.2.2 ≠ 0) :
    HasFDerivAt (fun q : ℂ × ℂ × ℂ => gaussParameterSeriesRatio q z n)
      (gaussParameterSeriesRatioDeriv p z n) p := by
  let A : ℂ × ℂ × ℂ → ℂ := fun q => (n : ℂ) + q.1
  let B : ℂ × ℂ × ℂ → ℂ := fun q => (n : ℂ) + q.2.1
  let C : ℂ × ℂ × ℂ → ℂ := fun q => (n : ℂ) + q.2.2



  let d : ℂ := z / (n + 1 : ℂ)
  have hA : HasFDerivAt A gaussParamProjectionA p := by
    simpa [A, gaussParamProjectionA] using (hasFDerivAt_fst (𝕜 := ℂ) (p := p)).const_add (n : ℂ)
  have hB : HasFDerivAt B gaussParamProjectionB p := by
    simpa [B, gaussParamProjectionB] using
      (hasFDerivAt_fst (𝕜 := ℂ) (p := p.2)).comp p hasFDerivAt_snd |>.const_add (n : ℂ)
  have hC : HasFDerivAt C gaussParamProjectionC p := by
    simpa [C, gaussParamProjectionC] using
      (hasFDerivAt_snd (𝕜 := ℂ) (p := p.2)).comp p hasFDerivAt_snd |>.const_add (n : ℂ)
  have hCne : C p ≠ 0 := by simpa [C] using hc
  have hCi : HasFDerivAt (fun q => (C q)⁻¹)
      (-(C p)⁻¹ ^ 2 • gaussParamProjectionC) p := by
    convert (hasFDerivAt_inv' hCne).comp p hC using 1
    · ext q
      rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.mulLeftRight_apply, smul_apply]
      ring
  have hAB := hA.mul hB
  have hABi := hAB.mul hCi
  have hscale := (hasFDerivAt_const d p).mul hABi
  have hfun : (fun q => gaussParameterSeriesRatio q z n) =
      fun q => d * (A q * B q * (C q)⁻¹) := by
    funext q
    dsimp [gaussParameterSeriesRatio, A, B, C, d]
    field_simp
  rw [hfun]
  convert hscale using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [gaussParameterSeriesRatioDeriv, A, B, C, d, gaussParamProjectionA, gaussParamProjectionB, gaussParamProjectionC,
    ContinuousLinearMap.comp_apply, smul_apply, mul_assoc, mul_left_comm, mul_comm]

/-- On a sufficiently far tail, the derivative of the Gauss term multiplier is uniformly bounded
on bounded pole-free parameter sets. -/
theorem gaussParameterSeriesRatioDeriv_norm_le (R : ℝ)
    (hR : 0 ≤ R) (hRn : R < (n : ℝ)) (h3R : 3 * R ≤ (n : ℝ))
    (hA : ‖p.1‖ ≤ R) (hB : ‖p.2.1‖ ≤ R) (hC : ‖p.2.2‖ ≤ R) :
    ‖gaussParameterSeriesRatioDeriv p z n‖ ≤ 8 * ‖z‖ := by
  let A := (n : ℂ) + p.1
  let B := (n : ℂ) + p.2.1
  let C := (n : ℂ) + p.2.2



  let x : ℝ := (n : ℝ)
  have hxR : R < x := by simpa [x] using hRn
  have hx0 : 0 < x := lt_of_le_of_lt hR hxR
  have hxmR : 0 < x - R := by linarith
  have hxpR : 0 ≤ x + R := by linarith
  have hA_norm : ‖A‖ ≤ x + R := gauss_norm_natCast_add_le n hA
  have hB_norm : ‖B‖ ≤ x + R := gauss_norm_natCast_add_le n hB
  have hC_lower : x - R ≤ ‖C‖ := gauss_sub_le_norm_natCast_add n hC
  have hC_inv : ‖C⁻¹‖ ≤ 1 / (x - R) := by
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hxmR hC_lower
  have heA : ‖gaussParamProjectionA‖ ≤ 1 := by
    exact ContinuousLinearMap.norm_fst_le ℂ ℂ (ℂ × ℂ)
  have heB : ‖gaussParamProjectionB‖ ≤ 1 := by
    dsimp [gaussParamProjectionB]
    calc
      _ ≤ ‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ *
          ‖ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 := by
        nlinarith [norm_nonneg (ContinuousLinearMap.fst ℂ ℂ ℂ),
          norm_nonneg (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)),
          ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ,
          ContinuousLinearMap.norm_snd_le ℂ ℂ (ℂ × ℂ)]
  have heC : ‖gaussParamProjectionC‖ ≤ 1 := by
    dsimp [gaussParamProjectionC]
    calc
      _ ≤ ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ *
          ‖ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 := by
        nlinarith [norm_nonneg (ContinuousLinearMap.snd ℂ ℂ ℂ),
          norm_nonneg (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)),
          ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ,
          ContinuousLinearMap.norm_snd_le ℂ ℂ (ℂ × ℂ)]
  have hratio : (x + R) / (x - R) ≤ 2 := by
    rw [div_le_iff₀ hxmR]
    nlinarith [h3R]
  have hratio_nonneg : 0 ≤ (x + R) / (x - R) := div_nonneg hxpR hxmR.le
  have hratio_sq : ((x + R) / (x - R)) ^ 2 ≤ 4 := by
    have hleft : 0 ≤ 2 - (x + R) / (x - R) := by linarith
    have hright : 0 ≤ 2 + (x + R) / (x - R) := by positivity
    nlinarith [mul_nonneg hleft hright]
  have hfirst : ‖(A * B) • (-(C⁻¹ ^ 2) • gaussParamProjectionC)‖ ≤ 4 := by
    have hAB_norm : ‖A * B‖ ≤ (x + R) ^ 2 := by
      calc
        ‖A * B‖ = ‖A‖ * ‖B‖ := norm_mul _ _
        _ ≤ (x + R) * (x + R) := mul_le_mul hA_norm hB_norm
          (norm_nonneg B) hxpR
        _ = (x + R) ^ 2 := by ring
    have hinner_norm : ‖-(C⁻¹ ^ 2) • gaussParamProjectionC‖ ≤ (1 / (x - R)) ^ 2 := by
      calc
        ‖-(C⁻¹ ^ 2) • gaussParamProjectionC‖ ≤ ‖-(C⁻¹ ^ 2)‖ * ‖gaussParamProjectionC‖ :=
          norm_smul_le (-(C⁻¹ ^ 2) : ℂ) gaussParamProjectionC
        _ = ‖C⁻¹‖ ^ 2 * ‖gaussParamProjectionC‖ := by simp [norm_pow]
        _ ≤ ‖C⁻¹‖ ^ 2 := by
          simpa [mul_one] using mul_le_mul_of_nonneg_left heC (sq_nonneg ‖C⁻¹‖)
        _ ≤ (1 / (x - R)) ^ 2 := by
          have hnonneg : 0 ≤ ‖C⁻¹‖ := norm_nonneg _
          have hdennonneg : 0 ≤ 1 / (x - R) := by positivity
          exact (sq_le_sq₀ hnonneg hdennonneg).2 hC_inv
    calc
      ‖(A * B) • (-(C⁻¹ ^ 2) • gaussParamProjectionC)‖ ≤
          ‖A * B‖ * (1 / (x - R)) ^ 2 := by
            calc
              _ ≤ ‖A * B‖ * ‖-(C⁻¹ ^ 2) • gaussParamProjectionC‖ := norm_smul_le _ _
              _ ≤ ‖A * B‖ * (1 / (x - R)) ^ 2 :=
                mul_le_mul_of_nonneg_left hinner_norm (norm_nonneg _)
      _ ≤ (x + R) ^ 2 * (1 / (x - R)) ^ 2 := by
            exact mul_le_mul hAB_norm (le_refl _) (sq_nonneg _) (sq_nonneg _)
      _ = ((x + R) / (x - R)) ^ 2 := by
            rw [div_pow]
            field_simp
      _ ≤ 4 := hratio_sq
  have hsecond : ‖C⁻¹ • (A • gaussParamProjectionB + B • gaussParamProjectionA)‖ ≤ 4 := by
    have hAeB : ‖A • gaussParamProjectionB‖ ≤ x + R := by
      calc
        ‖A • gaussParamProjectionB‖ ≤ ‖A‖ * ‖gaussParamProjectionB‖ := norm_smul_le A gaussParamProjectionB
        _ ≤ (x + R) * 1 := mul_le_mul hA_norm heB
          (norm_nonneg gaussParamProjectionB) hxpR
        _ = x + R := mul_one _
    have hBeA : ‖B • gaussParamProjectionA‖ ≤ x + R := by
      calc
        ‖B • gaussParamProjectionA‖ ≤ ‖B‖ * ‖gaussParamProjectionA‖ := norm_smul_le B gaussParamProjectionA
        _ ≤ (x + R) * 1 := mul_le_mul hB_norm heA
          (norm_nonneg gaussParamProjectionA) hxpR
        _ = x + R := mul_one _
    have hsum : ‖A • gaussParamProjectionB‖ + ‖B • gaussParamProjectionA‖ ≤ 2 * (x + R) := by linarith
    calc
      ‖C⁻¹ • (A • gaussParamProjectionB + B • gaussParamProjectionA)‖ ≤ ‖C⁻¹‖ * ‖A • gaussParamProjectionB + B • gaussParamProjectionA‖ :=
        norm_smul_le C⁻¹ (A • gaussParamProjectionB + B • gaussParamProjectionA)
      _ ≤ ‖C⁻¹‖ * (‖A • gaussParamProjectionB‖ + ‖B • gaussParamProjectionA‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (1 / (x - R)) * (2 * (x + R)) :=
        mul_le_mul hC_inv hsum (by positivity) (by positivity)
      _ = 2 * ((x + R) / (x - R)) := by ring
      _ ≤ 4 := by linarith
  have hinner :
      ‖(A * B) • (-(C⁻¹ ^ 2) • gaussParamProjectionC) + C⁻¹ • (A • gaussParamProjectionB + B • gaussParamProjectionA)‖ ≤ 8 := by
    calc
      _ ≤ ‖(A * B) • (-(C⁻¹ ^ 2) • gaussParamProjectionC)‖ +
          ‖C⁻¹ • (A • gaussParamProjectionB + B • gaussParamProjectionA)‖ := norm_add_le _ _
      _ ≤ 8 := by linarith [hfirst, hsecond]
  have hd : ‖z / (n + 1 : ℂ)‖ ≤ ‖z‖ := by
    have hdenNat : 1 ≤ n + 1 := by omega
    have hden : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast hdenNat
    calc
      ‖z / (n + 1 : ℂ)‖ = ‖z‖ / ‖(n + 1 : ℂ)‖ := norm_div _ _
      _ = ‖z‖ / ((n : ℝ) + 1) := by rw [show ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 by norm_cast]
      _ ≤ ‖z‖ := _root_.div_le_self (norm_nonneg z) hden
  dsimp [gaussParameterSeriesRatioDeriv]
  calc
    ‖(z / (n + 1 : ℂ)) •
        ((A * B) • (-(C⁻¹ ^ 2) • gaussParamProjectionC) + C⁻¹ • (A • gaussParamProjectionB + B • gaussParamProjectionA))‖ ≤
        ‖z / (n + 1 : ℂ)‖ * 8 := by
          calc
            _ ≤ ‖z / (n + 1 : ℂ)‖ *
                ‖(A * B) • (-(C⁻¹ ^ 2) • gaussParamProjectionC) + C⁻¹ • (A • gaussParamProjectionB + B • gaussParamProjectionA)‖ :=
                  norm_smul_le _ _
            _ ≤ _ := by gcongr
    _ ≤ ‖z‖ * 8 := by gcongr
    _ = 8 * ‖z‖ := by ring

/-- Every fixed ordinary-series term is parameter-differentiable at each point away from the
denominator poles. -/
theorem gaussParameterSeriesTerm_differentiableAt
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    DifferentiableAt ℂ (fun q => gaussParameterSeriesTerm q z n) p := by
  exact (gaussParameterSeriesTerm_differentiableOn (U := gaussParameterPoleFreeDomain)
    (fun _ h => h) z n).differentiableAt (gaussParameterPoleFreeDomain_isOpen.mem_nhds hc)

end

end DOZZ.Proofs
