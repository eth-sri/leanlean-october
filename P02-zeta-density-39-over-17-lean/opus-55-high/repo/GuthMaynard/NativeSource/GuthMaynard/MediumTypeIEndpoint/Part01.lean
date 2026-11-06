module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalEndpointSlab
public import GuthMaynard.NativeSource.GuthMaynard.WeylExplicit
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Asymptotics Filter Topology
open Complex Finset MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

/-!
# The medium Type-I endpoint consumer

This file closes the one reflected Type-I window left between the direct
endpoint estimate and the finite powering range.  The first lemmas expose
the genuine Bochner-integrability and norm bounds of the common Mellin
integrand.  They are kept separate from the final witness consumer so that
the passage from a source block to a fixed-coefficient reflected polynomial
is visible to the dependency audit.
-/

/-! ## Interval-form reflected polynomials

The endpoint argument cannot use the prefix `1 ≤ m ≤ M`: a dyadic
subblock selected from that prefix could be much shorter than the genuine
dual scale `T / N`.  The following definitions and identity retain an
arbitrary common interval of Fourier modes.  They are the exact Lean
counterpart of first restricting the B-process to its stationary annulus
and only then applying dyadic pigeonholing.
-/

/-- The common finite reflected Mellin integrand is genuinely Bochner
integrable.  This is the integrand occurring in the exact B-process identity,
not a separately postulated majorant. -/
theorem integrable_typeIReflectedMellinIntegrand
    {sigma t Q : ℝ} {M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    Integrable (fun r : ℝ =>
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)) := by
  pm_1314
  pm_4161
  have hAB : A ≤ B := by
    dsimp only [A, B]
    pm_77 hMReal M hM
    nlinarith
  have hMode : ∀ m ∈ S, Integrable (fun r : ℝ =>
      typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hm
    have hmData := Finset.mem_Icc.mp hm
    have hmPos : (0 : ℝ) < m := by
      aesop
    pm_7286
  have hSum : Integrable (fun r : ℝ =>
      ∑ m ∈ S, typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) :=
    MeasureTheory.integrable_finsetSum S hMode
  apply hSum.congr
  filter_upwards with r
  unfold typeIReflectedMellinPolynomial typeICommonMellinMode
  dsimp only [S, A, B]
  pm_1063 Finset.sum_mul m _hm
  ring

/-- A setwise norm bound for the exact reflected Mellin integral.  The
coefficient polynomial and the oscillatory kernel are bounded separately,
while the literal Mellin transform retains its full `L¹` mass. -/
theorem norm_setIntegral_typeIReflectedMellinIntegrand_le
    {sigma t Q R K : ℝ} {M : ℕ} {S : Set ℝ}
    (hS : MeasurableSet S) (hQ : 0 < Q) (hR : 0 ≤ R)
    (hFixed : ∀ r ∈ S,
      ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ ≤ R)
    (hKernel : ∀ r ∈ S,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤ K) :
    ‖∫ r : ℝ in S,
        typeIReflectedMellinPolynomial sigma t Q M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
      Q * R * K * ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ := by
  pm_4811 hMellin
  have hDom : IntegrableOn
      (fun r : ℝ => Q * R * K * ‖typeIDyadicCutoffMellin r‖) S :=
    hMellin.norm.const_mul (Q * R * K) |>.integrableOn
  have hPoint : ∀ᵐ r : ℝ ∂volume.restrict S,
      ‖typeIReflectedMellinPolynomial sigma t Q M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by
    filter_upwards [ae_restrict_mem hS] with r hr
    rw [norm_mul, norm_mul,
      norm_typeIReflectedMellinPolynomial_eq_fixed sigma t Q M r hQ]
    pm_111 hF hFixed r hr hP hKernel
    calc
      Q * ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ *
          ‖typeIDyadicCutoffMellin r‖ *
            ‖typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
        Q * R * ‖typeIDyadicCutoffMellin r‖ * K := by gcongr
      _ = Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by ring
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le hDom hPoint

/-! The remaining lemmas specialize the preceding exact estimate to the
bounded Mellin window and its complement. -/

/-- Uniform stationary-window upper bound on the common oscillatory
integral.  Only the proved first/second derivative estimate is used. -/
theorem norm_typeIPowerReflectionIntegral_le_on_symmetric_window
    {sigma t H Q : ℝ} {M : ℕ}
    (hsigma : 0 < sigma) (ht : 2 ≤ t)
    (hHt : 2 * H ≤ t - 2) (hQ : 0 < Q) (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (16 / t) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t / 2) ^ (-sigma - 1 / 2) := by
  have htPos : 0 < t := by linarith
  have hTau : 1 ≤ t + r := by
    have hrLower := hr.1
    linarith
  pm_4681
  have hRaw := norm_typeIPowerReflectionIntegral_le_stationary
    hsigma hTau hA hAB
  have hTauLower : t / 2 ≤ t + r := by
    have hrLower := hr.1
    linarith
  have hTauPos : 0 < t + r := zero_lt_one.trans_le hTau
  pm_4910 hHalfPos t
  have hInv : 8 / (t + r) ≤ 16 / t := by
    rw [div_le_div_iff₀ hTauPos htPos]
    nlinarith
  pm_7284
  have hPow : (t + r) ^ (-sigma - 1 / 2) ≤
      (t / 2) ^ (-sigma - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hHalfPos hTauLower hExp
  calc
    ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (8 / (t + r)) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t + r) ^ (-sigma - 1 / 2) := hRaw
    _ ≤ (16 / t) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t / 2) ^ (-sigma - 1 / 2) := by gcongr

/-- The complementary Mellin range is polynomially small to arbitrary
order, with every finite `M` and `Q` dependence displayed. -/
theorem exists_norm_typeIReflectedMellinIntegral_tail_le
    (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t Q H : ℝ} {M : ℕ},
      0 ≤ sigma → 0 < Q → 1 ≤ M → 1 ≤ H →
      ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          (((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
  pm_4289 C hC hTail exists_typeIDyadicCutoffMellin_tail_bound n hn
  intro sigma t Q H M hsigma hQ hM hH
  pm_4681
  have hBase := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc.compl hQ
    (mul_nonneg (Nat.cast_nonneg M) (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    (S := (Set.Icc (-H) H)ᶜ)
    (R := (M : ℝ) * (M : ℝ) ^ sigma)
    (K := (2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2)))
    (fun r _hr => norm_typeIReflectedFixedPolynomial_le hsigma (t + r) M)
    (fun r _hr => norm_typeIPowerReflectionIntegral_le_trivial
      hsigma hA hAB)
  calc
    ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
              ‖typeIDyadicCutoffMellin r‖ := hBase
    _ ≤ Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          (((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
      have hFront : 0 ≤ Q * ((M : ℝ) * (M : ℝ) ^ sigma) := by
        positivity
      have hKernel : 0 ≤
          (2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2)) := by
        pm_77 hMReal M hM
        positivity
      have hMul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hTail H hH) hKernel) hFront
      simpa only [mul_assoc] using hMul

/-- On the same symmetric Mellin window the reversed-ordinate integral is
uniformly nonstationary. -/
theorem norm_typeIPowerReflectionIntegral_neg_le_on_symmetric_window
    {sigma t H Q : ℝ} {M : ℕ}
    (hsigma : 0 < sigma) (ht : 0 < t) (hHt : 2 * H ≤ t)
    (hQ : 0 < Q) (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (-t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (8 / t) * (Q / 2) ^ (-sigma) := by
  pm_4681
  have hRight : -t + r < 2 * Real.pi * (Q / 2) := by
    have hrUpper := hr.2
    have hNeg : -t + r ≤ -t / 2 := by linarith
    have hPiQ : 0 < 2 * Real.pi * (Q / 2) := by positivity
    linarith
  have hRaw := norm_powerWeighted_gmReflectionIntegral_le_right
    hsigma hA hAB hRight
  have hDen : t / 2 ≤ 2 * Real.pi * (Q / 2) - (-t + r) := by
    have hrUpper := hr.2
    have hPiQ : 0 ≤ 2 * Real.pi * (Q / 2) := by positivity
    linarith
  have hDenPos : 0 < 2 * Real.pi * (Q / 2) - (-t + r) := by
    linarith
  have hFrac : 4 / (2 * Real.pi * (Q / 2) - (-t + r)) ≤ 8 / t := by
    rw [div_le_div_iff₀ hDenPos ht]
    nlinarith
  exact hRaw.trans (mul_le_mul_of_nonneg_right hFrac
    (Real.rpow_nonneg hA.le _))

/-- Literal `L¹` mass of the fixed dyadic Mellin kernel. -/
noncomputable def typeIDyadicCutoffMellinL1 : ℝ :=
  ∫ r : ℝ, ‖typeIDyadicCutoffMellin r‖

theorem typeIDyadicCutoffMellinL1_nonneg :
    0 ≤ typeIDyadicCutoffMellinL1 := by
  unfold typeIDyadicCutoffMellinL1
  exact integral_nonneg fun _ => norm_nonneg _

/-- Restricting the fixed Mellin kernel cannot increase its total `L¹`
mass. -/
theorem integral_norm_typeIDyadicCutoffMellin_restrict_le
    (S : Set ℝ) :
    ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ ≤
      typeIDyadicCutoffMellinL1 := by
  have hInt : Integrable (fun r : ℝ => ‖typeIDyadicCutoffMellin r‖) := by
    pm_4811 hMellin
    exact hMellin.norm
  unfold typeIDyadicCutoffMellinL1
  pm_8624 Eventually.of_forall norm_nonneg hInt

/-- A large exact reflected Mellin integral forces a large value of the
fixed reflected polynomial at one bounded ordinate displacement.  The tail
and central-kernel losses are explicit premises, not hidden in a choice. -/
theorem exists_large_typeIReflectedFixedPolynomial_of_integral
    {sigma t Q H L R K E : ℝ} {M : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hKernel : ∀ r ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤ K)
    (hLarge : L ≤ ‖∫ r : ℝ,
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)‖)
    (hTail : ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)‖ ≤ E)
    (hGap : Q * R * K * typeIDyadicCutoffMellinL1 + E < L) :
    ∃ r ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ := by
  by_contra h
  push Not at h
  have hK : 0 ≤ K := by
    have hZeroMem : (0 : ℝ) ∈ Set.Icc (-H) H := by
      constructor <;> linarith
    exact (norm_nonneg _).trans (hKernel 0 hZeroMem)
  have hCentral := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc hQ hR
    (S := Set.Icc (-H) H) (R := R) (K := K) h hKernel
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hInt := integrable_typeIReflectedMellinIntegrand
    (t := t) hsigma hQ hM
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 + E := by
    rw [← hSplit]
    pm_243 norm_add_le hCentral' hTail
  linarith

section
variable {sigma t : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
include sigma t Q M hsigma hQ hM
/-- Norm form of the exact negative-mode Mellin identity. -/
theorem norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes :
    ‖∫ r : ℝ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖ =
      2 * Real.pi *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedNegativeModes sigma t Q M‖ := by
  pm_7151 sourceScalar_mul_negativeModes_eq_reflectedMellinIntegral
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
      0 < 1 / (2 * Real.pi))] at hNorm
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hNorm]
  field_simp

/-- Norm form of the exact positive-mode Mellin identity.  Conjugation
changes neither side's norm, so the same `2π` normalization as in the
negative half is retained. -/
theorem norm_typeIReflectedPositiveMellinIntegral_eq_two_pi_mul_positiveModes :
    ‖∫ r : ℝ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (-t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖ =
      2 * Real.pi *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedPositiveModes sigma t Q M‖ := by
  pm_7151 sourceScalar_mul_positiveModes_eq_reflectedMellinIntegral
  simp only [norm_star, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  rw [hNorm]
  field_simp [Real.pi_ne_zero]
end

section
variable {sigma t H L R K E : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M) (hH : 0 ≤ H) (hR : 0 ≤ R)
include sigma t H L R K E Q M hsigma hQ hM hH hR
/-- A large retained negative half forces a large value of the common
fixed reflected polynomial at a bounded Mellin displacement. -/
theorem exists_large_reflectedFixedPolynomial_of_negativeModes
    (hLarge : L ≤
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeModes sigma t Q M‖)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ E)
    (hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      2 * Real.pi * L) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (t + u) M‖ := by
  have hIntegralEq := norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes
    (sigma := sigma) (t := t) (Q := Q) (M := M) hsigma hQ hM
  have hIntegralLarge : 2 * Real.pi * L ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ := by
    rw [hIntegralEq]
    exact mul_le_mul_of_nonneg_left hLarge (by positivity)
  pm_7013

/-- The corresponding extraction for the retained positive half.  Its
fixed polynomial occurs at the reversed source ordinate, exactly as in the
proved conjugation identity. -/
theorem exists_large_reflectedFixedPolynomial_of_positiveModes
    (hLarge : L ≤
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedPositiveModes sigma t Q M‖)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ E)
    (hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      2 * Real.pi * L) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (-t + u) M‖ := by
  have hIntegralEq :=
    norm_typeIReflectedPositiveMellinIntegral_eq_two_pi_mul_positiveModes
      (sigma := sigma) (t := t) (Q := Q) (M := M) hsigma hQ hM
  have hIntegralLarge : 2 * Real.pi * L ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ := by
    rw [hIntegralEq]
    exact mul_le_mul_of_nonneg_left hLarge (by positivity)
  pm_7013
end

/-- Zero-mode decay after restoring the exact source normalization. -/
theorem exists_sourceScalar_zeroMode_decay (sigma : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (Q : ℕ), 0 < Q →
      |t| ^ j *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
        (Q : ℝ) ^ (1 - sigma) * C := by
  pm_4289 C hC hDecay typeINormalizedFourier_zero_uniform_decay sigma j
  intro t Q hQ
  pm_4147
  have hNormQ : ‖(Q : ℂ)‖ = (Q : ℝ) := by
    rw [Complex.norm_natCast]
  have hQP : (Q : ℝ) ^ (-sigma) * (Q : ℝ) =
      (Q : ℝ) ^ (1 - sigma) := by
    calc
      (Q : ℝ) ^ (-sigma) * (Q : ℝ) =
          (Q : ℝ) ^ (-sigma) * (Q : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (Q : ℝ) ^ (-sigma + 1) := by
            rw [Real.rpow_add hQReal]
      _ = (Q : ℝ) ^ (1 - sigma) := by ring_nf
  rw [norm_mul, norm_mul,
    norm_typeISourceNormalizationScalar sigma t (Q : ℝ) hQReal,
    hNormQ]
  calc
    |t| ^ j * ((Q : ℝ) ^ (-sigma) *
          ((Q : ℝ) * ‖typeINormalizedFourier sigma t 0‖)) =
      (Q : ℝ) ^ (1 - sigma) *
        (|t| ^ j * ‖typeINormalizedFourier sigma t 0‖) := by
          rw [← hQP]
          ring_nf
    _ ≤ (Q : ℝ) ^ (1 - sigma) * C := by
      gcongr
      exact hDecay t

/-- Far-frequency decay after restoring the exact source normalization. -/
theorem exists_sourceScalar_farModes_bound (sigma : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedFarTail sigma t Q M‖ ≤
        (Q : ℝ) ^ (-sigma) *
          (K * (1 + |t|) ^ (n + 2) /
            ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n)) := by
  pm_4289 K hK hFar typeINormalizedFarTail_bound_order sigma n
  intro t Q M hQ hM
  pm_4147
  rw [norm_mul, norm_typeISourceNormalizationScalar sigma t (Q : ℝ) hQReal]
  exact mul_le_mul_of_nonneg_left (hFar t Q M hQ hM)
    (Real.rpow_nonneg hQReal.le _)

/-- If only the zero frequency and the genuinely far frequencies are
discarded, one of the two retained signed Poisson halves carries a fixed
fraction of the original smooth Type-I large value.  This is the
cancellation-safe alternative used in the endpoint proof: the positive
half is not estimated term-by-term and hence no factor depending on the
dual cutoff is introduced. -/
theorem sourceSmoothBlock_large_forces_signedModes
    {Y A r M : ℕ} {sigma t V : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hV : 0 ≤ V)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8) :
    V / 4 ≤
        ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
          typeINormalizedNegativeModes sigma t (2 ^ r * Y) M‖ ∨
      V / 4 ≤
        ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
          typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ := by
  pm_4897 Q r Y
  let z : ℂ := (Q : ℂ) * typeINormalizedFourier sigma t 0
  pm_8458 neg typeINormalizedNegativeModes
  pm_8458 pos typeINormalizedPositiveModes
  pm_8458 far typeINormalizedFarTail
  let c : ℂ := typeISourceNormalizationScalar sigma t Q
  have hDecomp := typeISourceSmoothBlock_eq_mode_decomposition_of_interior
    hY hLower hUpper (M := M) (sigma := sigma) (t := t)
  have hTriangle : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by
    rw [hDecomp]
    change ‖c * (z + neg + pos + far)‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖
    rw [mul_add, mul_add, mul_add]
    calc
      ‖c * z + c * neg + c * pos + c * far‖ ≤
          ‖c * z + c * neg + c * pos‖ + ‖c * far‖ := norm_add_le _ _
      _ ≤ (‖c * z + c * neg‖ + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖c * z‖ + ‖c * neg‖) + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by ring
  have hTotal : V ≤ ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ :=
    hLarge.trans hTriangle
  pm_7601 hz z hZero
  pm_7601 hf far hFar
  by_contra h
  push Not at h
  have hn : ‖c * neg‖ < V / 4 := by simpa only [Q, neg, c] using h.1
  have hp : ‖c * pos‖ < V / 4 := by simpa only [Q, pos, c] using h.2
  linarith

/-! ## Source block to a genuine reflected large value -/

/-- Algebraic normalization from a large fixed reflected polynomial to the
coefficient-bounded wide polynomial.  This lemma is sign-neutral: the caller
supplies the actual reflected ordinate. -/
theorem large_normalized_reflected_wide_of_fixed
    {M : ℕ} {sigma u R S : ℝ} (hM : 1 < M)
    (hNormalize : S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma)
    (hLarge : R < ‖typeIReflectedFixedPolynomial sigma u M‖) :
    S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
      (normalizedTypeIReflectedCoeff sigma M) (-u)‖ := by
  have hMReal : (0 : ℝ) < M := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hM)
  have hDenom : 0 < (M : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hMReal sigma
  have hFixedDiv : R / (M : ℝ) ^ sigma <
      ‖typeIReflectedFixedPolynomial sigma u M /
        (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDenom, div_lt_div_iff₀ hDenom hDenom]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hLarge hDenom
  have hIdentity := wideDirichletPoly_normalizedTypeIReflectedCoeff
    (sigma := sigma) (u := u) hM
  let P : ℂ := wideDirichletPoly 1 (Nat.clog 2 M)
    (normalizedTypeIReflectedCoeff sigma M) (-u)
  let z : ℂ := (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)
  have hRearrange :
      typeIReflectedFixedPolynomial sigma u M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ) = P + z := by
    dsimp only [P, z]
    calc
      typeIReflectedFixedPolynomial sigma u M /
            (((M : ℝ) ^ sigma : ℝ) : ℂ) =
          (typeIReflectedFixedPolynomial sigma u M /
              (((M : ℝ) ^ sigma : ℝ) : ℂ) -
            (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by ring
      _ = wideDirichletPoly 1 (Nat.clog 2 M)
            (normalizedTypeIReflectedCoeff sigma M) (-u) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by rw [← hIdentity]
  have hTriangle :
      ‖typeIReflectedFixedPolynomial sigma u M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ ≤
        ‖P‖ + (M : ℝ) ^ (-sigma) := by
    rw [hRearrange]
    calc
      ‖P + z‖ ≤ ‖P‖ + ‖z‖ := norm_add_le _ _
      _ = ‖P‖ + (M : ℝ) ^ (-sigma) := by
        dsimp only [z]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hMReal.le _)]
  dsimp only [P] at hTriangle ⊢
  linarith

/-- A large interior source block yields one of the two actual normalized
reflected wide polynomials.  The zero and far modes are removed once, and
the sign is selected only after the exact Poisson identity. -/
theorem exists_signed_shift_large_normalized_reflected_wide
    {Y A r M : ℕ} {sigma t V H R K E S : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hsigma : 0 ≤ sigma) (hM : 1 < M)
    (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernelNeg : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hKernelPos : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTailNeg :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailPos :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma (-t)
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap :
      ((2 ^ r * Y : ℕ) : ℝ) * R * K *
          typeIDyadicCutoffMellinL1 + E < Real.pi * V / 2)
    (hNormalize :
      S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma) :
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) := by
  pm_1123
  have hMOne : 1 ≤ M := hM.le
  rcases sourceSmoothBlock_large_forces_signedModes
      hY hLower hUpper hV hLarge hZero hFar with hNeg | hPos
  · left
    pm_4682
    obtain ⟨u, hu, hFixed⟩ :=
      exists_large_reflectedFixedPolynomial_of_negativeModes
        hsigma hQ hMOne hH hR hNeg hKernelNeg hTailNeg hGap'
    exact ⟨u, hu,
      large_normalized_reflected_wide_of_fixed hM hNormalize hFixed⟩
  · right
    pm_4682
    obtain ⟨u, hu, hFixed⟩ :=
      exists_large_reflectedFixedPolynomial_of_positiveModes
        hsigma hQ hMOne hH hR hPos hKernelPos hTailPos hGap'
    have hWide := large_normalized_reflected_wide_of_fixed
      hM hNormalize hFixed
    refine ⟨u, hu, ?_⟩
    convert hWide using 1
    ring_nf

/-- Translating the ordinate of a wide polynomial is exactly the same
unimodular twist of its coefficients as for an ordinary dyadic block. -/
theorem wideDirichletPoly_translate
    (Q k : ℕ) (a : ℕ → ℂ) (c t : ℝ) :
    wideDirichletPoly Q k a (t + c) =
      wideDirichletPoly Q k (phaseShiftCoeffs c a) t := by
  unfold wideDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    exact lt_of_le_of_lt (Nat.zero_le Q) (Finset.mem_Ioc.mp hn).1
  pm_4837
  rw [phaseShiftCoeffs, ite_eq_right hnPos.ne', mul_assoc,
    ← Complex.cpow_add _ _ hnNe]
  congr 2
  push_cast
  ring

/-- Bounded pointwise displacement followed by unit-bin selection.  The
weight on an image point is its complete fibre cardinality, so collisions
cannot silently discard multiplicity. -/
theorem exists_separated_bounded_shift_image_medium
    (W : Finset ℝ) (shift : ℝ → ℝ) (H : ℝ)
    (_hH : 0 ≤ H) (hSeparated : IsSeparated 1 W)
    (hShift : ∀ t ∈ W, |t - shift t| ≤ H) :
    ∃ U ⊆ W.image shift, IsSeparated 1 U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card := by
  classical
  let weight : ℝ → ℕ := fun _ => 1
  let shiftedWeight : ℝ → ℕ := fun u =>
    ∑ t ∈ W.filter (fun x => shift x = u), weight t
  have hLocalOriginal : ∀ z : ℤ,
      ∑ t ∈ W.filter
          (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1), weight t ≤ 1 := by
    intro z
    have hCard :
        (W.filter (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1)).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro x y hx hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hxy
      have hSep := hSeparated x hx.1 y hy.1 hxy
      rw [Real.dist_eq] at hSep
      have hlt : |x - y| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
      linarith
    simpa [weight] using hCard
  have hLocalShifted : ∀ z : ℤ,
      ∑ u ∈ (W.image shift).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1), shiftedWeight u ≤
        2 * ⌈H⌉₊ + 1 := by
    intro z
    simpa only [shiftedWeight, weight, mul_one] using
      shifted_bin_weight_le_of_unit_bin_weight W weight id shift H 1
        (by simpa only [id_eq] using hShift) hLocalOriginal z
  obtain ⟨U, hUImage, hUSep, hWeight⟩ :=
    weighted_separated_selection (W.image shift) shiftedWeight
      (2 * ⌈H⌉₊ + 1) hLocalShifted
  have hAll : W.filter (fun t => shift t ∈ W.image shift) = W := by
    apply Finset.filter_eq_self.mpr
    pm_4831 t ht
  have hFiber := Finset.sum_fiberwise_eq_sum_filter W (W.image shift)
    shift weight
  rw [hAll] at hFiber
  have hTotal : ∑ u ∈ W.image shift, shiftedWeight u = W.card := by
    simpa [shiftedWeight, weight] using hFiber
  refine ⟨U, hUImage, hUSep, ?_⟩
  rw [← hTotal]
  simpa only [mul_assoc] using hWeight

/-- Family form of the reflected extraction.  Each source ordinate may
choose its own bounded Mellin displacement, but the output is reseparated,
translated to one positive base interval, and pigeonholed onto one common
ordinary dyadic block.  The displayed cardinality loss keeps every fibre of
the displacement map. -/
theorem extract_common_reflected_mhh_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
      W.card ≤
        (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
      ∀ v ∈ U,
        S / Nat.clog 2 M ≤
          ‖dirichletPoly (2 ^ j)
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma M)) v‖ := by
  classical
  let reflect : ℝ → ℝ := fun t => 3 * T - t
  let Wrev : Finset ℝ := W.image reflect
  have hreflectInj : Function.Injective reflect := by
    intro x y hxy
    dsimp only [reflect] at hxy
    linarith
  have hWrevCard : Wrev.card = W.card := by
    dsimp only [Wrev]
    exact Finset.card_image_iff.mpr fun _ hx _ hy hxy =>
      hreflectInj hxy
  have hWrevSeparated : IsSeparated 1 Wrev := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, hyEq⟩
    have htxy : tx ≠ ty := by
      intro h
      subst ty
      exact hxy hyEq
    have hsep := hSeparated tx htx ty hty htxy
    subst y
    rw [Real.dist_eq] at hsep ⊢
    dsimp only [reflect]
    rw [show 3 * T - tx - (3 * T - ty) = -(tx - ty) by ring, abs_neg]
    exact hsep
  have hOriginalMem : ∀ x ∈ Wrev, 3 * T - x ∈ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    convert ht using 1
    dsimp only [reflect]
    ring
  let displacement : ℝ → ℝ := fun x =>
    if hx : x ∈ Wrev then Classical.choose (hEach (3 * T - x)
      (hOriginalMem x hx)) else 0
  have hDisplacementMem : ∀ x ∈ Wrev,
      displacement x ∈ Set.Icc (-H) H := by
    intro x hx
    simp only [displacement, dite_eq_left hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).1
  have hDisplacementLarge : ∀ x ∈ Wrev,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M)
          (-((3 * T - x) + displacement x))‖ := by
    intro x hx
    simp only [displacement, dite_eq_left hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).2
  pm_4906 x Wrev hx hWrevSeparated
  have hWide : ∀ v ∈ U₀,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M)) v‖ := by
    intro v hv
    have hvImage := hU₀Image hv
    rcases Finset.mem_image.mp hvImage with ⟨x, hx, rfl⟩
    have hLarge := hDisplacementLarge x hx
    have hArg : -((3 * T - x) + displacement x) =
        shift x + (-3 * T) := by
      dsimp only [shift]
      ring
    rw [hArg, wideDirichletPoly_translate] at hLarge
    exact hLarge
  pm_4815 hClog M hM
  obtain ⟨j, hj, U, hUsub, hCardDyadic, hLargeDyadic⟩ :=
    exists_dyadic_block_and_subset 1 (Nat.clog 2 M)
      (phaseShiftCoeffs (-3 * T)
        (normalizedTypeIReflectedCoeff sigma M)) U₀ S hClog
      (fun v hv => (hWide v hv).le)
  pm_4684
  · intro v hv
    pm_4683
    pm_8127
    · have hduUpper : displacement x ≤ H := hdu.2
      linarith
    · have hduLower : -H ≤ displacement x := hdu.1
      linarith
  · intro v hv
    pm_4683
    pm_6761
  · rw [← hWrevCard]
    calc
      Wrev.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U₀.card := hCardShift
      _ ≤ 2 * (2 * ⌈H⌉₊ + 1) *
          ((Nat.clog 2 M) * U.card) := by
            gcongr
            exact_mod_cast hCardDyadic
      _ = (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card := by ring
  · intro v hv
    simpa only [mul_one] using hLargeDyadic v hv

/-- Positive-sign companion to `extract_common_reflected_mhh_block`.
The positive Poisson half already lands at the positive ordinate `t - u`,
so no reflection about `3T/2` and no coefficient phase shift are needed. -/
theorem extract_common_positive_reflected_mhh_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
      W.card ≤
        (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
      ∀ v ∈ U,
        S / Nat.clog 2 M ≤
          ‖dirichletPoly (2 ^ j)
            (normalizedTypeIReflectedCoeff sigma M) v‖ := by
  classical
  let displacement : ℝ → ℝ := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hDisplacementMem : ∀ t ∈ W,
      displacement t ∈ Set.Icc (-H) H := by
    pm_4788 displacement
  have hDisplacementLarge : ∀ t ∈ W,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M)
          (t - displacement t)‖ := by
    pm_6417 displacement
  pm_4906 t W ht hSeparated
  have hWide : ∀ v ∈ U₀,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) v‖ := by
    intro v hv
    rcases Finset.mem_image.mp (hU₀Image hv) with ⟨t, ht, rfl⟩
    exact hDisplacementLarge t ht
  pm_4815 hClog M hM
  obtain ⟨j, hj, U, hUsub, hCardDyadic, hLargeDyadic⟩ :=
    exists_dyadic_block_and_subset 1 (Nat.clog 2 M)
      (normalizedTypeIReflectedCoeff sigma M) U₀ S hClog
      (fun v hv => (hWide v hv).le)
  pm_4684
  · intro v hv
    pm_4685
    pm_8127
    · linarith [hdu.2]
    · linarith [hdu.1]
  · intro v hv
    pm_4685
    pm_6761
  · calc
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U₀.card := hCardShift
      _ ≤ 2 * (2 * ⌈H⌉₊ + 1) *
          ((Nat.clog 2 M) * U.card) := by
            gcongr
            exact_mod_cast hCardDyadic
      _ = (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card := by ring
  · intro v hv
    simpa only [mul_one] using hLargeDyadic v hv

/-- A cancellation-safe family pigeonhole for the two retained Poisson
signs.  No point is discarded before the signed alternative is known; the
only loss is the explicit factor two. -/
theorem select_common_signed_reflected_family
    {M : ℕ} {sigma H S : ℝ} (W : Finset ℝ)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    (∃ W' : Finset ℝ, W' ⊆ W ∧ W.card ≤ 2 * W'.card ∧
      ∀ t ∈ W', ∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
    (∃ W' : Finset ℝ, W' ⊆ W ∧ W.card ≤ 2 * W'.card ∧
      ∀ t ∈ W', ∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) := by
  classical
  let isNegative : ℝ → Prop := fun t =>
    ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖
  let Wneg := W.filter isNegative
  by_cases hLargeHalf : W.card ≤ 2 * Wneg.card
  · left
    pm_8901 Wneg hLargeHalf
    exact (Finset.mem_filter.mp ht).2
  · right
    let Wpos := W.filter (fun t => ¬ isNegative t)
    have hPartition : Wneg.card + Wpos.card = W.card := by
      simpa only [Wneg, Wpos, isNegative] using
        W.card_filter_add_card_filter_not isNegative
    have hCard : W.card ≤ 2 * Wpos.card := by omega
    pm_8901 Wpos hCard
    have htData := Finset.mem_filter.mp ht
    rcases hEach t htData.1 with hNeg | hPos
    · exact False.elim (htData.2 hNeg)
    · exact hPos

/-
/-- One cancellation-safe interface for the two retained Poisson signs.
The coefficient sequence is existential because the negative sign carries
the fixed translation by `-3T`, whereas the positive sign does not.  The
last field identifies its norm with the same normalized reflected block at
an actual positive ordinate in `[T/2,5T/2]`; this is the bridge needed by
the Weyl alternative after the finite sign and displacement selections. -/
theorem extract_common_signed_reflected_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      ∃ a : ℕ → ℂ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
        W.card ≤ 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
          (Nat.clog 2 M) * U.card ∧
        (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
        (∀ v ∈ U, S / Nat.clog 2 M ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly (2 ^ j) a v‖ =
            ‖dirichletPoly (2 ^ j)
              (normalizedTypeIReflectedCoeff sigma M) w‖) := by
  rcases select_common_signed_reflected_family W hEach with
    ⟨Wsign, hWsign, hSignCard, hNegative⟩ |
      ⟨Wsign, hWsign, hSignCard, hPositive⟩
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hNegative
    let a : ℕ → ℂ := phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M)
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one (by linarith)
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨3 * T - v, ?_, ?_⟩
      · rw [Set.mem_Icc]
        have hvRange := hURange v hv
        constructor <;> linarith
      · dsimp only [a]
        exact norm_phaseShifted_normalized_reflected_eq sigma T v (2 ^ j) M
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hPositive
    let a : ℕ → ℂ := normalizedTypeIReflectedCoeff sigma M
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      exact norm_normalizedTypeIReflectedCoeff_le_one (by linarith)
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨v, hURange v hv, ?_⟩
      rfl
-/

/-! ## Dual-scale arithmetic -/

/-- The transition width used in the reflected endpoint argument.  The
factor `σ - 1/2` is the exact gap that degenerates at the left edge of the
critical strip; scaling by its reciprocal gives the Weyl branch a uniform
positive exponent margin.  The dedicated term in
`classicalEndpointLossParameter` makes this width epsilon-small. -/
noncomputable def reflectedEndpointScaleSlack (σ d : ℝ) : ℝ :=
  100 * d / (σ - 1 / 2)

theorem reflectedEndpointScaleSlack_pos
    {σ d : ℝ} (hσ : 1 / 2 < σ) (hd : 0 < d) :
    0 < reflectedEndpointScaleSlack σ d := by
  unfold reflectedEndpointScaleSlack
  positivity

theorem four_mul_le_reflectedEndpointScaleSlack
    {σ d : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1) (hd : 0 ≤ d) :
    4 * d ≤ reflectedEndpointScaleSlack σ d := by
  unfold reflectedEndpointScaleSlack
  by_cases hdz : d = 0
  · simp [hdz]
  · have hdPos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdz)
    pm_4686 hgap σ
    rw [le_div_iff₀ hgap]
    nlinarith

/-- Both critical-strip side-gap terms in the global loss parameter make the
reflected transition width smaller than one sixth of the endpoint scale. -/
theorem reflectedEndpointScaleSlack_le_tau0_sixth
    {σ τ₀ d : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (hdUpperGap : d ≤ (1 - σ) / 1000) :
    reflectedEndpointScaleSlack σ d ≤ τ₀ / 6 := by
  pm_4686 hgap σ
  pm_7152 hDensity
  have hSlackCore : reflectedEndpointScaleSlack σ d ≤
      (2 / 5 : ℝ) * (1 - σ) := by
    unfold reflectedEndpointScaleSlack
    by_cases hmid : σ ≤ 3 / 4
    · have hOneSigma : 1 / 4 ≤ 1 - σ := by linarith
      have hdScaled : 100 * d ≤ (σ - 1 / 2) / 10 := by nlinarith
      rw [div_le_iff₀ hgap]
      have hgapUpper : σ - 1 / 2 ≤ 1 / 4 := by linarith
      nlinarith [mul_pos hgap (sub_pos.mpr hσUpper)]
    · have hgapQuarter : 1 / 4 ≤ σ - 1 / 2 := by linarith
      have hdScaled : 100 * d ≤ (1 - σ) / 10 := by nlinarith
      rw [div_le_iff₀ hgap]
      nlinarith
  nlinarith

/-- Natural power selection after augmenting an actual reflected scale by an
arbitrary nonnegative transition width.  The returned `k` is the literal
natural exponent used by finite Dirichlet-polynomial powering. -/
theorem exists_bounded_positive_power_scale_reduction_with_gap
    {τ₀ τ U s : ℝ} (hτ₀ : 0 < τ₀) (hs : 0 ≤ s)
    (hNear : 4 * τ₀ / 3 - s ≤ τ)
    (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ ⌈3 * (U + s) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + s) / k ∧
      (τ + s) / k ≤ τ₀ ∧
      τ / k ≤ (τ + s) / k ∧
      (τ + s) / k - τ / k ≤ s := by
  have hRaised : 4 * τ₀ / 3 ≤ τ + s := by linarith
  have hUpper : τ + s ≤ U + s := by linarith
  pm_351 k hk hkB hkLower hkUpper exists_bounded_positive_power_scale_reduction hτ₀ hRaised hUpper
  pm_77 hkReal k hk
  pm_74 hkPos k hk
  refine ⟨k, hk, hkB, hkLower, hkUpper, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hkPos.le
  · rw [← sub_div]
    have hGap : s / (k : ℝ) ≤ s := div_le_self hs hkReal
    calc
      (τ + s - τ) / (k : ℝ) = s / (k : ℝ) := by ring
      _ ≤ s := hGap

/-- Endpoint form of the preceding selector.  It also records the lower
bound for the actual powered scale and pays exactly for replacing that scale
by the augmented one. -/
theorem exists_bounded_positive_power_augmented_endpoint_with_gap
    {σ τ₀ τ U s d : ℝ}
    (_hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
    (hs : 0 ≤ s) (_hdUpper : d ≤ (1 - σ) / 1000)
    (hSmall : s ≤ τ₀ / 6)
    (hNear : 4 * τ₀ / 3 - s ≤ τ) (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧
      k ≤ ⌈3 * (U + s) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + s) / k ∧
      (τ + s) / k ≤ τ₀ ∧
      τ / k ≤ (τ + s) / k ∧
      τ₀ / 2 ≤ τ / k ∧
      (3 * (1 - σ) / τ₀) *
          ((τ + s) / k - τ / k) ≤
        (2 * s / τ₀) * (τ / k) := by
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hkGap⟩ :=
    exists_bounded_positive_power_scale_reduction_with_gap
      hcert.tau0_pos hs hNear hτUpper
  pm_7152 hTauDensity
  have hActualLower : τ₀ / 2 ≤ τ / k := by
    have hGapAt : (τ + s) / k - s ≤ τ / k := by linarith
    have hCore : τ₀ / 2 ≤ (τ + s) / k - s := by
      nlinarith [hkLower]
    exact hCore.trans hGapAt
  have hTargetLeOne : 3 * (1 - σ) / τ₀ ≤ 1 := by
    rw [div_le_one hcert.tau0_pos]
    exact hTauDensity
  have hGapNonneg : 0 ≤ (τ + s) / k - τ / k :=
    sub_nonneg.mpr hkActual
  refine ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hActualLower, ?_⟩
  calc
    (3 * (1 - σ) / τ₀) * ((τ + s) / k - τ / k) ≤ 1 * s := by
      gcongr
    _ ≤ (2 * s / τ₀) * (τ / k) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hcert.tau0_pos).2
      have hActualNonneg : 0 ≤ τ / (k : ℝ) :=
        (div_nonneg hcert.tau0_pos.le (by norm_num)).trans hActualLower
      nlinarith [mul_nonneg hs hActualNonneg]

/-- The dedicated half-line-gap budget controls both the enlarged natural
power ceiling and the endpoint-exponent displacement caused by
`reflectedEndpointScaleSlack`. -/
theorem reflected_total_power_budget_with_gap_le
    {sigma tau0 eta d : ℝ}
    (hsigma : 1 / 2 < sigma) (_hsigmaUpper : sigma < 1)
    (htau0 : 0 < tau0) (_heta : 0 < eta)
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hdEta : d ≤ eta / 1000)
    (hdReflected : d ≤ eta * tau0 * (sigma - 1 / 2) / 1000000) :
    let s := reflectedEndpointScaleSlack sigma d
    let g := (sigma - 1 / 2) / 2
    let U := 2 / g
    let B := ⌈3 * (U + s) / (2 * tau0)⌉₊
    24 * d * (B : ℝ) + 2 * s / tau0 + 6 * d ≤ eta / 4 := by
  dsimp only
  let gap : ℝ := sigma - 1 / 2
  pm_4638 hgap gap
  let s : ℝ := 100 * d / gap
  pm_4760
  let U : ℝ := 4 / gap
  pm_3981
  let x : ℝ := 3 * (U + s) / (2 * tau0)
  pm_82 hx x
  let B : ℕ := ⌈x⌉₊
  have hB : (B : ℝ) < x + 1 := by
    simpa only [B] using Nat.ceil_lt_add_one hx
  have hdGapTau : d / (tau0 * gap) ≤ eta / 1000000 := by
    rw [div_le_iff₀ (mul_pos htau0 hgap)]
    have hrewrite : eta / 1000000 * (tau0 * gap) =
        eta * tau0 * gap / 1000000 := by ring
    rw [hrewrite]
    simpa only [gap] using hdReflected
  have hsTau : s / tau0 ≤ eta / 10000 := by
    dsimp only [s]
    calc
      (100 * d / gap) / tau0 = 100 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 100 * (eta / 1000000) := by gcongr
      _ = eta / 10000 := by ring
  have hdUTau : d * U / tau0 ≤ 4 * eta / 1000000 := by
    dsimp only [U]
    calc
      d * (4 / gap) / tau0 = 4 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 4 * (eta / 1000000) := by gcongr
      _ = 4 * eta / 1000000 := by ring
  have hdSTau : d * s / tau0 ≤ eta / 10000 := by
    calc
      d * s / tau0 = d * (s / tau0) := by ring
      _ ≤ 1 * (eta / 10000) := by
        exact mul_le_mul hdOne hsTau (div_nonneg hs.le htau0.le) (by norm_num)
      _ = eta / 10000 := by ring
  have hdB : d * (B : ℝ) <
      (3 / 2 : ℝ) * (d * U / tau0) +
        (3 / 2 : ℝ) * (d * s / tau0) + d := by
    have hmul := mul_lt_mul_of_pos_left hB hd
    dsimp only [x] at hmul
    have hrewrite : d * (3 * (U + s) / (2 * tau0) + 1) =
        (3 / 2 : ℝ) * (d * U / tau0) +
          (3 / 2 : ℝ) * (d * s / tau0) + d := by
      field_simp [htau0.ne']
    rwa [hrewrite] at hmul
  have hdB' : d * (B : ℝ) ≤ eta / 100 := by
    nlinarith [hdUTau, hdSTau, hdEta]
  have hFinal :
      24 * d * (B : ℝ) + 2 * s / tau0 + 6 * d ≤ eta / 4 := by
    have hTwo : 2 * s / tau0 ≤ 2 * (eta / 10000) := by
      calc
        2 * s / tau0 = 2 * (s / tau0) := by ring
        _ ≤ 2 * (eta / 10000) := by gcongr
    nlinarith [hdB', hTwo, hdEta]
  have hSrewrite : reflectedEndpointScaleSlack sigma d = s := by
    rfl
  have hUrewrite : 2 / ((sigma - 1 / 2) / 2) = U := by
    dsimp only [U, gap]
    field_simp [show sigma - 1 / 2 ≠ 0 by linarith]
    norm_num
  rw [hSrewrite, hUrewrite]
  simpa only [B, x] using hFinal

/-- A dyadic block selected from the expanded reflected prefix retains a
literal lower bound for its logarithmic height scale.  Floors are kept in
the hypothesis through the natural upper bound on `M`; no equality with the
ideal dual length is asserted. -/
theorem reflected_dyadic_scale_lower_of_expanded_cutoff
    {T τ d : ℝ} {Q P M : ℕ}
    (hT : 1 < T) (hQ : 1 < Q) (hP : 1 < P)
    (hτ : 1 < τ) (hτTwo : τ < 2)
    (hd : 0 ≤ d) (hScale : (Q : ℝ) ^ τ = T)
    (hPM : P ≤ M) (hM : (M : ℝ) ≤ T ^ (1 + d) / Q) :
    1 / (1 / 2 + d) ≤ typeILogarithmicScale T P := by
  pm_8479 hTPos hTOne
  pm_4728 hQReal Q hQ
  have hSqrtQ : T ^ (1 / 2 : ℝ) ≤ (Q : ℝ) := by
    pm_5880
    pm_5796 τ
  have hSplit : T ^ (1 + d) = T ^ (1 / 2 + d) * T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hMUpper : (M : ℝ) ≤ T ^ (1 / 2 + d) := by
    calc
      (M : ℝ) ≤ T ^ (1 + d) / Q := hM
      _ ≤ T ^ (1 + d) / T ^ (1 / 2 : ℝ) := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hTPos.le _)
          (Real.rpow_pos_of_pos hTPos _)
          hSqrtQ
      _ = T ^ (1 / 2 + d) := by
        rw [hSplit]
        field_simp [(Real.rpow_pos_of_pos hTPos (1 / 2 : ℝ)).ne']
  have hPUpper : (P : ℝ) ≤ T ^ (1 / 2 + d) := by
    exact (by exact_mod_cast hPM : (P : ℝ) ≤ M) |>.trans hMUpper
  pm_5776 ha
  have hInv : 0 ≤ 1 / (1 / 2 + d) := by positivity
  have hRaised := Real.rpow_le_rpow (Nat.cast_nonneg P) hPUpper hInv
  have hCancel : (T ^ (1 / 2 + d)) ^ (1 / (1 / 2 + d)) = T := by
    rw [← Real.rpow_mul hTPos.le]
    field_simp [ha.ne']
    exact Real.rpow_one T
  apply (Real.le_logb_iff_rpow_le (by exact_mod_cast hP) hTPos).mpr
  exact hRaised.trans_eq hCancel

/-- If the exceptional zeta window is nonempty, its entire upper endpoint
lies strictly below the Weyl threshold.  This strengthens the pointwise
strict inequality stored in `EndpointScaleCertificate` to the uniform gap
needed when an epsilon-power estimate is assembled. -/
theorem endpoint_zeta_window_upper_lt_weyl
    {σ τ₀ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hWindow : 2 < 4 * τ₀ / 3) :
    4 * τ₀ / 3 < 6 * σ - 3 := by
  have hAtTwo := hcert.zeta_window 2 (by norm_num) hWindow
  have hSigma : 5 / 6 < σ := by
    rcases hAtTwo with hFalse | hTwo
    · exact False.elim hFalse
    · linarith
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · have : 4 * τ₀ / 3 < 2 := by
      calc
        4 * τ₀ / 3 ≤ 4 * (2 - σ) / 3 := by gcongr
        _ < 2 := by linarith
    linarith
  · calc
      4 * τ₀ / 3 ≤ 4 * (3 * σ - 1) / 3 := by gcongr
      _ < 6 * σ - 3 := by linarith

/-- Exhaustive reflected split with the gap-scaled transition width.  The
strict complementary alternative now retains a margin large enough to pay
all floored-cutoff and finite-power losses uniformly as `σ ↓ 5/6`. -/
theorem reflected_actual_scale_powered_gap_or_weyl_margin
    {σ τ₀ τ d : ℝ}
    (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d)
    (hτLower : 1 / (1 / 2 + d) ≤ τ) :
    let s := reflectedEndpointScaleSlack σ d
    4 * τ₀ / 3 - s ≤ τ ∨ τ < 6 * σ - 3 - s := by
  dsimp only
  let s := reflectedEndpointScaleSlack σ d
  have hs : 0 < s := reflectedEndpointScaleSlack_pos hσ hd
  have hFour : 4 * d ≤ s :=
    four_mul_le_reflectedEndpointScaleSlack hσ hσUpper hd.le
  by_cases hNear : 4 * τ₀ / 3 - s ≤ τ
  · exact Or.inl hNear
  right
  have hBelow : τ + s < 4 * τ₀ / 3 := by linarith
  pm_4687
  have hNearTwo : 2 - 4 * d < τ := hReciprocal.trans_le hτLower
  have hWindow : 2 < 4 * τ₀ / 3 := by linarith
  have hWeyl := endpoint_zeta_window_upper_lt_weyl hσUpper hcert hWindow
  linarith

/-- The numerical heart of the complementary reflected branch.  The first
inequality is the exact dual-length relation `P < M ≤ T^(1+d-1/τ)` written
in logarithmic coordinates.  Together with the gap-scaled transition it
leaves a fixed `s/24` between the reflected Weyl exponent and the literal
stationary threshold exponent. -/
theorem reflected_weyl_exponent_margin
    {σ τ θ d u s : ℝ}
    (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hd : 0 < d) (huD : u ≤ d)
    (hs : s = reflectedEndpointScaleSlack σ d)
    (hτOne : 1 < τ) (hτTwo : τ < 2)
    (hDual : 1 / θ ≤ 1 + d - 1 / τ)
    (hθLower : 1 / (1 / 2 + d) ≤ θ)
    (hFar : θ < 6 * σ - 3 - s) :
    1 / (2 * θ) + 1 / 6 + 2 * d + s / 24 ≤
      1 / 2 - u - d * σ + (σ - 1) / τ - d := by
  pm_4686 hgap σ
  have hgapUpper : σ - 1 / 2 < 1 / 2 := by linarith
  have hτPos : 0 < τ := zero_lt_one.trans hτOne
  have hθPos : 0 < θ := by
    pm_5776 hden
    exact (div_pos (by norm_num) hden).trans_le hθLower
  pm_4687
  have hSigmaMargin : s - 4 * d < 6 * σ - 5 := by
    linarith
  have hScaleSlack : 200 * d ≤ s := by
    subst s
    unfold reflectedEndpointScaleSlack
    rw [le_div_iff₀ hgap]
    nlinarith [mul_pos hd hgap]
  have hTauGap : (σ - 1 / 2) / 2 < (σ - 1 / 2) / τ := by
    exact div_lt_div_of_pos_left hgap hτPos hτTwo
  have hInvTheta : 1 / (2 * θ) ≤ (1 + d - 1 / τ) / 2 := by
    have := div_le_div_of_nonneg_right hDual (by norm_num : (0 : ℝ) ≤ 2)
    calc
      1 / (2 * θ) = (1 / θ) / 2 := by field_simp [hθPos.ne']
      _ ≤ (1 + d - 1 / τ) / 2 := this
  have hdSigma : d * σ < d := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hσUpper hd
  have hSourceGap : 1 / 6 + s / 12 - d / 3 < (σ - 1 / 2) / 2 := by
    linarith
  have hActualGap : 1 / 6 + s / 12 - d / 3 < (σ - 1 / 2) / τ :=
    hSourceGap.trans hTauGap
  have hLoss :
      u + d * σ + 7 * d / 2 + s / 24 ≤ s / 12 - d / 3 := by
    linarith
  have hDivIdentity :
      (σ - 1) / τ + 1 / (2 * τ) = (σ - 1 / 2) / τ := by
    field_simp [hτPos.ne']
    ring
  calc
    1 / (2 * θ) + 1 / 6 + 2 * d + s / 24 ≤
        (1 + d - 1 / τ) / 2 + 1 / 6 + 2 * d + s / 24 := by
      linarith
    _ ≤ 1 / 2 - u - d * σ + (σ - 1) / τ - d := by
      rw [show (1 + d - 1 / τ) / 2 =
        1 / 2 + d / 2 - 1 / (2 * τ) by ring]
      linarith

/-! ## Dyadic realization of a selected source block -/

/-- The fixed coefficient sequence of a source-smooth Type-I block.  All
ordinate dependence remains in the ordinary Dirichlet phase. -/
noncomputable def typeISourceDirichletCoeff
    (Y A r : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (typeISourceSmoothWeight Y A r n : ℂ) *
    (n : ℂ) ^ (-(σ : ℂ))

/-- At integer arguments the complete source weight is between zero and one.
This includes both sharp tail boundaries and is therefore valid for every
source scale, not only the interior Poisson scales. -/
theorem typeISourceSmoothWeight_nat_mem_unitInterval
    (Y A r n : ℕ) :
    0 ≤ typeISourceSmoothWeight Y A r n ∧
      typeISourceSmoothWeight Y A r n ≤ 1 := by
  rw [typeISourceSmoothWeight, typeITailBoundary_natCast]
  split_ifs
  · have hCutNonneg := typeIDyadicCutoff_nonneg
        ((n : ℝ) / (2 ^ r * Y : ℕ))
    have hCutUpper := typeIDyadicCutoff_le_one
        ((n : ℝ) / (2 ^ r * Y : ℕ))
    simpa only [one_mul] using ⟨hCutNonneg, hCutUpper⟩
  · simp

/-- A source coefficient can be nonzero only inside the fixed annulus
`(Q/2,2Q)`, where `Q = 2^r Y`.  The strict inequalities record the zeroes of
the cutoff at both endpoints. -/
theorem typeISourceSmoothWeight_support
    {Y A r n : ℕ}
    (hn : typeISourceSmoothWeight Y A r n ≠ 0) :
    (((2 ^ r * Y : ℕ) : ℝ) / 2) < n ∧
      (n : ℝ) < 2 * (2 ^ r * Y : ℕ) := by
  pm_4897 Q r Y
  have hCut : typeIDyadicCutoff ((n : ℝ) / Q) ≠ 0 := by
    intro h
    apply hn
    unfold typeISourceSmoothWeight
    rw [h, mul_zero]
  have hQ : 0 < Q := by
    by_contra hnot
    have hQZero : Q = 0 := Nat.eq_zero_of_not_pos hnot
    apply hCut
    apply typeIDyadicCutoff_eq_zero_of_le_half
    simp [hQZero]
  constructor
  · by_contra hnot
    have hnUpper : (n : ℝ) ≤ (Q : ℝ) / 2 := by
      simpa only [Q] using le_of_not_gt hnot
    have hRatio : (n : ℝ) / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ)]
      nlinarith
    exact hCut (typeIDyadicCutoff_eq_zero_of_le_half hRatio)
  · by_contra hnot
    have hnLower : 2 * (Q : ℝ) ≤ n := by
      simpa only [Q] using le_of_not_gt hnot
    have hRatio : 2 ≤ (n : ℝ) / Q := by
      rw [le_div_iff₀ (by exact_mod_cast hQ)]
      exact hnLower
    exact hCut (typeIDyadicCutoff_eq_zero_of_two_le hRatio)

/-- Source normalization at the lower edge of its fixed annulus.  This is the
finite analogue of multiplying a smooth zeta block by `Q^σ`; the harmless
factor two makes the coefficient bound literal even at the left edge. -/
noncomputable def normalizedTypeISourceDirichletCoeff
    (Y A r : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  ((((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ : ℝ) : ℂ)) *
    typeISourceDirichletCoeff Y A r σ n

section
variable (Y A r : ℕ)
include Y A r
/-- The normalized coefficients of the actual source-smooth block are bounded
by one on the entire natural line. -/
theorem norm_normalizedTypeISourceDirichletCoeff_le_one (σ : ℝ) (hσ : 0 ≤ σ) :
    ∀ n : ℕ, ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
  intro n
  by_cases hw : typeISourceSmoothWeight Y A r n = 0
  · simp [normalizedTypeISourceDirichletCoeff, typeISourceDirichletCoeff, hw]
  · have hn := typeISourceSmoothWeight_support hw
    have hnPos : 0 < n := by exact_mod_cast (lt_of_le_of_lt
      (by positivity : (0 : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2)) hn.1)
    have hWeight := typeISourceSmoothWeight_nat_mem_unitInterval Y A r n
    rw [normalizedTypeISourceDirichletCoeff, typeISourceDirichletCoeff,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hWeight.1,
      Complex.norm_natCast_cpow_of_pos hnPos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by exact_mod_cast hnPos.le), ← div_eq_mul_inv]
    have hBaseNonneg : 0 ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) := by positivity
    have hnNonneg : (0 : ℝ) ≤ n := by exact_mod_cast hnPos.le
    have hRearrange :
        ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) *
            (typeISourceSmoothWeight Y A r n / (n : ℝ) ^ σ) =
          typeISourceSmoothWeight Y A r n *
            (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) / (n : ℝ) ^ σ) := by
      ring
    rw [hRearrange]
    rw [← Real.div_rpow hBaseNonneg hnNonneg]
    have hRatio : (((2 ^ r * Y : ℕ) : ℝ) / 2) / n ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hnPos)]
      exact hn.1.le
    calc
      typeISourceSmoothWeight Y A r n *
          ((((2 ^ r * Y : ℕ) : ℝ) / 2) / n) ^ σ ≤
        1 * 1 := by
          exact mul_le_mul hWeight.2
            (Real.rpow_le_one (by positivity) hRatio hσ)
            (Real.rpow_nonneg (by positivity) _) zero_le_one
      _ = 1 := by ring

/-- A source-smooth block is exactly one finite wide Dirichlet polynomial.
The two apparent endpoint discrepancies are genuine zero terms: the left
endpoint is killed by `typeITailBoundary`, and so is `A + 1`. -/
theorem typeISourceSmoothBlock_eq_wideDirichletPoly (σ t : ℝ) (hY : 1 ≤ Y) :
    typeISourceSmoothBlock Y A r σ t =
      wideDirichletPoly 1 (Nat.clog 2 (A + 1))
        (typeISourceDirichletCoeff Y A r σ) t := by
  classical
  pm_8402
  let term : ℕ → ℂ := fun n =>
    typeISourceDirichletCoeff Y A r σ n *
      (n : ℂ) ^ (-(t : ℂ) * I)
  have hSmall : Finset.Ioc 1 (A + 1) ⊆ Finset.Icc 1 (A + 1) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le,
      (Finset.mem_Ioc.mp hn).2⟩
  have hLeftZero : ∀ n ∈ Finset.Icc 1 (A + 1), n ∉ Finset.Ioc 1 (A + 1) →
      term n = 0 := by
    intro n hn hnSmall
    have hnOne : n = 1 := by
      pm_5938 Finset.mem_Icc.mp hnSmall
    subst n
    have hnotTail : 1 ∉ Finset.Ioc Y A := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inl (by omega)
    simp only [term, typeISourceDirichletCoeff, typeISourceSmoothWeight,
      typeITailBoundary_natCast, ite_eq_right hnotTail, Nat.cast_one, zero_mul,
      Complex.ofReal_zero]
  have hSource :
      (∑ n ∈ Finset.Icc 1 (A + 1), term n) =
        ∑ n ∈ Finset.Ioc 1 (A + 1), term n := by
    symm
    exact Finset.sum_subset hSmall hLeftZero
  have hCover : A + 1 ≤ 2 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by omega) (A + 1)
  have hTailSubset : Finset.Ioc 1 (A + 1) ⊆ Finset.Ioc 1 (2 ^ k) := by
    pm_5250 n hn
  have hRightZero : ∀ n ∈ Finset.Ioc 1 (2 ^ k),
      n ∉ Finset.Ioc 1 (A + 1) → term n = 0 := by
    intro n hn hnSmall
    have hnAbove : A + 1 < n := by
      pm_5938 Finset.mem_Ioc.mp hnSmall
    have hnotTail : n ∉ Finset.Ioc Y A := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inr (by omega)
    simp only [term, typeISourceDirichletCoeff, typeISourceSmoothWeight,
      typeITailBoundary_natCast, ite_eq_right hnotTail, zero_mul,
      Complex.ofReal_zero]
  have hWide :
      (∑ n ∈ Finset.Ioc 1 (2 ^ k), term n) =
        ∑ n ∈ Finset.Ioc 1 (A + 1), term n := by
    symm
    exact Finset.sum_subset hTailSubset hRightZero
  unfold typeISourceSmoothBlock wideDirichletPoly
  simp only [mul_one]
  change (∑ n ∈ Finset.Icc 1 (A + 1), term n) =
    ∑ n ∈ Finset.Ioc 1 (2 ^ k), term n
  rw [hSource, hWide]

/-- Normalizing the source coefficients scales the complete source block by
the same positive real scalar. -/
theorem wideDirichletPoly_normalizedTypeISourceDirichletCoeff (σ t : ℝ) (hY : 1 ≤ Y) :
    wideDirichletPoly 1 (Nat.clog 2 (A + 1))
        (normalizedTypeISourceDirichletCoeff Y A r σ) t =
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ : ℝ) : ℂ) *
        typeISourceSmoothBlock Y A r σ t := by
  rw [typeISourceSmoothBlock_eq_wideDirichletPoly Y A r σ t hY]
  pm_315 wideDirichletPoly normalizedTypeISourceDirichletCoeff Finset.mul_sum Finset.sum_congr n _hn
  ring
end

/-- A large actual source-smooth block yields one common nonzero dyadic
block with unit-bounded coefficients.  The selected dyadic length remains
within a factor four of the physical source scale; these inequalities are
proved from the literal support of the source coefficient rather than
postulated as a scale certificate. -/
theorem extract_normalized_source_dyadic_block
    {Y A r : ℕ} {σ V : ℝ} (W : Finset ℝ)
    (hY : 0 < Y) (hA : 1 < A) (hV : 0 < V)
    (hW : W.Nonempty) (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) :
    let k := Nat.clog 2 (A + 1)
    ∃ j ∈ Finset.range k, ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
      (∀ t ∈ W',
        (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) / k ≤
          ‖dirichletPoly (2 ^ j)
            (normalizedTypeISourceDirichletCoeff Y A r σ) t‖) ∧
      2 ^ j < 2 * (2 ^ r * Y) ∧
      2 ^ r * Y < 4 * 2 ^ j := by
  dsimp only
  pm_8402
  have hk : 0 < k := by
    dsimp only [k]
    apply Nat.clog_pos Nat.one_lt_two
    omega
  pm_1123
  have hScalePos : 0 < ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) := by
    apply Real.rpow_pos_of_pos
    positivity
  have hWide : ∀ t ∈ W,
      ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V ≤
        ‖wideDirichletPoly 1 k
          (normalizedTypeISourceDirichletCoeff Y A r σ) t‖ := by
    intro t ht
    rw [wideDirichletPoly_normalizedTypeISourceDirichletCoeff
      Y A r σ t hY]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hScalePos]
    exact mul_le_mul_of_nonneg_left (hLarge t ht) hScalePos.le
  obtain ⟨j, hj, W', hWsub, hCard, hLarge'⟩ :=
    exists_dyadic_block_and_subset 1 k
      (normalizedTypeISourceDirichletCoeff Y A r σ) W
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) hk hWide
  simp only [mul_one] at hLarge'
  have hSep' : IsSeparated 1 W' := by
    pm_203 hSeparated hWsub
  have hW' : W'.Nonempty := by
    by_contra hnot
    have hCardZero : W'.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hnot)
    rw [hCardZero, Nat.cast_zero, mul_zero] at hCard
    pm_74 hWCardPos W.card hW.card_pos
    linarith
  obtain ⟨t, ht⟩ := hW'
  have hThresholdPos : 0 <
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) / k := by
    positivity
  have hPolyNe : dirichletPoly (2 ^ j)
      (normalizedTypeISourceDirichletCoeff Y A r σ) t ≠ 0 := by
    intro hzero
    have hAt := hLarge' t ht
    rw [hzero, norm_zero] at hAt
    linarith
  unfold dirichletPoly at hPolyNe
  obtain ⟨n, hn, hnTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hPolyNe
  have hnCoeff : normalizedTypeISourceDirichletCoeff Y A r σ n ≠ 0 := by
    intro hzero
    apply hnTerm
    simp [hzero]
  have hnWeight : typeISourceSmoothWeight Y A r n ≠ 0 := by
    intro hzero
    apply hnCoeff
    simp [normalizedTypeISourceDirichletCoeff,
      typeISourceDirichletCoeff, hzero]
  have hnSource := typeISourceSmoothWeight_support hnWeight
  have hnDyadic := Finset.mem_Ioc.mp hn
  have hLeftReal : ((2 ^ j : ℕ) : ℝ) <
      2 * (2 ^ r * Y : ℕ) := by
    have hPn : ((2 ^ j : ℕ) : ℝ) < n := by exact_mod_cast hnDyadic.1
    exact hPn.trans hnSource.2
  have hRightReal : ((2 ^ r * Y : ℕ) : ℝ) <
      4 * (2 ^ j : ℕ) := by
    have hnUpper : (n : ℝ) ≤ 2 * (2 ^ j : ℕ) := by exact_mod_cast hnDyadic.2
    nlinarith [hnSource.1]
  refine ⟨j, hj, W', hWsub, hSep', hCard, ?_, ?_, ?_⟩
  · simpa only [k] using hLarge'
  · exact_mod_cast hLeftReal
  · exact_mod_cast hRightReal

/-- A dyadic interval extracted within a fixed factor of a physical source
scale inherits a uniform logarithmic-scale upper bound.  The factor four is
absorbed by the elementary inequality `4P ≤ P²` once the source scale is at
least sixteen. -/
theorem extracted_source_logarithmic_scale_upper
    {T U : ℝ} {Q P : ℕ}
    (hT : 1 ≤ T) (hU : 0 < U) (hQ : 16 ≤ Q)
    (hQP : Q < 4 * P)
    (hScale : typeILogarithmicScale T Q ≤ U) :
    1 < P ∧ typeILogarithmicScale T P ≤ 2 * U := by
  have hPFour : 4 ≤ P := by omega
  pm_6310
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPhysicalQ : T ≤ (Q : ℝ) ^ U :=
    (Real.logb_le_iff_le_rpow (by exact_mod_cast hQOne) hTPos).mp hScale
  have hQP2Nat : Q ≤ P ^ 2 := by
    calc
      Q ≤ 4 * P := hQP.le
      _ ≤ P * P := Nat.mul_le_mul_right P hPFour
      _ = P ^ 2 := by ring
  have hRaised : (Q : ℝ) ^ U ≤ ((P ^ 2 : ℕ) : ℝ) ^ U :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQP2Nat) hU.le
  have hPower : ((P ^ 2 : ℕ) : ℝ) ^ U = (P : ℝ) ^ (2 * U) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  pm_5568 Real.logb_le_iff_le_rpow hTPos
  calc
    T ≤ (Q : ℝ) ^ U := hPhysicalQ
    _ ≤ ((P ^ 2 : ℕ) : ℝ) ^ U := hRaised
    _ = (P : ℝ) ^ (2 * U) := hPower

/-- The same extracted dyadic interval inherits half of every nonnegative
lower logarithmic-scale bound.  The exact factor-two upper comparison
`P < 2Q` is absorbed by `2Q ≤ Q²`; no asymptotic replacement of either
finite length is used. -/
theorem extracted_source_logarithmic_scale_lower
    {T L : ℝ} {Q P : ℕ}
    (hT : 0 < T) (hL : 0 ≤ L) (hQ : 4 ≤ Q)
    (hQP : Q < 4 * P) (hPQ : P < 2 * Q)
    (hScale : L ≤ typeILogarithmicScale T Q) :
    1 < P ∧ L / 2 ≤ typeILogarithmicScale T P := by
  pm_6310
  have hPhysicalQ : (Q : ℝ) ^ L ≤ T :=
    (Real.le_logb_iff_rpow_le (by exact_mod_cast hQOne) hT).mp hScale
  have hPQSquareNat : P ≤ Q ^ 2 := by
    calc
      P ≤ 2 * Q := hPQ.le
      _ ≤ Q * Q := Nat.mul_le_mul_right Q (by omega : 2 ≤ Q)
      _ = Q ^ 2 := by ring
  have hRaised : (P : ℝ) ^ (L / 2) ≤ ((Q ^ 2 : ℕ) : ℝ) ^ (L / 2) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hPQSquareNat)
      (by positivity)
  have hPower : ((Q ^ 2 : ℕ) : ℝ) ^ (L / 2) = (Q : ℝ) ^ L := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  pm_5568 Real.le_logb_iff_rpow_le hT
  exact hRaised.trans_eq hPower |>.trans hPhysicalQ

/-- A dyadic interval within a factor two above its physical source scale
has logarithmic scale within any prescribed positive additive error once
the height is large enough.  This is the quantitative finite bridge needed
to choose the natural power from the extracted polynomial rather than from
an unrelated real surrogate. -/
theorem eventually_extracted_source_logarithmic_scale_lower_additive
    {δ U : ℝ} (hδ : 0 < δ) (hU : 0 < U) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T τ : ℝ} {Q P : ℕ}, T₀ ≤ T → 1 < Q → 1 < P →
        P < 2 * Q → τ = typeILogarithmicScale T Q →
        0 < τ → τ ≤ U →
        τ - δ ≤ typeILogarithmicScale T P := by
  let X : ℝ := U ^ 2 * Real.log 2 / δ
  let T₀ : ℝ := max 8 (Real.exp X)
  pm_4889
  intro T τ Q P hT hQ hP hPQ hτ hτPos hτUpper
  pm_4629
  have hTExp : Real.exp X ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTOne : 1 < T := by linarith
  have hLogT : 0 < Real.log T := Real.log_pos hTOne
  pm_1456 hLogQ Q hQ
  pm_1456 hLogP P hP
  pm_7446 hLogTwo
  have hXLog : X ≤ Real.log T := by
    have hLogMono := Real.log_le_log (Real.exp_pos X) hTExp
    simpa only [Real.log_exp] using hLogMono
  have hTauLog : τ * Real.log (Q : ℝ) = Real.log T := by
    rw [hτ]
    unfold typeILogarithmicScale Real.logb
    field_simp [hLogQ.ne']
  have hLogPUpper : Real.log (P : ℝ) ≤
      Real.log 2 + Real.log (Q : ℝ) := by
    have hCast : (P : ℝ) ≤ 2 * Q := by exact_mod_cast hPQ.le
    calc
      Real.log (P : ℝ) ≤ Real.log (2 * (Q : ℝ)) :=
        Real.log_le_log (by positivity) hCast
      _ = Real.log 2 + Real.log (Q : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
  have hULog : U * Real.log 2 ≤ δ * Real.log (Q : ℝ) := by
    have hULogQ : Real.log T ≤ U * Real.log (Q : ℝ) := by
      rw [← hTauLog]
      exact mul_le_mul_of_nonneg_right hτUpper hLogQ.le
    have hCore : U ^ 2 * Real.log 2 / δ ≤
        U * Real.log (Q : ℝ) := by
      simpa only [X] using hXLog.trans hULogQ
    rw [div_le_iff₀ hδ] at hCore
    have hUPos : 0 < U := hU
    nlinarith [mul_pos hUPos hLogTwo]
  have hTauLogTwo : τ * Real.log 2 ≤ δ * Real.log (Q : ℝ) :=
    (mul_le_mul_of_nonneg_right hτUpper hLogTwo.le).trans hULog
  rw [hτ]
  unfold typeILogarithmicScale Real.logb
  rw [le_div_iff₀ hLogP]
  by_cases hNonneg : 0 ≤ Real.log T / Real.log (Q : ℝ) - δ
  · calc
      (Real.log T / Real.log (Q : ℝ) - δ) * Real.log (P : ℝ) ≤
          (Real.log T / Real.log (Q : ℝ) - δ) *
            (Real.log 2 + Real.log (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left hLogPUpper hNonneg
      _ ≤ Real.log T := by
        rw [show Real.log T / Real.log (Q : ℝ) = τ by
          rw [hτ]; rfl]
        rw [← hTauLog]
        nlinarith
  · have hNeg : Real.log T / Real.log (Q : ℝ) - δ < 0 :=
      lt_of_not_ge hNonneg
    exact (mul_neg_of_neg_of_pos hNeg hLogP).le.trans hLogT.le

/-! ## Powered reflected-family bridge -/

/-- The zero-real-part convention used by the generic powering theorem is
definitionally the ordinary Dirichlet phase after the elementary complex
ring normalization. -/
theorem sum_zero_real_part_eq_dirichletPoly
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * (t : ℂ)))) =
      dirichletPoly N a t := by
  pm_8145 dirichletPoly n _hn
  norm_num
  ring

/-- A unit-coefficient dyadic polynomial cannot have norm larger than its
literal natural length.  This converts a retained reflected threshold into
a lower bound for the actual block selected by dyadic pigeonholing. -/
theorem unit_coeff_threshold_le_dyadic_length
    {N : ℕ} {V : ℝ} {W : Finset ℝ} {a : ℕ → ℂ}
    (hV : 0 ≤ V) (hW : W.Nonempty)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    V ≤ (N : ℝ) := by
  have hEnergy := dyadic_energy_le_length N a ha
  have hThreshold := threshold_sq_le_length_mul_energy N V W a hV hW hLarge
  pm_1199 hN N
  nlinarith [sq_nonneg (V - (N : ℝ))]

/-! ## Finite interval Abel bridges for the source boundary -/

/-- Abel summation for a nonnegative increasing weight.  Unlike the
antitone form used for `n^-sigma`, the endpoint and total variation each
cost one copy of the final weight. -/
theorem norm_weighted_sum_le_of_monotone
    (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hN : 0 < N)
    (hf : ∀ i, i < N → 0 ≤ f i)
    (hmono : ∀ i, i + 1 < N → f i ≤ f (i + 1))
    (hpartial : ∀ j, j ≤ N → ‖∑ i ∈ Finset.range j, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ ≤ 2 * f (N - 1) * B := by
  have hB : 0 ≤ B := by
    simpa using hpartial 0 (Nat.zero_le N)
  have hparts := Finset.sum_Ico_by_parts f g hN
  rw [Finset.range_eq_Ico]
  calc
    ‖∑ i ∈ Finset.Ico 0 N, f i • g i‖ =
        ‖f (N - 1) • (∑ i ∈ Finset.range N, g i) -
          f 0 • (∑ i ∈ Finset.range 0, g i) -
          ∑ i ∈ Finset.Ico 0 (N - 1),
            (f (i + 1) - f i) •
              (∑ j ∈ Finset.range (i + 1), g j)‖ :=
      congrArg norm hparts
    _ = ‖(f (N - 1) : ℂ) * (∑ i ∈ Finset.range N, g i) -
        ∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := by
      simp only [Finset.sum_range_zero, Complex.real_smul, mul_zero, sub_zero]
    _ ≤ ‖(f (N - 1) : ℂ) * (∑ i ∈ Finset.range N, g i)‖ +
        ‖∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sub_le _ _
    _ ≤ f (N - 1) * B +
        ∑ i ∈ Finset.Ico 0 (N - 1), (f (i + 1) - f i) * B := by
      apply add_le_add
      · rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hf (N - 1) (by omega))]
        exact mul_le_mul_of_nonneg_left (hpartial N le_rfl)
          (hf (N - 1) (by omega))
      · calc
          ‖∑ i ∈ Finset.Ico 0 (N - 1),
              ((f (i + 1) - f i : ℝ) : ℂ) *
                (∑ j ∈ Finset.range (i + 1), g j)‖ ≤
              ∑ i ∈ Finset.Ico 0 (N - 1),
                ‖((f (i + 1) - f i : ℝ) : ℂ) *
                  (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Ico 0 (N - 1),
              (f (i + 1) - f i) * B := by
            pm_5926 abs_of_nonneg sub_nonneg.mpr hmono
            pm_5614 hmono
    _ = (2 * f (N - 1) - f 0) * B := by
      have htel : ∑ i ∈ Finset.Ico 0 (N - 1),
          (f (i + 1) - f i) = f (N - 1) - f 0 := by
        rw [Nat.Ico_zero_eq_range, Finset.sum_range_sub]
      rw [← Finset.sum_mul, htel]
      ring
    _ ≤ 2 * f (N - 1) * B := by
      have hf0 : 0 ≤ f 0 := hf 0 hN
      nlinarith

/-- Exact range form of one dyadic block of the normalized reflected
polynomial.  The `min` records the literal truncation at the natural dual
cutoff `M`; no coefficient beyond that cutoff is retained. -/
theorem dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    (sigma t : ℝ) (P M : ℕ) (hP : 0 < P) (hPM : P < M) :
    dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t =
      ∑ i ∈ Finset.range (min P (M - P)),
        (((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) •
          unitaryPhase (logarithmicPhase t (P + 1 + i)) := by
  have hInterval : Finset.Ioc P (2 * P) =
      Finset.Ico (P + 1) (2 * P + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  unfold dirichletPoly dyadicInterval
  rw [hInterval, Finset.sum_Ico_eq_sum_range]
  pm_4641 hLength P
  push_cast
  symm
  calc
    ∑ i ∈ Finset.range (min P (M - P)),
        (((P : ℝ) + 1 + (i : ℝ)) ^ sigma / (M : ℝ) ^ sigma) •
          unitaryPhase (logarithmicPhase t (P + 1 + i)) =
      ∑ i ∈ Finset.range (min P (M - P)),
        normalizedTypeIReflectedCoeff sigma M (P + 1 + i) *
          ((P : ℂ) + 1 + (i : ℂ)) ^ (-t * I) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiL : i < min P (M - P) := Finset.mem_range.mp hi
      have hiDiff : i < M - P := lt_of_lt_of_le hiL (min_le_right _ _)
      pm_8165 hnPos P i
      have hnM : P + 1 + i ≤ M := by omega
      rw [normalizedTypeIReflectedCoeff, ite_eq_left ⟨by omega, hnM⟩,
        Complex.real_smul]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hPhase :=
        unitaryPhase_logarithmicPhase_eq_cpow t (P + 1 + i) hnPos
      norm_num only [Nat.cast_add, Nat.cast_one] at hPhase
      rw [hPhase]
    _ = ∑ i ∈ Finset.range P,
        normalizedTypeIReflectedCoeff sigma M (P + 1 + i) *
          ((P : ℂ) + 1 + (i : ℂ)) ^ (-t * I) := by
      apply Finset.sum_subset
      · intro i hi
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp hi).trans_le (min_le_left _ _))
      · intro i hiP hiL
        have hiP' : i < P := Finset.mem_range.mp hiP
        have hiLower : min P (M - P) ≤ i := by
          exact le_of_not_gt (fun h => hiL (Finset.mem_range.mpr h))
        have hMin : min P (M - P) = M - P := by
          apply min_eq_right
          omega
        have hnM : M < P + 1 + i := by
          rw [hMin] at hiLower
          omega
        rw [normalizedTypeIReflectedCoeff,
          ite_eq_right (fun h => (Nat.not_le_of_lt hnM) h.2), zero_mul]

/-- Boundary-slack version of the weighted reflected Weyl estimate.  The
factor `X` is retained explicitly through the A--B process, so the natural
dual cutoff may differ from its ideal real scale by a proved power loss. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl_with_slack
    (sigma t X : ℝ) (P M : ℕ)
    (hsigma : 0 ≤ sigma) (hP : 0 < P) (hPM : P < M)
    (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (htP : t ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ ≤
      60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
        Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
  pm_880
  let L : ℕ := min P (M - P)
  let f : ℕ → ℝ := fun i =>
    ((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma
  let g : ℕ → ℂ := fun i =>
    unitaryPhase (logarithmicPhase t (P + 1 + i))
  pm_4688
  pm_4689 P htP
  have hLPos : 0 < L := by
    dsimp only [L]
    exact lt_min hP (Nat.sub_pos_of_lt hPM)
  have hLUpper : L ≤ P + 1 := by
    dsimp only [L]
    exact (min_le_left _ _).trans (Nat.le_succ _)
  have hPartial : ∀ j, j ≤ L →
      ‖∑ i ∈ Finset.range j, g i‖ ≤
        30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix_with_slack
      Y X (P + 1) j hYOne hX (by omega) hYUpper
      (by simpa only [hYcube] using hPt) (hj.trans hLUpper)
    rw [logarithmicSum_eq_sum_range] at hWeyl
    norm_num only [Nat.cast_add, Nat.cast_one] at hWeyl
    pm_354 hYcube hWeyl Nat.cast_add Nat.cast_one
  have hFNonneg : ∀ i, i < L → 0 ≤ f i := by
    intro i _hi
    dsimp only [f]
    positivity
  have hFMono : ∀ i, i + 1 < L → f i ≤ f (i + 1) := by
    intro i _hi
    pm_6762
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast (show P + 1 + i ≤ P + 1 + (i + 1) by omega)
    · exact hsigma
  have hAbel := norm_weighted_sum_le_of_monotone f g L
    (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y))
    hLPos hFNonneg hFMono hPartial
  have hLastTwo : P + 1 + (L - 1) ≤ 2 * (P + 1) := by
    have hLP : L ≤ P := min_le_left _ _
    omega
  have hFLast : f (L - 1) ≤
      (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) := by
    pm_6762
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLastTwo) hsigma
  rw [dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    sigma t P M hP hPM]
  change ‖∑ i ∈ Finset.range L, f i • g i‖ ≤ _
  calc
    ‖∑ i ∈ Finset.range L, f i • g i‖ ≤
        2 * f (L - 1) *
          (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y)) := hAbel
    _ ≤ 2 * ((((2 * (P + 1) : ℕ) : ℝ) ^ sigma /
          (M : ℝ) ^ sigma)) *
          (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y)) := by
      gcongr
    _ = 60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
        Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [Y]
      ring

/-- Physical-scale form of the reflected Weyl estimate.  The exact scale
identity eliminates the dyadic length, while the harmless factor `4^sigma`
accounts for the sharp endpoint and normalization. -/
theorem norm_normalizedTypeIReflectedCoeff_le_physical_weyl
    {sigma d T theta w : ℝ} {P M : ℕ}
    (hsigma : 0 ≤ sigma) (hd : 0 ≤ d) (hT : 1 ≤ T)
    (hP : 1 < P) (hPM : P < M)
    (htheta : 0 < theta) (hScale : (P : ℝ) ^ theta = T)
    (hwOne : 1 ≤ w) (hwUpper : w ≤ 3 * T)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      (2 * T ^ (4 * d)) * w)
    (htP : w ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ ≤
      (60 * 4 ^ sigma * Real.sqrt 12) *
        T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  pm_4728 hPReal P hP
  have hMPos : (0 : ℝ) < M := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (lt_trans hP hPM))
  have hXOne : (1 : ℝ) ≤ 2 * T ^ (4 * d) := by
    pm_6094
    nlinarith
  have hRaw := norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl_with_slack
    sigma w (2 * T ^ (4 * d)) P M hsigma (by omega) hPM hwOne hXOne hPt htP
  have hRatio :
      (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) ≤
        4 ^ sigma := by
    have hPMCast : (((2 * (P + 1) : ℕ) : ℝ)) ≤ 4 * (M : ℝ) := by
      exact_mod_cast (show 2 * (P + 1) ≤ 4 * M by omega)
    have hPow := Real.rpow_le_rpow (by positivity) hPMCast hsigma
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hMPos.le] at hPow
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hMPos sigma)).2 (by
      simpa only [mul_assoc] using hPow)
  have hPEq : (P : ℝ) = T ^ (1 / theta) :=
    calc
      (P : ℝ) = ((P : ℝ) ^ theta) ^ (1 / theta) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ P)]
        field_simp [htheta.ne']
        exact (Real.rpow_one _).symm
      _ = T ^ (1 / theta) := by rw [hScale]
  have hPSucc : ((P + 1 : ℕ) : ℝ) ≤ 2 * T ^ (1 / theta) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [← hPEq]
    nlinarith [hPReal.le]
  have hwThird : w ^ (1 / 3 : ℝ) ≤ 3 * T ^ (1 / 3 : ℝ) := by
    pm_5927 hRpow w hwUpper
    calc
      w ^ (1 / 3 : ℝ) ≤ (3 * T) ^ (1 / 3 : ℝ) := hRpow
      _ = 3 ^ (1 / 3 : ℝ) * T ^ (1 / 3 : ℝ) := by
        pm_1232 hTPos.le
      _ ≤ 3 * T ^ (1 / 3 : ℝ) := by
        pm_4690
  have hInside :
      (2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) * w ^ (1 / 3 : ℝ) ≤
        12 * T ^ (4 * d + 1 / theta + 1 / 3) := by
    calc
      (2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) * w ^ (1 / 3 : ℝ) ≤
          (2 * T ^ (4 * d)) * (2 * T ^ (1 / theta)) *
            (3 * T ^ (1 / 3 : ℝ)) := by gcongr
      _ = 12 * T ^ (4 * d + 1 / theta + 1 / 3) := by
        rw [Real.rpow_add hTPos, Real.rpow_add hTPos]
        ring
  have hSqrt := Real.sqrt_le_sqrt hInside
  have hSqrtRewrite :
      Real.sqrt (12 * T ^ (4 * d + 1 / theta + 1 / 3)) =
        Real.sqrt 12 * T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTPos.le]
    congr 1
    field_simp [htheta.ne']
    ring
  calc
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ ≤
        60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
          Real.sqrt ((2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) *
            w ^ (1 / 3 : ℝ)) := hRaw
    _ ≤ 60 * 4 ^ sigma *
          Real.sqrt (12 * T ^ (4 * d + 1 / theta + 1 / 3)) := by gcongr
    _ = (60 * 4 ^ sigma * Real.sqrt 12) *
          T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
      rw [hSqrtRewrite]
      ring

/-- The normalized reflected coefficients are real, hence fixed by the
coefficientwise conjugation used to reverse the sign of an ordinate. -/
theorem conjugateCoeffs_normalizedTypeIReflectedCoeff
    (sigma : ℝ) (M : ℕ) :
    conjugateCoeffs (normalizedTypeIReflectedCoeff sigma M) =
      normalizedTypeIReflectedCoeff sigma M := by
  funext n
  unfold conjugateCoeffs normalizedTypeIReflectedCoeff
  split_ifs <;> simp

/-- Reversing the ordinate preserves the norm of a normalized reflected
block.  This is the exact bridge for the negative Poisson half. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_neg
    (sigma t : ℝ) (P M : ℕ) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t)‖ =
      ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ := by
  have hSource :
      sourceDirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t =
        dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t) := by
    unfold sourceDirichletPoly dirichletPoly
    pm_8456 n _hn
  calc
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t)‖ =
        ‖sourceDirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ :=
      congrArg norm hSource.symm
    _ = ‖sourceDirichletPoly P
          (conjugateCoeffs (normalizedTypeIReflectedCoeff sigma M)) t‖ := by
      rw [conjugateCoeffs_normalizedTypeIReflectedCoeff]
    _ = ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ :=
      norm_sourceDirichletPoly_conjugateCoeffs _ _ _

/-- The translated negative Poisson block has the norm of the same real
coefficient block at the positive reflected ordinate `3T-v`. -/
theorem norm_phaseShifted_normalized_reflected_eq
    (sigma T v : ℝ) (P M : ℕ) :
    ‖dirichletPoly P
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M)) v‖ =
      ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (3 * T - v)‖ := by
  rw [← dirichletPoly_translate]
  convert norm_dirichletPoly_normalizedTypeIReflectedCoeff_neg
    sigma (3 * T - v) P M using 2
  all_goals ring_nf

/-- One cancellation-safe interface for the two retained Poisson signs.
The coefficient sequence is existential because the negative sign carries
the fixed translation by `-3T`, whereas the positive sign does not.  The
last field identifies its norm with the same normalized reflected block at
an actual positive ordinate in `[T/2,5T/2]`; this is the bridge needed by
the Weyl alternative after the finite sign and displacement selections. -/
theorem extract_common_signed_reflected_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hsigma : 0 ≤ sigma) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      ∃ a : ℕ → ℂ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
        W.card ≤ 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
          (Nat.clog 2 M) * U.card ∧
        (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
        (∀ v ∈ U, S / Nat.clog 2 M ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly (2 ^ j) a v‖ =
            ‖dirichletPoly (2 ^ j)
              (normalizedTypeIReflectedCoeff sigma M) w‖) := by
  rcases select_common_signed_reflected_family W hEach with
    ⟨Wsign, hWsign, hSignCard, hNegative⟩ |
      ⟨Wsign, hWsign, hSignCard, hPositive⟩
  · have hSepSign : IsSeparated 1 Wsign := by
      pm_203 hSeparated hWsign
    pm_4692
    pm_5755 extract_common_reflected_mhh_block hNegative
    let a : ℕ → ℂ := phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M)
    pm_4691
    · intro n hn
      dsimp only [a]
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨3 * T - v, ?_, ?_⟩
      · rw [Set.mem_Icc]
        have hvRange := hURange v hv
        constructor <;> linarith
      · dsimp only [a]
        exact norm_phaseShifted_normalized_reflected_eq sigma T v (2 ^ j) M
  · have hSepSign : IsSeparated 1 Wsign := by
      pm_203 hSeparated hWsign
    pm_4692
    pm_5755 extract_common_positive_reflected_mhh_block hPositive
    let a : ℕ → ℂ := normalizedTypeIReflectedCoeff sigma M
    pm_4691
    · intro n hn
      dsimp only [a]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨v, hURange v hv, ?_⟩
      rfl

/-- Abel summation on a literal natural interval.  This is the interval
counterpart of `norm_weighted_sum_le_of_antitone`; keeping the endpoints in
the statement avoids replacing a terminal source block by a prefix beginning
at one. -/
theorem norm_weighted_Ioc_le_of_antitone
    (f : ℕ → ℝ) (g : ℕ → ℂ) (L U : ℕ) (B : ℝ)
    (hLU : L < U)
    (hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n)
    (hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n)
    (hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ ≤ f (L + 1) * B := by
  have hLen : 0 < U - L := Nat.sub_pos_of_lt hLU
  let F : ℕ → ℝ := fun i => f (L + 1 + i)
  let G : ℕ → ℂ := fun i => g (L + 1 + i)
  have hF : ∀ i, i < U - L → 0 ≤ F i := by
    intro i hi
    exact hf _ (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
  have hAntiF : ∀ i, i + 1 < U - L → F (i + 1) ≤ F i := by
    intro i hi
    simpa only [F, Nat.add_assoc] using
      hanti (L + 1 + i) (by omega) (by omega)
  have hBound := norm_weighted_sum_le_of_antitone F G (U - L) B
    hLen hF hAntiF (by
      intro j hj
      simpa only [G] using hpartial j hj)
  have hIoc : Finset.Ioc L U = Finset.Ico (L + 1) (U + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : U + 1 - (L + 1) = U - L := by omega
  rw [hLength]
  pm_99 F G Nat.cast_add Nat.cast_one hBound

/-- The fixed smooth step used by the Type-I partition is decreasing. -/
theorem antitone_typeISmoothStep : Antitone typeISmoothStep := by
  intro x y hxy
  unfold typeISmoothStep
  exact Real.smoothTransition.monotone (by linarith)

theorem typeISmoothStep_nonneg (x : ℝ) : 0 ≤ typeISmoothStep x := by
  unfold typeISmoothStep
  exact Real.smoothTransition.nonneg _

theorem typeISmoothStep_le_one (x : ℝ) : typeISmoothStep x ≤ 1 := by
  unfold typeISmoothStep
  exact Real.smoothTransition.le_one _

theorem typeIDyadicCutoff_eq_one_sub_step_of_le
    {x : ℝ} (hx : x ≤ 1) :
    typeIDyadicCutoff x = 1 - typeISmoothStep (2 * x) := by
  rw [typeIDyadicCutoff, typeISmoothStep_eq_one hx]

theorem typeIDyadicCutoff_eq_step_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    typeIDyadicCutoff x = typeISmoothStep x := by
  have hzero : typeISmoothStep (2 * x) = 0 :=
    typeISmoothStep_eq_zero (by linarith)
  rw [typeIDyadicCutoff, hzero]
  ring

/-- Real-power deweighting of one source term into the unitary logarithmic
phase used by all finite Abel estimates. -/
theorem source_weighted_cpow_eq_smul_phase
    (w σ t : ℝ) {n : ℕ} (hn : 0 < n) :
    (w : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) *
        (n : ℂ) ^ (-(t : ℂ) * I) =
      (w * (n : ℝ) ^ (-σ)) •
        unitaryPhase (logarithmicPhase t n) := by
  rw [Complex.real_smul,
    unitaryPhase_logarithmicPhase_eq_cpow t n hn]
  pm_8019 Complex.ofReal_mul
  push_cast
  ring

/-- A decreasing smooth cutoff can be inserted into the Abel-summed
second-derivative estimate without changing its square-root majorant. -/
theorem norm_smoothStep_weighted_Ioc_le_sqrt
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (hLt : (L : ℝ) ≤ t) (htL : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  pm_4695
  pm_4147
  pm_4696
  pm_4693
  pm_4697
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (100 * Real.sqrt t) hLU hf hanti hpartial
  pm_4694
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) * (100 * Real.sqrt t) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by norm_num

/-- Weyl A--B-process companion to the preceding smooth-weight Abel bound.
It applies to the exact monotone cutoff occurring in a classified source
block and retains the physical ordinate `t`. -/
theorem norm_smoothStep_weighted_Ioc_le_weyl
    (X c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hSquare : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (hCube : t ≤ (((L + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
  pm_4695
  pm_880
  pm_4688
  pm_4689 L hCube
  pm_4147
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    dsimp only [f]
    exact mul_nonneg (typeISmoothStep_nonneg _)
      (Real.rpow_nonneg (by positivity) _)
  pm_4693
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤
        30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix_with_slack
      Y X (L + 1) j hYOne hX (by omega) hYUpper
      (by simpa only [hYcube] using hSquare)
      (hj.trans hLength |>.trans (Nat.le_succ L))
    rw [logarithmicSum_eq_sum_range] at hWeyl
    rw [hYcube] at hWeyl
    pm_99 Nat.cast_add Nat.cast_one Nat.add_assoc add_assoc hWeyl
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) hLU hf hanti hpartial
  pm_4694
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
      rfl

/-- Uncut specialization of the smooth Weyl estimate, used for the middle
term in the exact three-sum source expansion. -/
theorem norm_plain_weighted_Ioc_le_weyl
    (X σ t : ℝ) (L U : ℕ)
    (hσ : 0 ≤ σ) (hL : 0 < L) (hLU : L < U)
    (hLength : U - L ≤ L) (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hSquare : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (hCube : t ≤ (((L + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
  have h := norm_smoothStep_weighted_Ioc_le_weyl
    X 0 σ t 1 L U (by norm_num) hσ (by omega) hL hLU hLength
      htOne hX hSquare hCube
  have hEq :
      (∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (0 * (n : ℝ) / 1) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (0 : ℝ) * (n : ℝ) / 1 = 0 by ring,
      typeISmoothStep_eq_one (by norm_num : (0 : ℝ) ≤ 1), one_mul]
  rw [hEq]
  simpa only [Nat.cast_one] using h

/-- Exact three-sum form of a source block whose upper tail boundary meets
the sharp cutoff.  The rising half of the annular cutoff is written as the
difference of two decreasing weights, and the falling half is already a
decreasing smooth step. -/
theorem typeISourceSmoothBlock_eq_terminal_three_sums
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y)
    (hLower : 2 * (Y + 1) ≤ 2 ^ r * Y) :
    let Q := 2 ^ r * Y
    typeISourceSmoothBlock Y A r σ t =
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) := by
  dsimp only
  pm_4897 Q r Y
  pm_4187
  have hYHalf : Y ≤ Q / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
    omega
  have hYQ : Y ≤ Q := hYHalf.trans (Nat.div_le_self Q 2)
  have hLowerSubset : Finset.Ioc (Q / 2) (min Q A) ⊆
      Finset.Ioc Y (min Q A) := by
    intro n hn
    have hndata := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hYHalf.trans_lt hndata.1, hndata.2⟩
  have hRestricted :
      (∑ n ∈ Finset.Ioc Y (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    pm_8028 hLowerSubset
    have hnHalf : n ≤ Q / 2 := by
      by_contra hnot
      exact hnSmall (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnot, hnData.2⟩)
    have hRatio : (n : ℝ) / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ)]
      have hnTwice : 2 * n ≤ Q :=
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hnHalf
      have hnTwiceReal : (2 : ℝ) * n ≤ Q := by exact_mod_cast hnTwice
      nlinarith
    rw [typeIDyadicCutoff_eq_zero_of_le_half hRatio, zero_mul, zero_smul]
  have hLowerExpand :
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : n ≤ Q :=
      (Finset.mem_Ioc.mp hn).2.trans (min_le_left Q A)
    have hRatio : (n : ℝ) / Q ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hQ)]
      exact_mod_cast hnQ
    rw [typeIDyadicCutoff_eq_one_sub_step_of_le hRatio]
    rw [sub_mul, one_mul, sub_smul]
    simp only [mul_div_assoc]
  have hUpperExpand :
      (∑ n ∈ Finset.Ioc Q A,
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : Q < n := (Finset.mem_Ioc.mp hn).1
    have hRatio : 1 ≤ (n : ℝ) / Q := by
      rw [le_div_iff₀ (by exact_mod_cast hQ)]
      norm_num
      exact_mod_cast hnQ.le
    rw [typeIDyadicCutoff_eq_step_of_one_le hRatio]
  rw [typeISourceSmoothBlock_eq_restricted]
  have hCpow :
      (∑ n ∈ Finset.Ioc Y A,
        (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
          (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc Y A,
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact source_weighted_cpow_eq_smul_phase _ σ t
      (lt_trans hY (Finset.mem_Ioc.mp hn).1)
  change (∑ n ∈ Finset.Ioc Y A,
      (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)) = _
  rw [hCpow]
  by_cases hQA : Q ≤ A
  · have hUnion : Finset.Ioc Y Q ∪ Finset.Ioc Q A = Finset.Ioc Y A :=
      Finset.Ioc_union_Ioc_eq_Ioc hYQ hQA
    have hDisjoint : Disjoint (Finset.Ioc Y Q) (Finset.Ioc Q A) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [← hUnion, Finset.sum_union hDisjoint]
    have hMin : min Q A = Q := min_eq_left hQA
    rw [hMin] at hRestricted hLowerExpand
    rw [hRestricted, hLowerExpand, hUpperExpand]
    rw [min_eq_left hQA]
  · have hAQ : A < Q := lt_of_not_ge hQA
    have hMin : min Q A = A := min_eq_right hAQ.le
    have hUpperEmpty : Finset.Ioc Q A = ∅ := by
      ext n
      simp
      omega
    rw [hMin] at hRestricted hLowerExpand
    rw [hRestricted, hLowerExpand]
    rw [hMin]
    rw [hUpperEmpty, Finset.sum_empty, add_zero]

/-- The coefficient-one member of the three-sum terminal decomposition obeys
the same interval Abel bound as its smooth companions. -/
theorem norm_plain_weighted_Ioc_le_sqrt
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hLU : L < U) (hL : 0 < L)
    (hLength : U - L ≤ L) (hLt : (L : ℝ) ≤ t)
    (htL : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  pm_4698
  pm_4697
  simpa only [f, g, Nat.cast_add, Nat.cast_one] using
    norm_weighted_Ioc_le_of_antitone f g L U
      (100 * Real.sqrt t) hLU hf hanti hpartial

/-- First-derivative companion to `norm_smoothStep_weighted_Ioc_le_sqrt`.
It covers a terminal interval beginning to the right of the ordinate. -/
theorem norm_smoothStep_weighted_Ioc_le_div
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htL : t ≤ (L : ℝ)) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by
  pm_4695
  pm_4147
  pm_4696
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    have hnPos : 0 < n := lt_trans hL hnL
    have harg : c * (n : ℝ) / Q ≤ c * ((n + 1 : ℕ) : ℝ) / Q := by
      apply div_le_div_of_nonneg_right _ hQReal.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc
    have hstep := antitone_typeISmoothStep harg
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) := by
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hnPos)
        (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr hσ)
    dsimp only [f]
    exact mul_le_mul hstep hpow (Real.rpow_nonneg (by positivity) _)
      (typeISmoothStep_nonneg _)
  pm_4699
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (6 * Real.pi * (L : ℝ) / t) hLU hf hanti hpartial
  pm_4694
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) * (6 * Real.pi * (L : ℝ) / t) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (6 * Real.pi * (L : ℝ) / t) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by norm_num

/-- First-derivative terminal estimate for the coefficient-one member of the
three-sum source decomposition. -/
theorem norm_plain_weighted_Ioc_le_div
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hLU : L < U) (hL : 0 < L)
    (hLength : U - L ≤ L) (htOne : 1 ≤ t)
    (htL : t ≤ (L : ℝ)) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by
  pm_4698
  pm_4699
  simpa only [f, g, Nat.cast_add, Nat.cast_one] using
    norm_weighted_Ioc_le_of_antitone f g L U
      (6 * Real.pi * (L : ℝ) / t) hLU hf hanti hpartial

/-- Uniform interval estimate obtained by routing at the physical comparison
`t ≤ L`.  Keeping both nonnegative majorants makes the later terminal source
assembly independent of that case split. -/
theorem norm_plain_weighted_Ioc_le_sqrt_add_div
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hL : 0 < L) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htSq : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) *
        (100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t) := by
  by_cases hLU : L < U
  · by_cases htL : t ≤ (L : ℝ)
    · exact (norm_plain_weighted_Ioc_le_div hσ hLU hL hLength htOne htL).trans
        (by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
          nlinarith [Real.sqrt_nonneg t])
    · exact (norm_plain_weighted_Ioc_le_sqrt hσ hLU hL hLength
          (le_of_not_ge htL) htSq).trans (by
            pm_4700
            linarith)
  pm_1315

/-- Smooth-cutoff counterpart of
`norm_plain_weighted_Ioc_le_sqrt_add_div`. -/
theorem norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htSq : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) *
        (100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t) := by
  by_cases hLU : L < U
  · by_cases htL : t ≤ (L : ℝ)
    · exact (norm_smoothStep_weighted_Ioc_le_div c σ t Q L U hc hσ hQ
          hL hLU hLength htOne htL).trans (by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
            nlinarith [Real.sqrt_nonneg t])
    · exact (norm_smoothStep_weighted_Ioc_le_sqrt c σ t Q L U hc hσ hQ
          hL hLU hLength (le_of_not_ge htL) htSq).trans
        (by
          pm_4700
          linarith)
  pm_1315

/-- Quantitative elimination bound for a classified upper-edge source block.
The proof uses the exact three-sum identity above and controls all three
pieces without extending the sharp cutoff. -/
theorem norm_typeISourceSmoothBlock_terminal_le
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hTerminal : A < 2 * (2 ^ r * Y))
    (hσ : 0 ≤ σ) (htOne : 1 ≤ t)
    (htSq : t ≤ (((2 ^ r * Y) / 2 : ℕ) : ℝ) ^ 2) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t +
          6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
  pm_4704
  have hpowFour : 4 ≤ 2 ^ r := by
    pm_4703
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    have hYOne : 1 ≤ Y := hY
    pm_5584 hYOne hpowFour
  have hQ : 0 < Q := by omega
  pm_4647 hL L
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left (by
      exact dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  pm_4705
  have hLower : 2 * (Y + 1) ≤ Q := by
    calc
      2 * (Y + 1) ≤ 4 * Y := by omega
      _ ≤ Q := by
        dsimp only [Q]
        exact Nat.mul_le_mul_right Y hpowFour
  have hLowerLength : min Q A - L ≤ L := by omega
  have hUpperLength : A - Q ≤ Q := by omega
  have htSqQ : t ≤ (Q : ℝ) ^ 2 := by
    pm_6311
    have hSq : (L : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 := by nlinarith
    exact htSq.trans hSq
  pm_5706
  pm_4165
  pm_4706
  pm_6652 A
  pm_4702
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
    by
      pm_996 hPlain.trans
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
    by
      pm_996 hRise.trans
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    calc
      _ ≤ ((Q + 1 : ℕ) : ℝ) ^ (-σ) * B := by
        pm_99 B Nat.cast_add Nat.cast_one one_mul hFall
      _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
        mul_le_mul_of_nonneg_right hWeight hB
  pm_4701
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      pm_4707
    _ ≤ (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) +
        (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) +
        (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) := by linarith
    _ = 3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
      dsimp only [L, Q, B]
      ring

/-- The falling smooth half of a source block stops exactly at `2Q`, even
when the ambient sharp cutoff is larger. -/
theorem source_upper_smooth_sum_eq_min_two_mul
    (Q A : ℕ) (hQ : 0 < Q) (σ t : ℝ) :
    (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc Q (min (2 * Q) A),
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
  have hSub : Finset.Ioc Q (min (2 * Q) A) ⊆ Finset.Ioc Q A := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans (min_le_right _ _)⟩
  pm_8028 hSub
  have hnTwo : 2 * Q ≤ n := by
    by_contra hnot
    have hnLt : n < 2 * Q := lt_of_not_ge hnot
    exact hnSmall (Finset.mem_Ioc.mpr
      ⟨hnData.1, le_min hnLt.le hnData.2⟩)
  have hRatio : 2 ≤ (n : ℝ) / Q := by
    rw [le_div_iff₀ (by exact_mod_cast hQ)]
    exact_mod_cast hnTwo
  rw [typeISmoothStep_eq_zero hRatio, zero_mul, zero_smul]

section
variable {Y A r : ℕ} {σ t : ℝ} (hY : 0 < Y) (hr : 2 ≤ r)
include Y A r σ t hY hr
/-- Uniform square-root cancellation bound for every classified source
block, with no upper-edge assumption.  The proof uses the exact support at
`2Q`; consequently the ambient sharp cutoff never appears in an interval
length estimate. -/
theorem norm_typeISourceSmoothBlock_le_sqrt (hσ : 0 ≤ σ)
    (htOne : 1 ≤ t)
    (htSq : t ≤ (((2 ^ r * Y) / 2 : ℕ) : ℝ) ^ 2) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t +
          6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
  pm_4704
  pm_7861
  pm_4708
  have htSqQ : t ≤ (Q : ℝ) ^ 2 := by
    pm_6311
    exact htSq.trans (by nlinarith)
  pm_5706
  pm_4165
  pm_4706
  pm_6652 U
  pm_4702
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    pm_6418 hPlain.trans
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    pm_6418 hRise.trans
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    rw [source_upper_smooth_sum_eq_min_two_mul Q A hQ σ t]
    calc
      _ ≤ ((Q + 1 : ℕ) : ℝ) ^ (-σ) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
        pm_99 U Nat.cast_add Nat.cast_one one_mul hFall
      _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
        mul_le_mul_of_nonneg_right hWeight hB
  pm_4701
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      pm_4707
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B +
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B +
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by linarith
    _ = 3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
      dsimp only [L, Q, B]
      ring

/-- Uniform Weyl bound for a complete source-smooth block in the physical
range `Q^2 \lesssim t \lesssim Q^3`.  This theorem consumes the exact
three-sum expansion of the source block, including both smooth boundary
pieces, rather than replacing it by a coefficient-free model. -/
theorem norm_typeISourceSmoothBlock_le_weyl
    (hInterior : 2 * (2 ^ r * Y) ≤ A) (hσ : 0 ≤ σ)
    (htOne : 1 ≤ t)
    (hSquare : ((((2 ^ r * Y) + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t)
    (hCube : t ≤ ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      90 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        Real.sqrt (8 * (((2 ^ r * Y + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
  pm_4704
  pm_7861
  let R : ℝ := Real.sqrt (8 * ((Q + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))
  pm_4708
  have hLQ : L + 1 ≤ Q + 1 := by omega
  have hLQReal : (((L + 1 : ℕ) : ℝ)) ≤ (((Q + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hLQ
  have hSquareL : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    exact (pow_le_pow_left₀ (by positivity) hLQReal 2).trans
      (by simpa only [Q] using hSquare)
  have hSquareQ : (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    simpa only [Q] using hSquare
  have hCubeQ : t ≤ (((Q + 1 : ℕ) : ℝ) ^ (3 : ℕ)) :=
    hCube.trans (pow_le_pow_left₀ (by positivity) hLQReal 3)
  have hPlain := norm_plain_weighted_Ioc_le_weyl
    8 σ t L (min Q A) hσ hL (by omega) hLowerLength htOne
      (by norm_num) hSquareL
      (by simpa only [L, Q] using hCube)
  have hRise := norm_smoothStep_weighted_Ioc_le_weyl
    8 2 σ t Q L (min Q A) (by norm_num) hσ hQ hL (by omega)
      hLowerLength htOne (by norm_num) hSquareL
      (by simpa only [L, Q] using hCube)
  have hFall := norm_smoothStep_weighted_Ioc_le_weyl
    8 1 σ t Q Q U (by norm_num) hσ hQ hQ (by omega)
      hUpperLength htOne (by norm_num) hSquareQ hCubeQ
  have hRoot :
      Real.sqrt (8 * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) ≤ R := by
    dsimp only [R]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLQReal (by norm_num))
      (Real.rpow_nonneg (by positivity) _)
  have hWeight : (((Q + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      (((L + 1 : ℕ) : ℝ)) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast hLQ
    · linarith
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    pm_6419 hPlain.trans
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    pm_6419 hRise.trans
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    rw [source_upper_smooth_sum_eq_min_two_mul Q A hQ σ t]
    calc
      _ ≤ (((Q + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
        simpa only [U, R, one_mul] using hFall
      _ ≤ (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
        exact mul_le_mul_of_nonneg_right hWeight (by positivity)
  pm_4701
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      pm_4707
    _ ≤ (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) +
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) +
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by linarith
    _ = 90 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        Real.sqrt (8 * (((2 ^ r * Y + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [L, Q, R]
      ring
end

/-- Physical form of the preceding source-block Weyl estimate.  The source
length is kept as the actual natural `Q = 2^r Y`, and the identity
`Q^tau = T` is used only at the final exponent conversion. -/
theorem norm_typeISourceSmoothBlock_le_physical_weyl
    {Y A r : ℕ} {σ T t tau : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hInterior : 2 * (2 ^ r * Y) ≤ A)
    (hσ : 0 ≤ σ) (hσUpper : σ ≤ 1)
    (hT : 1 ≤ T) (htOne : 1 ≤ t) (htUpper : t ≤ 3 * T)
    (htau : 0 < tau)
    (hScale : (((2 ^ r * Y : ℕ) : ℝ)) ^ tau = T)
    (hSquare : ((((2 ^ r * Y) + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t)
    (hCube : t ≤ ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      (180 * Real.sqrt 48) *
        T ^ ((1 / 2 - σ) / tau + 1 / 6) := by
  pm_4897 Q r Y
  have hQFour : 4 ≤ Q := by
    have hPow : 4 ≤ 2 ^ r := by
      pm_4703
    pm_1381
  pm_4711
  pm_308 hQOne Q
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  pm_4709
  pm_4710
  have hHalfPos : (0 : ℝ) < Q / 2 := by positivity
  have hWeight : (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      2 * (Q : ℝ) ^ (-σ) := by
    have hHalfLe : (Q : ℝ) / 2 ≤ ((Q / 2 + 1 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one, hHalfCast]
      linarith
    have hAnti : (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤
        ((Q : ℝ) / 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hHalfPos hHalfLe (neg_nonpos.mpr hσ)
    have hTwoPow : (2 : ℝ) ^ σ ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hσUpper
    calc
      (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤ ((Q : ℝ) / 2) ^ (-σ) := by
        simpa only [hHalfCast] using hAnti
      _ = (2 : ℝ) ^ σ * (Q : ℝ) ^ (-σ) := by
        rw [Real.div_rpow hQPos.le (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.rpow_neg (by norm_num : (2 : ℝ) ≥ 0)]
        field_simp [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) σ]
      _ ≤ 2 * (Q : ℝ) ^ (-σ) := by gcongr
  pm_1512 hQSucc
  have htThird : t ^ (1 / 3 : ℝ) ≤ 3 * T ^ (1 / 3 : ℝ) := by
    pm_5927 hPow t htUpper
    calc
      t ^ (1 / 3 : ℝ) ≤ (3 * T) ^ (1 / 3 : ℝ) := hPow
      _ = 3 ^ (1 / 3 : ℝ) * T ^ (1 / 3 : ℝ) := by
        pm_1232 hTPos.le
      _ ≤ 3 * T ^ (1 / 3 : ℝ) := by
        pm_4690
  have hInside : 8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ) ≤
      48 * (Q : ℝ) * T ^ (1 / 3 : ℝ) := by
    calc
      8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ) ≤
          8 * (2 * (Q : ℝ)) * (3 * T ^ (1 / 3 : ℝ)) := by gcongr
      _ = 48 * (Q : ℝ) * T ^ (1 / 3 : ℝ) := by ring
  have hSqrt := Real.sqrt_le_sqrt hInside
  have hSqrtRewrite :
      Real.sqrt (48 * (Q : ℝ) * T ^ (1 / 3 : ℝ)) =
        Real.sqrt 48 * (Q : ℝ) ^ (1 / 2 : ℝ) * T ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 48 * (Q : ℝ)),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 48)]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    congr 1
    rw [← Real.rpow_mul hTPos.le]
    congr 1
    ring
  have hQPower : (Q : ℝ) ^ (1 / 2 - σ) =
      T ^ ((1 / 2 - σ) / tau) := by
    rw [← hScale, ← Real.rpow_mul hQPos.le]
    congr 1
    field_simp [htau.ne']
  have hRaw := norm_typeISourceSmoothBlock_le_weyl
    hY hr hInterior hσ htOne hSquare hCube
  calc
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
        90 * (((Q / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
          Real.sqrt (8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
      simpa only [Q] using hRaw
    _ ≤ 90 * (2 * (Q : ℝ) ^ (-σ)) *
          Real.sqrt (48 * (Q : ℝ) * T ^ (1 / 3 : ℝ)) := by gcongr
    _ = (180 * Real.sqrt 48) *
          (((Q : ℝ) ^ (-σ) * (Q : ℝ) ^ (1 / 2 : ℝ)) *
            T ^ (1 / 6 : ℝ)) := by
      rw [hSqrtRewrite]
      ring
    _ = (180 * Real.sqrt 48) *
          ((Q : ℝ) ^ (1 / 2 - σ) * T ^ (1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hQPos]
      congr 3
      ring
    _ = (180 * Real.sqrt 48) *
          T ^ ((1 / 2 - σ) / tau + 1 / 6) := by
      rw [hQPower, Real.rpow_add hTPos]

/-- Uniform physical side conditions for the complete source-block Weyl
estimate.  The factor eight in the quadratic condition is exactly what
absorbs the left displacement of the slab at the boundary `tau = 2`; the
cubic condition uses the fixed positive gap between `tauMax` and `3`. -/
theorem eventually_source_weyl_geometry
    {d tauMax : ℝ} (hTauMaxTwo : 2 ≤ tauMax)
    (hTauMaxThree : tauMax < 3) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T t tau : ℝ} {Q : ℕ}, T₀ ≤ T → 1 < Q → 2 ∣ Q →
        2 ≤ tau → tau ≤ tauMax → (Q : ℝ) ^ tau = T →
        T ^ d ≤ T / 2 → T - T ^ d ≤ t → t ≤ 2 * T + T ^ d →
        (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t ∧
          t ≤ ((((Q / 2) + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
  let rho : ℝ := 3 / tauMax - 1
  have hTauMaxPos : 0 < tauMax := by linarith
  have hRho : 0 < rho := by
    dsimp only [rho]
    rw [sub_pos, one_lt_div hTauMaxPos]
    exact hTauMaxThree
  have hTop := tendsto_rpow_atTop hRho
  have hEventually := (tendsto_atTop.1 hTop) 24
  pm_4712
  let T₀ := max 8 Tpow
  pm_4889
  intro T t tau Q hT hQ hEven hTauTwo hTauUpper hScale hDisp htLower htUpper
  pm_4629
  pm_4713
  pm_4169
  have hTauPos : 0 < tau := by linarith
  pm_4711
  pm_4739
  pm_1082 htHalf htThree
  have hQSquare : (Q : ℝ) ^ (2 : ℕ) ≤ T := by
    calc
      (Q : ℝ) ^ (2 : ℕ) = (Q : ℝ) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (Q : ℝ) 2).symm
      _ ≤ (Q : ℝ) ^ tau :=
        Real.rpow_le_rpow_of_exponent_le hQOne hTauTwo
      _ = T := hScale
  pm_1512 hSucc
  have hQuadratic : (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    calc
      (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ (2 * (Q : ℝ)) ^ (2 : ℕ) := by
        gcongr
      _ = 4 * (Q : ℝ) ^ (2 : ℕ) := by ring
      _ ≤ 4 * T := by gcongr
      _ ≤ 8 * t := by linarith
  have hInv : 3 / tauMax ≤ 3 / tau := by
    exact div_le_div_of_nonneg_left (by norm_num) hTauPos hTauUpper
  have hExp : rho ≤ (3 - tau) / tau := by
    dsimp only [rho]
    rw [sub_div]
    field_simp [hTauPos.ne']
    nlinarith [hInv]
  have hPowerSaving : 24 ≤ (Q : ℝ) ^ (3 - tau) := by
    calc
      (24 : ℝ) ≤ T ^ rho := hTpow T hTPow
      _ ≤ T ^ ((3 - tau) / tau) :=
        Real.rpow_le_rpow_of_exponent_le hTOne hExp
      _ = (Q : ℝ) ^ (3 - tau) := by
        rw [← hScale, ← Real.rpow_mul hQPos.le]
        congr 1
        field_simp [hTauPos.ne']
  have hQCube : 24 * T ≤ (Q : ℝ) ^ (3 : ℕ) := by
    calc
      24 * T = 24 * (Q : ℝ) ^ tau := by rw [hScale]
      _ ≤ (Q : ℝ) ^ (3 - tau) * (Q : ℝ) ^ tau := by
        exact mul_le_mul_of_nonneg_right hPowerSaving
          (Real.rpow_nonneg hQPos.le _)
      _ = (Q : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_add hQPos]
        convert Real.rpow_natCast (Q : ℝ) 3 using 1
        all_goals ring_nf
  pm_4710
  refine ⟨hQuadratic, ?_⟩
  calc
    t ≤ 3 * T := htThree
    _ ≤ ((Q : ℝ) / 2) ^ (3 : ℕ) := by
      rw [show ((Q : ℝ) / 2) ^ (3 : ℕ) = (Q : ℝ) ^ (3 : ℕ) / 8 by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith
    _ = ((Q / 2 : ℕ) : ℝ) ^ (3 : ℕ) := by rw [hHalfCast]
    _ ≤ (((Q / 2 + 1 : ℕ) : ℝ)) ^ (3 : ℕ) := by
      gcongr
      norm_num

/-- The complementary physical source-scale alternative is empty.  This
consumes a nonempty source family and its actual pointwise lower bound; the
`Nat.clog` loss is supplied explicitly and absorbed by the displayed
positive exponent budget. -/
theorem eventually_source_far_family_impossible
    {sigma d u q v Clog : ℝ}
    (hsigmaUpper : sigma < 1)
    (hq : 0 < q) (hTauMaxTwo : 2 ≤ 6 * sigma - 3 - q)
    (hBudget : u + v < q / 18) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        tau = typeILogarithmicScale T (2 ^ r * Y) →
        2 ≤ tau → tau < 6 * sigma - 3 - q →
        T ^ d ≤ T / 2 →
        W.Nonempty →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤ Clog * T ^ v) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r sigma t‖) →
        False := by
  let tauMax : ℝ := 6 * sigma - 3 - q
  have hTauMaxTwo' : 2 ≤ tauMax := by simpa only [tauMax] using hTauMaxTwo
  have hTauMaxThree : tauMax < 3 := by dsimp only [tauMax]; linarith
  pm_4081 Tgeo hTgeo hGeo eventually_source_weyl_geometry hTauMaxTwo' hTauMaxThree
  have hSaving : 0 < q / 18 - u - v := by linarith
  let Cw : ℝ := 180 * Real.sqrt 48
  pm_116 hCw Cw
  have hTop := tendsto_rpow_atTop hSaving
  have hEventually := (tendsto_atTop.1 hTop)
    ((8 / 3 : ℝ) * Clog * Cw + 1)
  pm_4610 eventually_atTop hEventually Tconst hTconst
  let T₀ : ℝ := max Tgeo Tconst
  pm_4266 T₀ hTgeo.trans le_max_left
  intro T tau Y A r W hT hA hY hr hInterior hTau hTauTwo hFar hDisp
    hW hRange hLog hLarge
  pm_4630 hTGeo Tgeo le_max_left hT
  have hTEight : 8 ≤ T := hTgeo.trans hTGeo
  pm_4630 hTConst Tconst le_max_right hT
  pm_4169
  have hTauPos : 0 < tau := by linarith
  pm_4046 hTauUpper tau tauMax
  obtain ⟨t, ht⟩ := hW
  pm_4897 Q r Y
  have hQFour : 4 ≤ Q := by
    have hPow : 4 ≤ 2 ^ r := by
      pm_4703
    pm_1381
  have hQOne : 1 < Q := by omega
  pm_4709
  pm_4714
  have htLower : T / 2 ≤ t := by linarith [(hRange t ht).1]
  have htOne : 1 ≤ t := by linarith
  have htUpper : t ≤ 3 * T := by linarith [(hRange t ht).2]
  obtain ⟨hSquare, hCube⟩ := hGeo hTGeo hQOne hEven hTauTwo
    hTauUpper hScale hDisp (hRange t ht).1 (hRange t ht).2
  have hWeyl := norm_typeISourceSmoothBlock_le_physical_weyl
    hY hr hInterior (by linarith : 0 ≤ sigma) hsigmaUpper.le hTOne
    htOne htUpper hTauPos hScale hSquare hCube
  let F : ℝ := (1 / 2 - sigma) / tau + 1 / 6
  have hExp : F ≤ -q / 18 := by
    have hCore : F < -q / (6 * tau) := by
      dsimp only [F]
      rw [lt_div_iff₀ (mul_pos (by norm_num) hTauPos)]
      field_simp [hTauPos.ne']
      linarith
    have hUniform : -q / (6 * tau) ≤ -q / 18 := by
      have hDiv : q / 18 ≤ q / (6 * tau) := by
        exact div_le_div_of_nonneg_left hq.le (by positivity) (by linarith)
      simpa only [neg_div] using (neg_le_neg hDiv)
    exact hCore.le.trans hUniform
  have hPow : T ^ F ≤ T ^ (-q / 18) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExp
  have hNorm : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      Cw * T ^ (-q / 18) := by
    exact hWeyl.trans (mul_le_mul_of_nonneg_left
      (by simpa only [F] using hPow) hCw.le)
  have hLogPos : (0 : ℝ) < ((Nat.clog 2 A + 1 : ℕ) : ℝ) := by positivity
  have hLower : (3 / 4 : ℝ) * (T ^ (-u) / 2) ≤
      ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
        ‖typeISourceSmoothBlock Y A r sigma t‖ := by
    simpa only [mul_comm] using (div_le_iff₀ hLogPos).mp (hLarge t ht)
  have hLogNonneg : 0 ≤ Clog * T ^ v := hLogPos.le.trans hLog
  have hThreshold : (3 / 8 : ℝ) * T ^ (-u) ≤
      (Clog * Cw) * T ^ (v - q / 18) := by
    calc
      (3 / 8 : ℝ) * T ^ (-u) =
          (3 / 4) * (T ^ (-u) / 2) := by ring
      _ ≤ ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
          ‖typeISourceSmoothBlock Y A r sigma t‖ := hLower
      _ ≤ (Clog * T ^ v) * (Cw * T ^ (-q / 18)) := by
        exact mul_le_mul hLog hNorm (norm_nonneg _) hLogNonneg
      _ = (Clog * Cw) * (T ^ v * T ^ (-q / 18)) := by ring
      _ = (Clog * Cw) * T ^ (v - q / 18) := by
        rw [← Real.rpow_add hTPos]
        ring_nf
  have hConstRaw := hTconst T hTConst
  change (8 / 3 : ℝ) * Clog * Cw + 1 ≤
    T ^ (q / 18 - u - v) at hConstRaw
  have hConst : (8 / 3 : ℝ) * Clog * Cw <
      T ^ (q / 18 - u - v) := (lt_add_one _).trans_le hConstRaw
  have hScaled := mul_lt_mul_of_pos_right hConst
    (Real.rpow_pos_of_pos hTPos (v - q / 18))
  have hIdentity : T ^ (q / 18 - u - v) * T ^ (v - q / 18) =
      T ^ (-u) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hContradiction : (Clog * Cw) * T ^ (v - q / 18) <
      (3 / 8 : ℝ) * T ^ (-u) := by
    calc
      (Clog * Cw) * T ^ (v - q / 18) =
          (3 / 8 : ℝ) * (((8 / 3 : ℝ) * Clog * Cw) *
            T ^ (v - q / 18)) := by ring
      _ < (3 / 8 : ℝ) *
          (T ^ (q / 18 - u - v) * T ^ (v - q / 18)) := by
        exact mul_lt_mul_of_pos_left hScaled (by norm_num)
      _ = (3 / 8 : ℝ) * T ^ (-u) := by rw [hIdentity]
  linarith

set_option maxHeartbeats 1200000

/-- A genuinely large interior source block must lie on the stationary side
of the B-process margin.  This is proved from the sharp-support square-root
bound above; the margin is not added as a hypothesis to the final consumer. -/
theorem eventually_large_source_forces_complementary_margin
    {σ d u : ℝ} (hσOne : σ < 1)
    (hd : 0 < d) (hdOne : d < 1)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T t τ : ℝ) (Y A r : ℕ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        T - T ^ d ≤ t → t ≤ 2 * T + T ^ d →
        T ^ d ≤ T / 2 →
        τ = typeILogarithmicScale T (2 ^ r * Y) →
        ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : ℕ) ≤
          ‖typeISourceSmoothBlock Y A r σ t‖ →
        -100 * d ≤ τ / 2 - σ := by
  pm_1221 σ
  have haOne : 1 < a := by
    dsimp only [a]
    have hScaled : 200 * d ≤ (σ - 1 / 2) / 5 := by
      calc
        200 * d ≤ 200 * ((σ - 1 / 2) / 1000) := by gcongr
        _ = (σ - 1 / 2) / 5 := by ring
    linarith
  have haPos : 0 < a := zero_lt_one.trans haOne
  have haTwo : a < 2 := by dsimp only [a]; linarith
  let δ : ℝ := 2 / a - 1
  have hδ : 0 < δ := by
    dsimp only [δ]
    rw [sub_pos, one_lt_div haPos]
    exact haTwo
  have hPowTop := tendsto_rpow_atTop hδ
  have hEventuallyPow := (tendsto_atTop.1 hPowTop) 48
  pm_4610 eventually_atTop hEventuallyPow Tpow hTpow
  have hDecay : u + 1 / 2 < σ / a := by
    have hGapEq : σ / a - 1 / 2 = 100 * d / a := by
      field_simp [haPos.ne']
      dsimp only [a]
      ring
    have hFifty : 50 * d < 100 * d / a := by
      rw [lt_div_iff₀ haPos]
      have hMul := mul_lt_mul_of_pos_right haTwo
        (mul_pos (by norm_num : (0 : ℝ) < 50) hd)
      nlinarith
    have huFifty : u < 50 * d := huD.trans_lt (by nlinarith [hd])
    linarith
  have hRatioTop := tendsto_typeI_terminal_ratio (σ / a) (u + 1 / 2) hDecay
  let c : ℝ := 6 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ
  pm_116 hc c
  pm_6594 hRatioTop.const_mul hEventuallySmall
  pm_4610 eventually_atTop hEventuallySmall Tsmall hTsmall
  pm_98 Thalf hThalf hHalf eventually_rpow_le_half_self d hdOne
  let T₀ : ℝ := max 8 (max Tpow (max Tsmall Thalf))
  pm_4889
  intro T t τ Y A r hT hA hY hr hUpper htLower htUpper hDisp hτ hLarge
  pm_4629
  pm_5098 hRest Tpow Tsmall Thalf hT
  pm_4630 hTPow Tpow le_max_left hRest
  pm_4639 hRest₁ Tsmall Thalf hRest
  pm_4630 hTSmall Tsmall le_max_left hRest₁
  pm_4630 hTHalf Thalf le_max_right hRest₁
  pm_4185
  by_contra hMargin
  have hτa : τ < a := by
    have : τ / 2 - σ < -100 * d := lt_of_not_ge hMargin
    dsimp only [a]
    linarith
  pm_4704
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    have hpow : 4 ≤ 2 ^ r := by
      pm_4703
    pm_5584 hY hpow
  have hQOne : 1 < Q := by omega
  have hQ : 0 < Q := by omega
  pm_4709
  pm_4705
  have hL : 0 < L := by omega
  have hScale : (Q : ℝ) ^ τ = T := by
    subst τ
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hTa : T ≤ (Q : ℝ) ^ a := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hQOne.le) hτa.le
  have hRoot : T ^ (1 / a) ≤ (Q : ℝ) := by
    have hRaised := Real.rpow_le_rpow hTPos.le hTa
      (by positivity : 0 ≤ 1 / a)
    calc
      T ^ (1 / a) ≤ ((Q : ℝ) ^ a) ^ (1 / a) := hRaised
      _ = (Q : ℝ) := by
        pm_5879
  have hPowAt : 48 ≤ T ^ δ := hTpow T hTPow
  have hQSquare : 48 * T ≤ (Q : ℝ) ^ 2 := by
    have hSquare := pow_le_pow_left₀ (Real.rpow_nonneg hTPos.le _) hRoot 2
    have hPowerEq : (T ^ (1 / a)) ^ (2 : ℕ) = T ^ (2 / a) := by
      pm_336 Real.rpow_natCast Real.rpow_mul hTPos.le
    have hSplit : T ^ (2 / a) = T * T ^ δ := by
      rw [show 2 / a = 1 + δ by dsimp only [δ]; ring,
        Real.rpow_add hTPos, Real.rpow_one]
    rw [hPowerEq, hSplit] at hSquare
    nlinarith [mul_le_mul_of_nonneg_left hPowAt hTPos.le]
  pm_1082 htHalf htThree
  have htSq : t ≤ (L : ℝ) ^ 2 := by
    pm_4716
    rw [hLReal]
    nlinarith
  have hNorm := norm_typeISourceSmoothBlock_le_sqrt
    (Y := Y) (A := A) (r := r) (σ := σ) (t := t)
    hY hr (by linarith) (by linarith) (by simpa only [Q, L] using htSq)
  pm_1380
  pm_4715
  have hQUpper : (Q : ℝ) ≤ 3 * T := by
    have hUpperReal : (2 : ℝ) * Q ≤ A := by exact_mod_cast hUpper
    linarith
  have hSqrt : Real.sqrt t ≤ Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (3 * T) := Real.sqrt_le_sqrt htThree
      _ = Real.sqrt 3 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
        congr 1
        exact Real.sqrt_eq_rpow T
  have hRatio : (Q : ℝ) / t ≤ 6 := by
    have hQt : (Q : ℝ) ≤ 6 * t := by linarith only [hQUpper, htHalf]
    exact (div_le_iff₀ (by linarith only [htHalf, hTPos])).2 hQt
  have hSqrtOne : 1 ≤ T ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hTOne (by norm_num)
  have hBracket :
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
        (100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ) := by
    have hRatioTerm : 6 * Real.pi * (Q : ℝ) / t ≤ 36 * Real.pi := by
      calc
        6 * Real.pi * (Q : ℝ) / t = 6 * Real.pi * ((Q : ℝ) / t) := by ring
        _ ≤ 6 * Real.pi * 6 := by gcongr
        _ = 36 * Real.pi := by ring
    calc
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
          100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) + 36 * Real.pi := by
        gcongr
      _ ≤ 100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
          36 * Real.pi * T ^ (1 / 2 : ℝ) := by
        have hPiTerm : 36 * Real.pi ≤ 36 * Real.pi * T ^ (1 / 2 : ℝ) := by
          calc
            36 * Real.pi = 36 * Real.pi * 1 := by ring
            _ ≤ 36 * Real.pi * T ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left hSqrtOne (by positivity)
        exact add_le_add_right hPiTerm _
      _ = (100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ) := by ring
  have hWeightQ : (((L + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      ((Q : ℝ) / 2) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · norm_num only [Nat.cast_add, Nat.cast_one]
      pm_4716
      linarith
    · linarith
  have hWeightT : ((Q : ℝ) / 2) ^ (-σ) ≤
      2 ^ σ * T ^ (-σ / a) := by
    have hQNeg : (Q : ℝ) ^ (-σ) ≤ T ^ (-σ / a) := by
      have hRaised := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hTPos (1 / a))
        hRoot (by linarith : -σ ≤ 0)
      have hEq : (T ^ (1 / a)) ^ (-σ) = T ^ (-σ / a) := by
        rw [← Real.rpow_mul hTPos.le]
        congr 1
        ring
      simpa only [hEq] using hRaised
    rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ Q)
      (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (Q : ℝ) ^ (-σ) / (2 ^ σ)⁻¹ = 2 ^ σ * (Q : ℝ) ^ (-σ) := by
        field_simp
      _ ≤ 2 ^ σ * T ^ (-σ / a) :=
        mul_le_mul_of_nonneg_left hQNeg (Real.rpow_nonneg (by norm_num) _)
  have hNormBound : ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
        T ^ (1 / 2 - σ / a) := by
    calc
      _ ≤ 3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
        simpa only [Q, L, A] using hNorm
      _ ≤ 3 * (2 ^ σ * T ^ (-σ / a)) *
          ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ)) := by
        calc
          3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
              (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) =
            3 * ((((L + 1 : ℕ) : ℝ) ^ (-σ)) *
              (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t)) := by ring
          _ ≤ 3 * ((2 ^ σ * T ^ (-σ / a)) *
              ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ))) := by
            have hSourceBracketNonneg :
                0 ≤ 100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t := by
              have htPos : 0 < t := by linarith only [htHalf, hTPos]
              positivity
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (hWeightQ.trans hWeightT) hBracket
                hSourceBracketNonneg (by positivity)) (by norm_num)
          _ = _ := by ring
      _ = 3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ / a) := by
        calc
          3 * (2 ^ σ * T ^ (-σ / a)) *
              ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ)) =
            3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
              (T ^ (-σ / a) * T ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hTPos]
            congr 1
            ring_nf
  have hAOne : 1 < A := by
    dsimp only [A]
    pm_4735
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hkBound : ((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤
      2 * (1 + (Real.log 6 + Real.log T) / Real.log 2) := by
    have hEnvelopeOne : 1 ≤
        1 + (Real.log 6 + Real.log T) / Real.log 2 := by
      pm_4778
      pm_234 hLogSix
      have hLogT : 0 ≤ Real.log T := Real.log_nonneg hTOne
      have : 0 ≤ (Real.log 6 + Real.log T) / Real.log 2 :=
        div_nonneg (add_nonneg hLogSix hLogT) hLogTwo.le
      linarith
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hSmallAt :
      c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (u + 1 / 2 - σ / a) < 3 / 8 := by
    simpa only [mul_assoc] using hTsmall T hTSmall
  have hPowerSplit : T ^ (u + 1 / 2 - σ / a) * T ^ (-u) =
      T ^ (1 / 2 - σ / a) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    pm_5777 hSmallAt
    calc
      _ ≤ (2 * (1 + (Real.log 6 + Real.log T) / Real.log 2)) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) := by gcongr
      _ = (c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u + 1 / 2 - σ / a)) * T ^ (-u) := by
        rw [show T ^ (1 / 2 - σ / a) =
            T ^ (u + 1 / 2 - σ / a) * T ^ (-u) from hPowerSplit.symm]
        dsimp only [c]
        ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  have hkPos : (0 : ℝ) < (Nat.clog 2 A + 1 : ℕ) := by positivity
  have hThresholdLt : ‖typeISourceSmoothBlock Y A r σ t‖ <
      ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) := by
    rw [lt_div_iff₀ hkPos]
    calc
      ‖typeISourceSmoothBlock Y A r σ t‖ * (Nat.clog 2 A + 1 : ℕ) =
          (Nat.clog 2 A + 1 : ℕ) * ‖typeISourceSmoothBlock Y A r σ t‖ := by ring
      _ ≤ (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) :=
        mul_le_mul_of_nonneg_left hNormBound hkPos.le
      _ < _ := hNumerator
  exact (not_lt_of_ge (by simpa only [A] using hLarge)) hThresholdLt

/-- Budgeted form of the signed B-process extraction.  The choice of `R`
uses `L¹+1`, so it is valid even if the fixed Mellin mass vanishes; the
strict source gap and the normalization of the reflected polynomial are
then elementary consequences of `R ≥ 2`. -/
theorem exists_signed_shift_large_normalized_reflected_wide_of_budget
    {Y A r M : ℕ} {σ t V H K E : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hσ : 0 ≤ σ) (hM : 1 < M)
    (hV : 0 < V) (hH : 0 ≤ H) (hK : 0 < K)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖)
    (hZero :
      ‖typeISourceNormalizationScalar σ t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier σ t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar σ t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail σ t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernelNeg : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral σ (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hKernelPos : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral σ (-t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTailNeg :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial σ t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral σ (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailPos :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial σ (-t)
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral σ (-t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailBudget : E ≤ Real.pi * V / 8)
    (hR : 2 ≤ (Real.pi * V) /
      (8 * ((2 ^ r * Y : ℕ) : ℝ) * K *
        (typeIDyadicCutoffMellinL1 + 1))) :
    let R := (Real.pi * V) /
      (8 * ((2 ^ r * Y : ℕ) : ℝ) * K *
        (typeIDyadicCutoffMellinL1 + 1))
    let S := R / (2 * (M : ℝ) ^ σ)
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff σ M) (-(t + u))‖) ∨
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff σ M) (t - u)‖) := by
  dsimp only
  pm_4897 Q r Y
  let R : ℝ := (Real.pi * V) /
    (8 * (Q : ℝ) * K * (typeIDyadicCutoffMellinL1 + 1))
  let S : ℝ := R / (2 * (M : ℝ) ^ σ)
  pm_4187
  have hMass : 0 ≤ typeIDyadicCutoffMellinL1 :=
    typeIDyadicCutoffMellinL1_nonneg
  have hDen : 0 < 8 * (Q : ℝ) * K *
      (typeIDyadicCutoffMellinL1 + 1) := by positivity
  pm_116 hRPos R
  have hCentral : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 ≤
      Real.pi * V / 8 := by
    dsimp only [R]
    rw [div_eq_mul_inv]
    have hFrac : typeIDyadicCutoffMellinL1 /
        (typeIDyadicCutoffMellinL1 + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hQV : 0 ≤ Real.pi * V / 8 := by positivity
    field_simp [hDen.ne']
    nlinarith [mul_le_mul_of_nonneg_left hFrac (mul_nonneg Real.pi_pos.le hV.le)]
  have hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      Real.pi * V / 2 := by
    have hPiV : 0 < Real.pi * V := mul_pos Real.pi_pos hV
    nlinarith
  have hNormalize : S + (M : ℝ) ^ (-σ) ≤ R / (M : ℝ) ^ σ := by
    have hMPow : 0 < (M : ℝ) ^ σ := by positivity
    have hInv : (M : ℝ) ^ (-σ) = 1 / (M : ℝ) ^ σ := by
      simpa only [one_div] using
        (Real.rpow_neg (by positivity : (0 : ℝ) ≤ M) σ)
    have hRAt : 2 ≤ R := by simpa only [R, Q] using hR
    rw [hInv]
    dsimp only [S]
    have hRewrite : R / (2 * (M : ℝ) ^ σ) + 1 / (M : ℝ) ^ σ =
        (R / 2 + 1) / (M : ℝ) ^ σ := by
      field_simp [hMPow.ne']
    rw [hRewrite]
    exact (div_le_div_iff_of_pos_right hMPow).2 (by nlinarith)
  simpa only [Q, R, S] using
    exists_signed_shift_large_normalized_reflected_wide
      hY hLower hUpper hσ hM hV.le hH hRPos.le hLarge hZero hFar
      hKernelNeg hKernelPos hTailNeg hTailPos hGap hNormalize

/-- The terminal three-sum majorant is eventually smaller than the exact
classified-source threshold.  The statement keeps the additional `clog + 1`
selection loss, rather than silently identifying it with the detector's
original `clog`. -/
theorem eventually_terminal_source_majorant_lt_threshold
    {σ u : ℝ} (hσ : 1 / 2 < σ) (hu : u < σ - 1 / 2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (Q L : ℕ), T₀ ≤ T →
      T / 2 ≤ L → (Q : ℝ) ≤ 24 * T →
      T / 2 ≤ t → t ≤ 3 * T →
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) <
        ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) := by
  have hDecay : u + 1 / 2 < σ := by linarith
  have hTendsto := tendsto_typeI_terminal_ratio σ (u + 1 / 2) hDecay
  let c : ℝ := 6 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ
  pm_116 hc c
  pm_6594 hTendsto.const_mul hEventually
  pm_4635
  intro T t Q L hT hTL hQT htLower htUpper
  pm_4629
  pm_4636
  pm_72 hTPos T htPos t
  pm_8896 hLPos L
  have hWeight : (((L + 1 : ℕ) : ℝ)) ^ (-σ) ≤ (T / 2) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · norm_num only [Nat.cast_add, Nat.cast_one]
      linarith
    · linarith
  pm_4736
  have hRatio : (Q : ℝ) / t ≤ 48 := by
    rw [div_le_iff₀ htPos]
    nlinarith
  have hSqrtOne : 1 ≤ T ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hRatioTerm : 6 * Real.pi * (Q : ℝ) / t ≤ 6 * Real.pi * 48 := by
    calc
      6 * Real.pi * (Q : ℝ) / t = 6 * Real.pi * ((Q : ℝ) / t) := by ring
      _ ≤ 6 * Real.pi * 48 := mul_le_mul_of_nonneg_left hRatio
        (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hBracket :
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
        (100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ) := by
    calc
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
          100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
            6 * Real.pi * 48 := add_le_add (mul_le_mul_of_nonneg_left hSqrt
              (by norm_num)) hRatioTerm
      _ ≤ 100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
            (6 * Real.pi * 48) * T ^ (1 / 2 : ℝ) := by
        have hCoeff : 0 ≤ 6 * Real.pi * 48 := by positivity
        have hScaledRatio := mul_le_mul_of_nonneg_left hSqrtOne hCoeff
        have hRatioLift : 6 * Real.pi * 48 ≤
            (6 * Real.pi * 48) * T ^ (1 / 2 : ℝ) := by
          simpa only [mul_one] using hScaledRatio
        linarith
      _ = (100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ) := by ring
  have hDivPow : (T / 2) ^ (-σ) = 2 ^ σ * T ^ (-σ) := by
    pm_1355 hTPos.le
    field_simp
  have hPowCombine : T ^ (-σ) * T ^ (1 / 2 : ℝ) =
      T ^ (1 / 2 - σ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hMajorant :
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) ≤
        3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ) := by
    calc
      _ ≤ 3 * (T / 2) ^ (-σ) *
          ((100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ)) := by
        gcongr
      _ = 3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ) := by
        rw [hDivPow, ← hPowCombine]
        ring
  let A := ⌊sharpZetaCutoff T⌋₊
  have hAOne : 1 < A := by
    dsimp only [A]
    pm_4735
  have hkPos : 0 < (Nat.clog 2 A + 1 : ℕ) := by omega
  have hkRealPos : (0 : ℝ) < (Nat.clog 2 A + 1 : ℕ) := by exact_mod_cast hkPos
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hEnvelopeOne : 1 ≤
      1 + (Real.log 6 + Real.log T) / Real.log 2 := by
    pm_301 hLogT T
    pm_234 hLogSix
    pm_4778
    have hFrac : 0 ≤ (Real.log 6 + Real.log T) / Real.log 2 := by positivity
    linarith
  have hkBound : (Nat.clog 2 A + 1 : ℕ) ≤
      2 * (1 + (Real.log 6 + Real.log T) / Real.log 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hRatioAt := hTscale T hTscale'
  have hRatioSmall :
      c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (u + 1 / 2 - σ) < 3 / 8 := by
    simpa only [mul_assoc] using hRatioAt
  have hPowSplit : T ^ (u + 1 / 2 - σ) * T ^ (-u) =
      T ^ (1 / 2 - σ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    pm_5777 hRatioSmall
    calc
      (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) ≤
        (2 * (1 + (Real.log 6 + Real.log T) / Real.log 2)) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) := by gcongr
      _ = (c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u + 1 / 2 - σ)) * T ^ (-u) := by
        calc
          _ = c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
              T ^ (1 / 2 - σ) := by dsimp only [c]; ring
          _ = c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
              (T ^ (u + 1 / 2 - σ) * T ^ (-u)) := by rw [hPowSplit]
          _ = _ := by ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  change 3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
      (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) <
    ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ)
  rw [lt_div_iff₀ hkRealPos]
  exact (mul_le_mul_of_nonneg_right hMajorant (Nat.cast_nonneg _)).trans_lt
    (by simpa only [mul_comm] using hNumerator)

/-- The upper-edge alternative returned by the actual common-source
selection is empty for all sufficiently large heights.  Its scale comparison
is derived from a nonzero dyadic coefficient of that same source block. -/
theorem eventually_no_terminal_classified_source
    {σ d u : ℝ} (hσ : 1 / 2 < σ) (hu : u < σ - 1 / 2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T : ℝ) (Y A r : ℕ) (W : Finset ℝ), T₀ ≤ T →
      A = ⌊sharpZetaCutoff T⌋₊ →
      0 < Y → 2 ≤ r → A < 2 * (2 ^ r * Y) →
      W.Nonempty → IsSeparated 1 W →
      (∀ t ∈ W,
        ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) ≤
          ‖typeISourceSmoothBlock Y A r σ t‖) →
      (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
      T ^ d ≤ T / 2 → False := by
  pm_4081 Tterminal hTterminal hTerminalSmall eventually_terminal_source_majorant_lt_threshold hσ hu
  let T₀ := max Tterminal 12
  have hEightTwelve : (8 : ℝ) ≤ 12 := by norm_num
  pm_4266 T₀ hEightTwelve.trans le_max_right
  intro T Y A r W hT hA hY hr hTerminal hW hSep hLarge hRange hDisp
  pm_4630 hTTerminal Tterminal le_max_left hT
  have hTTwelve : 12 ≤ T := (le_max_right _ _).trans hT
  pm_6312
  pm_1380
  pm_4704
  have hAOne : 1 < A := by
    dsimp only [A]
    pm_4735
  have hV : 0 < ((3 / 4) * (T ^ (-u) / 2)) /
      (Nat.clog 2 A + 1 : ℕ) := by positivity
  obtain ⟨j, hj, W', _hWsub, _hSep', _hCard, _hLarge', _hPUpper, hQFourP⟩ :=
    extract_normalized_source_dyadic_block W hY hAOne hV hW hSep hLarge
  have hPA : 2 ^ j ≤ A := by
    have hjClog : j < Nat.clog 2 (A + 1) := Finset.mem_range.mp hj
    have hpow : 2 ^ j < A + 1 := Nat.pow_lt_of_lt_clog hjClog
    omega
  pm_4715
  have hQUpperNat : Q < 4 * A := by
    dsimp only [Q] at hQFourP ⊢
    exact hQFourP.trans_le (Nat.mul_le_mul_left 4 hPA)
  have hQUpper : (Q : ℝ) ≤ 24 * T := by
    calc
      (Q : ℝ) ≤ 4 * A := by exact_mod_cast hQUpperNat.le
      _ ≤ 24 * T := by nlinarith
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  pm_4705
  obtain ⟨t, htW⟩ := hW
  have hCutLt : sharpZetaCutoff T < (A : ℝ) + 1 := by
    dsimp only [A]
    exact_mod_cast Nat.lt_floor_add_one (sharpZetaCutoff T)
  have hFourTA : 4 * T < (A : ℝ) + 1 :=
    (four_mul_lt_sharpZetaCutoff T).trans hCutLt
  have hAQT : (A : ℝ) + 1 ≤ 2 * Q := by
    have hNat : A + 1 ≤ 2 * Q := by
      dsimp only [Q] at hTerminal ⊢
      omega
    exact_mod_cast hNat
  have hTL : T / 2 ≤ (L : ℝ) := by
    have hQL : (Q : ℝ) = 2 * L := by exact_mod_cast hTwiceL.symm
    rw [hQL] at hAQT
    nlinarith
  have htLower : T / 2 ≤ t := by
    have := (hRange t htW).1
    linarith
  have htUpper : t ≤ 3 * T := by
    have := (hRange t htW).2
    linarith
  have hLThree : (3 : ℝ) ≤ L := by nlinarith
  have htSq : t ≤ (L : ℝ) ^ 2 := by
    have : 3 * T ≤ (L : ℝ) ^ 2 := by nlinarith [sq_nonneg ((L : ℝ) - T / 2)]
    exact htUpper.trans this
  have hBound := norm_typeISourceSmoothBlock_terminal_le
    (Y := Y) (A := A) (r := r) (σ := σ) (t := t) hY hr
    (by simpa only [Q] using hTerminal) (by linarith) (by linarith) (by
      simpa only [L, Q] using htSq)
  have hSmall := hTerminalSmall T t Q L hTTerminal hTL hQUpper
    htLower htUpper
  have hLargeAt := hLarge t htW
  have hThresholdEq :
      ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) =
        ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) := by
    rfl
  rw [hThresholdEq] at hSmall
  have hBound' : ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
    simpa only [L, Q] using hBound
  linarith

/-- The two bottom source blocks selected from the long tail have a physical
logarithmic scale comparable with `1 / d`.  Both comparisons retain the
literal natural floor and the factor `2 ^ r`; no real surrogate for the
source length is introduced. -/
theorem eventually_lower_source_logarithmic_scale_bounds
    (d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T → r < 2 →
      let Y := ⌊T ^ d⌋₊
      let N := 2 ^ r * Y
      1 < N ∧ 1 / (2 * d) ≤ typeILogarithmicScale T N ∧
        typeILogarithmicScale T N ≤ 2 / d := by
  pm_4081 Tupper hTupper hUpper eventually_typeI_logarithmic_scale_upper d hd
  let T₀ : ℝ := max Tupper ((2 : ℝ) ^ (1 / d))
  pm_4266 T₀ hTupper.trans le_max_left
  intro T r hT hr
  dsimp only
  pm_4630 hTUpper Tupper le_max_left hT
  have hTConst : (2 : ℝ) ^ (1 / d) ≤ T :=
    (le_max_right _ _).trans hT
  have hTTwo : 2 ≤ T := hTupper.trans hTUpper
  pm_1056
  pm_6775 hUpperAt hUpper hTUpper hTauUpper
  have hPowTwo : 2 ≤ T ^ d := by
    have hRaised := Real.rpow_le_rpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      hTConst hd.le
    have hCancel : ((2 : ℝ) ^ (1 / d)) ^ d = 2 := by
      pm_4302
      have hExp : 1 / d * d = 1 := by field_simp [hd.ne']
      rw [hExp, Real.rpow_one]
    simpa only [hCancel] using hRaised
  pm_4741 hYUpper d
  have hPowR : 2 ^ r ≤ 2 := by
    pm_7057 hrCases r
    rcases hrCases with rfl | rfl <;> norm_num
  have hNUpper : (N : ℝ) ≤ T ^ (2 * d) := by
    have hFirst : (N : ℝ) ≤ 2 * T ^ d := by
      calc
        (N : ℝ) = (2 ^ r : ℕ) * (Y : ℝ) := by
          dsimp only [N]
          push_cast
          rfl
        _ ≤ 2 * (Y : ℝ) := by
          gcongr
          exact_mod_cast hPowR
        _ ≤ 2 * T ^ d := by gcongr
    have hSecond : 2 * T ^ d ≤ T ^ d * T ^ d := by
      nlinarith [Real.rpow_nonneg hTPos.le d]
    calc
      (N : ℝ) ≤ 2 * T ^ d := hFirst
      _ ≤ T ^ d * T ^ d := hSecond
      _ = T ^ (2 * d) := by
        rw [← Real.rpow_add hTPos]
        congr 1
        ring
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hNOne)
  have hLowerPhysical : (N : ℝ) ^ (1 / (2 * d)) ≤ T := by
    pm_8854 hExp d
    have hRaised := Real.rpow_le_rpow hNPos.le hNUpper hExp
    calc
      (N : ℝ) ^ (1 / (2 * d)) ≤
          (T ^ (2 * d)) ^ (1 / (2 * d)) := hRaised
      _ = T := by
        rw [← Real.rpow_mul hTPos.le]
        have hCancel : 2 * d * (1 / (2 * d)) = 1 := by
          field_simp [hd.ne']
        rw [hCancel, Real.rpow_one]
  have hTauLower : 1 / (2 * d) ≤ typeILogarithmicScale T N :=
    (Real.le_logb_iff_rpow_le (by exact_mod_cast hNOne) hTPos).mpr
      hLowerPhysical
  exact ⟨hNOne, hTauLower, hTauUpper⟩

-- Generated closures: source context is replayed in the next part.
end GuthMaynard.NativeMoment
end
