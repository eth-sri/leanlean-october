/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import GaussianFields.LogCorrelated.ABK.LogLimit

/-!
# GaussianFields.LogCorrelated/ABK/KernelPairing

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


variable {d : Nat} (ψ φ : MeanZeroTestFunction d)

include d ψ φ
/-- Product-measure kernel pairing against two ABK test functions. -/
@[expose]
noncomputable def abkKernelPairing
    (K : Vec d → Vec d → ℝ) : ℝ :=
  ∫ p : Vec d × Vec d,
    ψ p.1 * φ p.2 * K p.1 p.2
    ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d)))


/-- Product-measure kernel pairings can be written as iterated integrals once the product
integrand is integrable. -/
theorem abkKernelPairing_eq_integral_integral  (K : Vec d → Vec d → ℝ)
    (hint :
      Integrable
        (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * K p.1 p.2)
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d)))) :
    abkKernelPairing ψ φ K =
      ∫ x : Vec d,
        ∫ y : Vec d, ψ x * φ y * K x y
        ∂(volume : Measure (Vec d))
      ∂(volume : Measure (Vec d)) := by
  unfold abkKernelPairing
  rw [integral_prod _ hint]


/-- Mean-zero test functions annihilate the constant kernel in product-measure pairing form. -/
theorem abkKernelPairing_const_one_eq_zero  :
    abkKernelPairing ψ φ (fun _ _ => 1) = 0 := by
  unfold abkKernelPairing
  calc
    (∫ p : Vec d × Vec d,
        ψ p.1 * φ p.2 * (fun _ _ => (1 : ℝ)) p.1 p.2
        ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))))
        = ∫ p : Vec d × Vec d,
            ψ p.1 * φ p.2
            ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
          simp_all
    _ = (∫ x : Vec d, ψ x ∂(volume : Measure (Vec d))) *
        ∫ y : Vec d, φ y ∂(volume : Measure (Vec d)) := by
          rw [integral_prod_mul]
    _ = 0 := by rw [ψ.integral_eq_zero, zero_mul]


/-- The constant-kernel product integrand is integrable for compact mean-zero test functions. -/
theorem integrable_abkKernelPairing_const_one  :
    Integrable
      (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * (1 : ℝ))
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  simpa only [mul_one] using ψ.integrable.mul_prod φ.integrable
omit d ψ φ


/-- The Riesz kernel `|x-y|^{-α}` used in Appendix A's Abel regularization. -/
@[expose]
noncomputable def abkRieszKernel {d : Nat} (α : ℝ) (x y : Vec d) : ℝ :=
  (euclideanNorm (x - y)) ^ (-α)

include d ψ φ in
/-- Product-measure pairing with the Riesz kernel. -/
@[expose]
noncomputable def abkRieszPairing  (α : ℝ) : ℝ :=
  abkKernelPairing ψ φ (abkRieszKernel α)

/-- The centered Riesz slope `( |x-y|^{-α} - 1 ) / α`. -/
@[expose]
noncomputable def abkCenteredRieszSlopeKernel {d : Nat} (α : ℝ) (x y : Vec d) : ℝ :=
  ((euclideanNorm (x - y)) ^ (-α) - 1) / α

/-- The centered Riesz difference `|x-y|^{-α} - 1`. -/
@[expose]
noncomputable def abkCenteredRieszDifferenceKernel {d : Nat} (α : ℝ) (x y : Vec d) : ℝ :=
  (euclideanNorm (x - y)) ^ (-α) - 1

include d ψ φ
/-- Product-measure pairing with the centered Riesz slope kernel. -/
@[expose]
noncomputable def abkCenteredRieszSlopePairing  (α : ℝ) : ℝ :=
  abkKernelPairing ψ φ (abkCenteredRieszSlopeKernel α)


/-- Product-measure pairing with the centered Riesz difference kernel. -/
@[expose]
noncomputable def abkCenteredRieszDifferencePairing  (α : ℝ) : ℝ :=
  abkKernelPairing ψ φ (abkCenteredRieszDifferenceKernel α)


/-- Product-measure pairing with the logarithmic covariance kernel. -/
@[expose]
noncomputable def abkLogCovariancePairing  : ℝ :=
  abkKernelPairing ψ φ abkLogCovarianceKernel


/-- Mean-zero cancellation identifies the Riesz pairing with its centered-difference version. -/
theorem abkCenteredRieszDifferencePairing_eq_rieszPairing  (α : ℝ)
    (hR :
      Integrable
        (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2)
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d)))) :
    abkCenteredRieszDifferencePairing ψ φ α = abkRieszPairing ψ φ α := by
  let μ : Measure (Vec d × Vec d) :=
    (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  have hconst  :=
    integrable_abkKernelPairing_const_one ψ φ
  have hzero :
      (∫ p : Vec d × Vec d, ψ p.1 * φ p.2 * (1 : ℝ) ∂μ) = 0 := abkKernelPairing_const_one_eq_zero ψ φ
  unfold abkCenteredRieszDifferencePairing abkRieszPairing abkKernelPairing
  calc
    (∫ p : Vec d × Vec d,
        ψ p.1 * φ p.2 * abkCenteredRieszDifferenceKernel α p.1 p.2 ∂μ)
        = ∫ p : Vec d × Vec d,
            (ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2) -
              (ψ p.1 * φ p.2 * (1 : ℝ)) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with p
          simp [abkCenteredRieszDifferenceKernel, abkRieszKernel]
          ring
    _ = (∫ p : Vec d × Vec d,
            ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2 ∂μ) -
          ∫ p : Vec d × Vec d, ψ p.1 * φ p.2 * (1 : ℝ) ∂μ := by
          rw [integral_sub hR hconst]
    _ = ∫ p : Vec d × Vec d,
          ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2 ∂μ := by
          rw [hzero, sub_zero]
omit d ψ φ


/-- The diagonal is null for product Lebesgue measure in positive dimension. -/
theorem ae_fst_ne_snd_volume_prod {d : Nat} (hd : 0 < d) :
    ∀ᵐ p : Vec d × Vec d
      ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
      p.1 ≠ p.2 := by
  have  := Fin.pos_iff_nonempty.mp hd
  let μ : Measure (Vec d) := volume
  have hmeas : MeasurableSet {p : Vec d × Vec d | p.1 ≠ p.2} := by
    measurability
  rw [Measure.ae_prod_iff_ae_ae hmeas]
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnull  := measure_singleton (μ := μ) x
  filter_upwards [compl_mem_ae_iff.mpr hnull] with y hy
  exact fun hxy => hy hxy.symm

/-- A.e. pointwise limit of the centered Riesz slope kernel pairing integrand. -/
theorem ae_tendsto_abkCenteredRieszSlopeKernel_integrand {d : Nat} (hd : 0 < d)
    (ψ φ : MeanZeroTestFunction d) :
    ∀ᵐ p : Vec d × Vec d
      ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
      Tendsto
        (fun α : ℝ =>
          ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (ψ p.1 * φ p.2 * abkLogCovarianceKernel p.1 p.2)) := by
  filter_upwards [ae_fst_ne_snd_volume_prod hd] with p hp_ne
  have hlim := tendsto_euclideanNorm_rpow_neg_sub_one_div_nhdsGT_zero
    (d := d) (x := p.1) (y := p.2) hp_ne
  exact hlim.const_mul (ψ p.1 * φ p.2)

/-- Dominated convergence for the ABK centered Riesz slope pairings.  The concrete majorant is
the remaining local-integrability estimate near the diagonal. -/
theorem tendsto_abkCenteredRieszSlopePairing_of_dominated {d : Nat} (hd : 0 < d)
    (ψ φ : MeanZeroTestFunction d) (bound : Vec d × Vec d → ℝ)
    (hmeas :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable
          (fun p : Vec d × Vec d =>
            ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
          ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))))
    (hbound :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ p : Vec d × Vec d
          ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
          ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤ bound p)
    (hbound_int :
      Integrable bound ((volume : Measure (Vec d)).prod (volume : Measure (Vec d)))) :
    Tendsto (fun α : ℝ => abkCenteredRieszSlopePairing ψ φ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkLogCovariancePairing ψ φ)) := tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hbound_int
    (ae_tendsto_abkCenteredRieszSlopeKernel_integrand hd ψ φ)

include d ψ φ in
/-- The centered difference pairing is `α` times the centered slope pairing. -/
theorem abkCenteredRieszDifferencePairing_eq_mul_slope  (α : ℝ) :
    abkCenteredRieszDifferencePairing ψ φ α =
      α * abkCenteredRieszSlopePairing ψ φ α := by
  unfold abkCenteredRieszDifferencePairing abkCenteredRieszSlopePairing
    abkKernelPairing abkCenteredRieszDifferenceKernel abkCenteredRieszSlopeKernel
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with p
  by_cases hα : α = 0
  · simp [hα]
  · field_simp [hα]

/-- Combining dominated convergence for the centered slopes with `α M_α^{-1} → M_0` gives the
ABK centered Riesz pairing limit. -/
theorem tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing_of_dominated {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (bound : Vec d × Vec d → ℝ)
    (hmeas :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable
          (fun p : Vec d × Vec d =>
            ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
          ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))))
    (hbound :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ p : Vec d × Vec d
          ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
          ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤ bound p)
    (hbound_int :
      Integrable bound ((volume : Measure (Vec d)).prod (volume : Measure (Vec d)))) :
    Tendsto
      (fun α : ℝ =>
        abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α)
      (𝓝[>] (0 : ℝ))
      (𝓝 (abkM0 ζ * abkLogCovariancePairing ψ φ)) := by
  have hM := tendsto_alpha_mul_abkMAlphaInv hd ζ
  have hslope :=
    tendsto_abkCenteredRieszSlopePairing_of_dominated
      hd ψ φ bound hmeas hbound hbound_int
  have hprod := hM.mul hslope
  refine hprod.congr' ?_
  filter_upwards with α
  rw [abkCenteredRieszDifferencePairing_eq_mul_slope ψ φ α]
  ring

/-- The canonical normalization converts the `M_0` logarithmic limit into the ABK covariance
prefactor. -/
theorem abkNormalizationRadicand_mul_logCovarianceLimit {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    abkNormalizationRadicand ζ * (abkM0 ζ * abkLogCovariancePairing ψ φ) =
      abkLGFCovarianceConstant d * abkLogCovariancePairing ψ φ := by
  rw [← mul_assoc, abkNormalizationRadicand_mul_abkM0]

end GaussianFields

end
