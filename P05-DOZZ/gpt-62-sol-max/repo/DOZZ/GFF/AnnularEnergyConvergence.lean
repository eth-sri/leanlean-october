/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.EnergyPositivity

/-!
# DOZZ.GFF.AnnularEnergyConvergence

Mixed-energy estimates for the smooth annular approximations to the equator law.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DOZZ

/-- The mixed raw-log energy of the `n`th and `k`th annular probability densities. -/
noncomputable def annularMixedEnergy (n k : ℕ) : ℝ :=
  ∫ q : ℂ × ℂ,
    annularProbabilityDensity n q.1 * annularProbabilityDensity k q.2 *
      (-Real.log ‖q.1 - q.2‖)
    ∂((volume : Measure ℂ).prod (volume : Measure ℂ))

/-- The mean-zero ABK pairing transports to a mixed complex logarithmic energy. -/
theorem abkLogCovariancePairing_eq_complex_pair
    (ψ φ : GaussianFields.MeanZeroTestFunction 2) :
    GaussianFields.abkLogCovariancePairing ψ φ =
      ∫ q : ℂ × ℂ,
        ψ (complexToVecTwo q.1) * φ (complexToVecTwo q.2) *
          (-Real.log ‖q.1 - q.2‖)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let ψC := ψ ∘ complexLinearEquivVecTwo
  let φC := φ ∘ complexLinearEquivVecTwo
  simpa [ψC, φC, GaussianFields.abkLogCovariancePairing, GaussianFields.abkKernelPairing,
    ← complexLinearEquivVecTwo_apply] using
    (integral_complexLogKernelPair_eq_vec ψC φC
      (ψ.continuous.comp complexLinearEquivVecTwo.continuous)
      (φ.continuous.comp complexLinearEquivVecTwo.continuous)
      (ψ.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.toHomeomorph)
      (φ.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.toHomeomorph)).2.symm

/-- The annular centered pairing for two tests and two annulus widths expands into the planar,
two mixed, and annular-annular logarithmic energies. -/
theorem annularCenteredPairing_eq_mixedExpansion (f g : TestFn) (n k : ℕ) :
    GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g k) =
      testFnLogPairing f g - testMass g * annularCrossEnergy f k -
        testMass f * annularCrossEnergy g n +
          testMass f * testMass g * annularMixedEnergy n k := by
  let m := testMass f
  let p := testMass g
  let ρn  := annularProbabilityDensity n
  let ρk  := annularProbabilityDensity k
  let μ  := (volume : Measure ℂ).prod (volume : Measure ℂ)
  let A : ℂ × ℂ → ℝ := fun q => f q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)
  let B : ℂ × ℂ → ℝ := fun q => f q.1 * ρk q.2 * (-Real.log ‖q.1 - q.2‖)
  let C : ℂ × ℂ → ℝ := fun q => ρn q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)
  let Cswap : ℂ × ℂ → ℝ := fun q => g q.1 * ρn q.2 * (-Real.log ‖q.1 - q.2‖)
  let D : ℂ × ℂ → ℝ := fun q => ρn q.1 * ρk q.2 * (-Real.log ‖q.1 - q.2‖)
  have hf := f.continuous
  have hg := g.continuous
  have hfc := f.hasCompactSupport
  have hgc := g.hasCompactSupport
  have hρn := continuous_annularProbabilityDensity n
  have hρk := continuous_annularProbabilityDensity k
  have hρnc := hasCompactSupport_annularProbabilityDensity n
  have hρkc := hasCompactSupport_annularProbabilityDensity k
  have hA : Integrable A μ := (integral_complexLogKernelPair_eq_vec f g hf hg hfc hgc).1
  have hB : Integrable B μ := (integral_complexLogKernelPair_eq_vec f ρk hf hρk hfc hρkc).1
  have hC : Integrable C μ := (integral_complexLogKernelPair_eq_vec ρn g hρn hg hρnc hgc).1
  have hD : Integrable D μ := (integral_complexLogKernelPair_eq_vec ρn ρk hρn hρk hρnc hρkc).1
  have hswap : ∫ q : ℂ × ℂ, C q ∂μ = ∫ q : ℂ × ℂ, Cswap q ∂μ := by
    calc
      _ = ∫ q : ℂ × ℂ, Cswap q.swap ∂μ := by
            apply integral_congr_ae
            filter_upwards with q
            dsimp [C, Cswap]
            rw [norm_sub_rev]
            ring
      _ = ∫ q : ℂ × ℂ, Cswap q ∂μ := integral_prod_swap Cswap
  rw [abkLogCovariancePairing_eq_complex_pair, testFnLogPairing_eq_complex]
  calc
    _ = ∫ q, (A q - p * B q) - (m * C q - m * p * D q) ∂μ := by
      apply integral_congr_ae
      filter_upwards with q
      rw [annularCenteredTestFn_complexValue, annularCenteredTestFn_complexValue]
      dsimp [A, B, C, D, m, p, ρn, ρk]
      ring
    _ = (∫ q, A q - p * B q ∂μ) - ∫ q, m * C q - m * p * D q ∂μ :=
      integral_sub (hA.sub (hB.const_mul p)) ((hC.const_mul m).sub (hD.const_mul (m * p)))
    _ = _ := by
      rw [integral_sub hA (hB.const_mul p), integral_sub (hC.const_mul m) (hD.const_mul (m * p))]
      simp only [integral_const_mul, hswap]
      change (∫ q, A q ∂μ) - p * annularCrossEnergy f k -
          (m * annularCrossEnergy g n - m * p * annularMixedEnergy n k) = _
      ring

theorem abs_annularMixedEnergy_le (n k : ℕ) :
    |annularMixedEnergy n k| ≤
      1 / ((n : ℝ) + 2) + 2 / ((k : ℝ) + 2) := by
  let ρ  := annularProbabilityDensity n
  let V  := annularLogPotential k
  let μ : Measure ℂ := volume
  let c  := 1 / ((n : ℝ) + 2) + 2 / ((k : ℝ) + 2)
  have hPair := integral_logKernel_annular ρ
    (continuous_annularProbabilityDensity n)
    (hasCompactSupport_annularProbabilityDensity n) k
  have hVInt : Integrable (fun z : ℂ => ρ z * V z) μ := by
    simpa [ρ, V, μ, annularLogPotential] using hPair.1
  have hρInt : Integrable ρ μ := by
    simpa [ρ, μ] using integrable_annularProbabilityDensity n
  have hρMass : ∫ z : ℂ, ρ z ∂μ = 1 := by
    simpa [ρ, μ] using integral_annularProbabilityDensity n
  have hD : annularMixedEnergy n k = -(∫ z : ℂ, ρ z * V z ∂μ) := by
    simpa [annularMixedEnergy, ρ, V, μ, annularLogPotential] using hPair.2
  have hUpperInt  := hρInt.const_mul c
  have hPointwise (z : ℂ) : |ρ z * V z| ≤ c * ρ z := by
    by_cases hzero : ρ z = 0
    · simp [hzero]
    · have hρnonneg  := annularProbabilityDensity_nonneg n z
      have hlog := abs_logPlus_of_annularDensity_ne_zero n z (by simpa [ρ] using hzero)
      have hpotential := abs_annularLogPotential_sub_logPlus k z
      have hpot : |V z - Real.log (max 1 ‖z‖)| ≤ 2 / ((k : ℝ) + 2) := by
        assumption
      have hV : |V z| ≤ c := by
        have htri : |V z| ≤ |V z - Real.log (max 1 ‖z‖)| +
            |Real.log (max 1 ‖z‖)| := by
          calc
            |V z| = |(V z - Real.log (max 1 ‖z‖)) +
                Real.log (max 1 ‖z‖)| := by congr 1; ring
            _ ≤ |V z - Real.log (max 1 ‖z‖)| +
                |Real.log (max 1 ‖z‖)| := abs_add_le _ _
        have hbound : |V z| ≤
            2 / ((k : ℝ) + 2) + 1 / ((n : ℝ) + 2) := by
          calc
            |V z| ≤ |V z - Real.log (max 1 ‖z‖)| +
                |Real.log (max 1 ‖z‖)| := htri
            _ ≤ 2 / ((k : ℝ) + 2) + 1 / ((n : ℝ) + 2) := add_le_add hpot hlog
        simpa [c, add_comm] using hbound
      rw [abs_mul, abs_of_nonneg hρnonneg]
      calc
        ρ z * |V z| ≤ ρ z * c := mul_le_mul_of_nonneg_left hV hρnonneg
        _ = c * ρ z := by ring
  calc
    |annularMixedEnergy n k| = |∫ z : ℂ, ρ z * V z ∂μ| := by rw [hD, abs_neg]
    _ ≤ ∫ z : ℂ, |ρ z * V z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z : ℂ, c * ρ z ∂μ := by
      apply integral_mono_ae hVInt.norm hUpperInt
      filter_upwards with z
      exact hPointwise z
    _ = c := by rw [integral_const_mul, hρMass]; ring
    _ = _ := rfl

/-- Reciprocal scale of the `n`th annular approximation. -/
private theorem tendsto_annular_width :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2)

/-- Both widths can go to zero independently in the pinned covariance limit. -/
theorem tendsto_annularCenteredPairing_prod (f g : TestFn) :
    Tendsto (fun i : ℕ × ℕ => GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f i.1) (annularCenteredTestFn g i.2))
      (atTop ×ˢ atTop) (𝓝 (gffCov f g)) := by
  let m := testMass f
  let p := testMass g
  let Lf := ∫ z : ℂ, |f z|
  let Lg := ∫ z : ℂ, |g z|
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  let C := 2 * (|p| * Lf + |m| * Lg + |m * p|)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_annular_width
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (g := fun i : ℕ × ℕ => C * (δ i.1 + δ i.2))
    (fun ⟨n, k⟩ => ?_) ?_
  · rw [Real.dist_eq, annularCenteredPairing_eq_mixedExpansion, gffCov_eq_equatorLogEnergy]
    have he : testFnLogPairing f g - p * annularCrossEnergy f k -
        m * annularCrossEnergy g n + m * p * annularMixedEnergy n k -
          (testFnLogPairing f g + testFnPotential f * p + m * testFnPotential g) =
        -(p * (annularCrossEnergy f k + testFnPotential f) +
          m * (annularCrossEnergy g n + testFnPotential g)) + m * p * annularMixedEnergy n k := by ring
    rw [he]
    refine (abs_add_le ..).trans ?_
    rw [abs_neg]
    refine (add_le_add (abs_add_le ..) le_rfl).trans ?_
    simp only [abs_mul]
    have hk : |annularCrossEnergy f k + testFnPotential f| ≤ 2 * δ k * Lf := by
      simpa only [δ, mul_one_div] using abs_annularCrossEnergy_add_testFnPotential f k
    have hn : |annularCrossEnergy g n + testFnPotential g| ≤ 2 * δ n * Lg := by
      simpa only [δ, mul_one_div] using abs_annularCrossEnergy_add_testFnPotential g n
    have hnk : |annularMixedEnergy n k| ≤ δ n + 2 * δ k := by
      simpa only [δ, mul_one_div] using abs_annularMixedEnergy_le n k
    refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hk (abs_nonneg p))
      (mul_le_mul_of_nonneg_left hn (abs_nonneg m)))
      (mul_le_mul_of_nonneg_left hnk (mul_nonneg (abs_nonneg m) (abs_nonneg p)))).trans ?_
    simp only [C, abs_mul]
    have hc1 : 0 ≤ |p| * Lf * δ n := by dsimp [Lf, δ]; positivity
    have hc2 : 0 ≤ |m| * Lg * δ k := by dsimp [Lg, δ]; positivity
    have hc3 : 0 ≤ |m| * |p| * δ n := by dsimp [δ]; positivity
    linarith only [hc1, hc2, hc3]
  · simpa using ((hδ.comp tendsto_fst).add (hδ.comp tendsto_snd)).const_mul C

theorem tendsto_annularCenteredPairing_gffCov (f g : TestFn) :
    Tendsto (fun n => GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f n) (annularCenteredTestFn g n)) atTop (𝓝 (gffCov f g)) := by
  simpa only [Function.comp_def, Function.diag] using
    (tendsto_annularCenteredPairing_prod f g).comp (tendsto_diag (f := (atTop : Filter ℕ)))

theorem gffCov_self_nonneg (f : TestFn) : 0 ≤ gffCov f f :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds (tendsto_annularCenteredPairing_gffCov f f)
    (fun n => abkLogCovariancePairing_self_nonneg (annularCenteredTestFn f n))

end DOZZ
