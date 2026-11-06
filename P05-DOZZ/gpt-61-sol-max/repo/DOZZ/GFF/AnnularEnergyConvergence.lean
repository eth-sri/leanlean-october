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
  let ψC  := fun z => ψ (complexLinearEquivVecTwo z)
  let φC  := fun z => φ (complexLinearEquivVecTwo z)
  have hψC  := ψ.continuous.comp complexLinearEquivVecTwo.continuous
  have hφC  := φ.continuous.comp complexLinearEquivVecTwo.continuous
  have hψCc  :=
    ψ.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.toHomeomorph
  have hφCc  :=
    φ.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.toHomeomorph
  have hpair := integral_complexLogKernelPair_eq_vec ψC φC hψC hφC hψCc hφCc
  have hkernel (z w : ℂ) :
      GaussianFields.abkLogCovarianceKernel (complexToVecTwo z) (complexToVecTwo w) =
        -Real.log ‖z - w‖ := congrArg (fun t : ℝ => -Real.log t) (euclideanNorm_complexToVecTwo (z - w))
  have hback (z : ℂ) : complexLinearEquivVecTwo.symm (complexToVecTwo z) = z := by
    rw [← complexLinearEquivVecTwo_apply]
    simp
  have hψmap (z : ℂ) : ψC z = ψ (complexToVecTwo z) := by
    simp [ψC, complexLinearEquivVecTwo_apply]
  have hφmap (z : ℂ) : φC z = φ (complexToVecTwo z) := by
    simp [φC, complexLinearEquivVecTwo_apply]
  aesop

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
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  let A : ℂ × ℂ → ℝ := fun q => f q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)
  let B : ℂ × ℂ → ℝ := fun q => f q.1 * ρk q.2 * (-Real.log ‖q.1 - q.2‖)
  let C : ℂ × ℂ → ℝ := fun q => ρn q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)
  let Cswap : ℂ × ℂ → ℝ := fun q => g q.1 * ρn q.2 * (-Real.log ‖q.1 - q.2‖)
  let D : ℂ × ℂ → ℝ := fun q => ρn q.1 * ρk q.2 * (-Real.log ‖q.1 - q.2‖)
  let h  := fun z => f z - m * ρn z
  let j  := fun z => g z - p * ρk z
  have hρnc := continuous_annularProbabilityDensity n
  have hρkc := continuous_annularProbabilityDensity k
  have hρncs := hasCompactSupport_annularProbabilityDensity n
  have hρkcs := hasCompactSupport_annularProbabilityDensity k
  have hhc  := f.continuous.sub (hρnc.const_mul m)
  have hjc  := g.continuous.sub (hρkc.const_mul p)
  have hhcs : HasCompactSupport h := by
    have hmul : HasCompactSupport (fun z : ℂ => m * ρn z) := hρncs.smul_left (f := fun _ : ℂ => m)
    exact f.hasCompactSupport.sub hmul
  have hjcs : HasCompactSupport j := by
    have hmul : HasCompactSupport (fun z : ℂ => p * ρk z) := hρkcs.smul_left (f := fun _ : ℂ => p)
    exact g.hasCompactSupport.sub hmul
  have hA0 := integral_complexLogKernelPair_eq_vec f g
    f.continuous g.continuous f.hasCompactSupport g.hasCompactSupport
  have hB0 := integral_complexLogKernelPair_eq_vec f ρk
    f.continuous hρkc f.hasCompactSupport hρkcs
  have hC0 := integral_complexLogKernelPair_eq_vec ρn g
    hρnc g.continuous hρncs g.hasCompactSupport
  have hCswap0 := integral_complexLogKernelPair_eq_vec g ρn
    g.continuous hρnc g.hasCompactSupport hρncs
  have hD0 := integral_complexLogKernelPair_eq_vec ρn ρk
    hρnc hρkc hρncs hρkcs
  have hAint : Integrable A μ := hA0.1
  have hBint : Integrable B μ := hB0.1
  have hCint : Integrable C μ := hC0.1

  have hDint : Integrable D μ := hD0.1
  have hHJ0 := integral_complexLogKernelPair_eq_vec h j hhc hjc hhcs hjcs

  have hpB  := hBint.const_mul p
  have hmC  := hCint.const_mul m
  have hmpD  := hDint.const_mul (m * p)
  have hpoint (q : ℂ × ℂ) :
      h q.1 * j q.2 * (-Real.log ‖q.1 - q.2‖) =
        (A q - p * B q) - (m * C q - m * p * D q) := by
    bound
  have hswap : ∫ q : ℂ × ℂ, C q ∂μ = ∫ q : ℂ × ℂ, Cswap q ∂μ := by
    calc
      _ = ∫ q : ℂ × ℂ, Cswap q.swap ∂μ := by
            apply integral_congr_ae
            filter_upwards with q
            dsimp [C, Cswap]
            rw [norm_sub_rev]
            ring
      _ = ∫ q : ℂ × ℂ, Cswap q ∂μ := integral_prod_swap Cswap
  have hBvalue : annularCrossEnergy f k = ∫ q : ℂ × ℂ, B q ∂μ := rfl
  have hCvalue : annularCrossEnergy g n = ∫ q : ℂ × ℂ, Cswap q ∂μ := rfl
  have hDvalue : annularMixedEnergy n k = ∫ q : ℂ × ℂ, D q ∂μ := rfl
  have hpair := abkLogCovariancePairing_eq_complex_pair
    (annularCenteredTestFn f n) (annularCenteredTestFn g k)
  have hpair' :
      GaussianFields.abkLogCovariancePairing
          (annularCenteredTestFn f n) (annularCenteredTestFn g k) =
        ∫ q : ℂ × ℂ, h q.1 * j q.2 * (-Real.log ‖q.1 - q.2‖) ∂μ := by
    calc
      _ = ∫ q : ℂ × ℂ,
            annularCenteredTestFn f n (complexToVecTwo q.1) *
              annularCenteredTestFn g k (complexToVecTwo q.2) *
                (-Real.log ‖q.1 - q.2‖) ∂μ := hpair
      _ = ∫ q : ℂ × ℂ, h q.1 * j q.2 *
            (-Real.log ‖q.1 - q.2‖) ∂μ := by
          apply integral_congr_ae
          filter_upwards with q
          rw [annularCenteredTestFn_complexValue, annularCenteredTestFn_complexValue]
  have hExpanded :
      (∫ q : ℂ × ℂ, h q.1 * j q.2 * (-Real.log ‖q.1 - q.2‖) ∂μ) =
        (∫ q : ℂ × ℂ, A q ∂μ) - p * (∫ q : ℂ × ℂ, B q ∂μ) -
          m * (∫ q : ℂ × ℂ, C q ∂μ) +
            m * p * (∫ q : ℂ × ℂ, D q ∂μ) := by
    calc
      _ = ∫ q : ℂ × ℂ, (A q - p * B q) - (m * C q - m * p * D q) ∂μ := by
            simp_all
      _ = (∫ q : ℂ × ℂ, A q - p * B q ∂μ) -
            ∫ q : ℂ × ℂ, m * C q - m * p * D q ∂μ :=
          integral_sub (hAint.sub hpB) (hmC.sub hmpD)
      _ = _ := by
            rw [integral_sub hAint hpB, integral_sub hmC hmpD]
            simp only [integral_const_mul]
            ring
  have hAtest : testFnLogPairing f g = ∫ q : ℂ × ℂ, A q ∂μ := testFnLogPairing_eq_complex f g
  grind

def integrable_annularMixedEnergyIntegrand (n k : ℕ)  := (integral_complexLogKernelPair_eq_vec
    (annularProbabilityDensity n) (annularProbabilityDensity k)
    (continuous_annularProbabilityDensity n) (continuous_annularProbabilityDensity k)
    (hasCompactSupport_annularProbabilityDensity n)
    (hasCompactSupport_annularProbabilityDensity k)).1

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
    continuity
  have hρInt : Integrable ρ μ := integrable_annularProbabilityDensity n
  have hρMass : ∫ z : ℂ, ρ z ∂μ = 1 := integral_annularProbabilityDensity n
  have hD : annularMixedEnergy n k = -(∫ z : ℂ, ρ z * V z ∂μ) := by
    bound

  have hUpperInt  := hρInt.const_mul c
  have hPointwise (z : ℂ) : |ρ z * V z| ≤ c * ρ z := by
    by_cases hzero : ρ z = 0
    · simp [hzero]
    · have hρnonneg  := annularProbabilityDensity_nonneg n z
      have hlog := abs_logPlus_of_annularDensity_ne_zero n z (hzero)
      have hpotential := abs_annularLogPotential_sub_logPlus k z

      have hV : |V z| ≤ c := by
        grind
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

/-- The mixed annular centered energies converge quantitatively to the pinned covariance. -/
theorem abs_annularCenteredPairing_sub_gffCov_le (f : TestFn) (n k : ℕ) :
    |GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn f k) - gffCov f f| ≤
      (2 * (|testMass f| * (∫ z : ℂ, |f z|) + (testMass f) ^ 2)) *
        (1 / ((n : ℝ) + 2) + 1 / ((k : ℝ) + 2)) := by
  let m  := testMass f
  let L  := ∫ z : ℂ, |f z|
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  let Q  := fun i j =>
    GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f i) (annularCenteredTestFn f j)
  let C  := 2 * (|m| * L + m ^ 2)
  have hCovExpansion : gffCov f f = testFnLogPairing f f + 2 * m * testFnPotential f := by
    rw [gffCov_eq_equatorLogEnergy]
    dsimp [m]
    ring
  have hQ : Q n k = testFnLogPairing f f - m * annularCrossEnergy f k -
      m * annularCrossEnergy f n + m ^ 2 * annularMixedEnergy n k := by
    dsimp [Q]
    rw [annularCenteredPairing_eq_mixedExpansion f f n k]
    dsimp [m]
    ring
  have hCrossN := abs_annularCrossEnergy_add_testFnPotential f n
  have hCrossK := abs_annularCrossEnergy_add_testFnPotential f k
  have hMixed := abs_annularMixedEnergy_le n k
  have hDiff : Q n k - gffCov f f =
      -m * (annularCrossEnergy f k + testFnPotential f) -
        m * (annularCrossEnergy f n + testFnPotential f) +
          m ^ 2 * annularMixedEnergy n k := by
    rw [hQ, hCovExpansion]
    ring

  have hCrossN' : |annularCrossEnergy f n + testFnPotential f| ≤
      2 * δ n * L := by
    continuity
  have hCrossK' : |annularCrossEnergy f k + testFnPotential f| ≤
      2 * δ k * L := by
    continuity
  have hMixed' : |annularMixedEnergy n k| ≤ δ n + 2 * δ k := by
    grind
  calc
    |Q n k - gffCov f f| =
        |-m * (annularCrossEnergy f k + testFnPotential f) -
          m * (annularCrossEnergy f n + testFnPotential f) +
            m ^ 2 * annularMixedEnergy n k| := by rw [hDiff]
    _ ≤ |m| * |annularCrossEnergy f k + testFnPotential f| +
          |m| * |annularCrossEnergy f n + testFnPotential f| +
            m ^ 2 * |annularMixedEnergy n k| := by
        calc
          _ ≤ |-m * (annularCrossEnergy f k + testFnPotential f) -
                m * (annularCrossEnergy f n + testFnPotential f)| +
                  |m ^ 2 * annularMixedEnergy n k| := abs_add_le (-m * (annularCrossEnergy f k + testFnPotential f) - m * (annularCrossEnergy f n + testFnPotential f)) (m ^ 2 * annularMixedEnergy n k)
          _ ≤ |-m * (annularCrossEnergy f k + testFnPotential f)| +
                |m * (annularCrossEnergy f n + testFnPotential f)| +
                  |m ^ 2 * annularMixedEnergy n k| := by
                have hAB  := abs_sub (-m * (annularCrossEnergy f k + testFnPotential f)) (m * (annularCrossEnergy f n + testFnPotential f))
                exact add_le_add hAB le_rfl
          _ = _ := by simp_all
    _ ≤ |m| * (2 * δ k * L) + |m| * (2 * δ n * L) +
          m ^ 2 * (δ n + 2 * δ k) := by
        bound
    _ ≤ C * (δ n + δ k) := by
        have hδn : 0 ≤ δ n := by dsimp [δ]; positivity
        have hdouble : m ^ 2 * δ n ≤ 2 * m ^ 2 * δ n := by
          calc
            _ = m ^ 2 * δ n + 0 := by ring
            _ ≤ m ^ 2 * δ n + m ^ 2 * δ n :=
              add_le_add le_rfl (mul_nonneg (sq_nonneg m) hδn)
            _ = _ := by ring
        grind
    _ = _ := by
        dsimp [C, δ, m, L]

/-- The mixed annular centered pairing converges quantitatively to the full pinned covariance. -/
theorem abs_annularCenteredPairing_sub_gffCov_le_mixed
    (f g : TestFn) (n k : ℕ) :
    |GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g k) - gffCov f g| ≤
      (2 * (|testMass g| * (∫ z : ℂ, |f z|) +
        |testMass f| * (∫ z : ℂ, |g z|) +
        |testMass f * testMass g|)) *
        (1 / ((n : ℝ) + 2) + 1 / ((k : ℝ) + 2)) := by
  let m  := testMass f
  let p  := testMass g
  let Lf  := ∫ z : ℂ, |f z|
  let Lg  := ∫ z : ℂ, |g z|
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  let Q  := fun i j =>
    GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f i) (annularCenteredTestFn g j)
  let C  := 2 * (|p| * Lf + |m| * Lg + |m * p|)
  have hCovExpansion :
      gffCov f g = testFnLogPairing f g + testFnPotential f * p +
        m * testFnPotential g := by
    rw [gffCov_eq_equatorLogEnergy]
  have hQ : Q n k = testFnLogPairing f g - p * annularCrossEnergy f k -
      m * annularCrossEnergy g n + m * p * annularMixedEnergy n k := by
    dsimp [Q]
    rw [annularCenteredPairing_eq_mixedExpansion f g n k]
  have hDiff : Q n k - gffCov f g =
      -p * (annularCrossEnergy f k + testFnPotential f) -
        m * (annularCrossEnergy g n + testFnPotential g) +
          m * p * annularMixedEnergy n k := by
    rw [hQ, hCovExpansion]
    ring
  have hLf : 0 ≤ Lf := by
    positivity
  have hLg : 0 ≤ Lg := by
    positivity
  have hCrossf := abs_annularCrossEnergy_add_testFnPotential f k
  have hCrossg := abs_annularCrossEnergy_add_testFnPotential g n
  have hMixed := abs_annularMixedEnergy_le n k
  have hCrossf' : |annularCrossEnergy f k + testFnPotential f| ≤
      2 * δ k * Lf := by
    continuity
  have hCrossg' : |annularCrossEnergy g n + testFnPotential g| ≤
      2 * δ n * Lg := by
    grind
  have hMixed' : |annularMixedEnergy n k| ≤ δ n + 2 * δ k := by
    grind
  have hCoeffK : 2 * |p| * Lf + 2 * |m * p| ≤ C := by
    dsimp [C]
    have hnonneg  := mul_nonneg (abs_nonneg m) hLg
    linarith
  have hCoeffN : 2 * |m| * Lg + |m * p| ≤ C := by
    dsimp [C]
    have hnonneg  := mul_nonneg (abs_nonneg p) hLf
    grind
  have hδn : 0 ≤ δ n := by dsimp [δ]; positivity
  have hδk : 0 ≤ δ k := by dsimp [δ]; positivity
  calc
    |Q n k - gffCov f g| =
        |-p * (annularCrossEnergy f k + testFnPotential f) -
          m * (annularCrossEnergy g n + testFnPotential g) +
            m * p * annularMixedEnergy n k| := by rw [hDiff]
    _ ≤ |p| * |annularCrossEnergy f k + testFnPotential f| +
          |m| * |annularCrossEnergy g n + testFnPotential g| +
            |m * p| * |annularMixedEnergy n k| := by
        calc
          _ ≤ |-p * (annularCrossEnergy f k + testFnPotential f) -
                m * (annularCrossEnergy g n + testFnPotential g)| +
                  |m * p * annularMixedEnergy n k| := by
                grind
          _ ≤ |-p * (annularCrossEnergy f k + testFnPotential f)| +
                |m * (annularCrossEnergy g n + testFnPotential g)| +
                  |m * p * annularMixedEnergy n k| := by
                have hab  := abs_sub (-p * (annularCrossEnergy f k + testFnPotential f)) (m * (annularCrossEnergy g n + testFnPotential g))
                exact add_le_add hab le_rfl
          _ = _ := by
                simp_all
    _ ≤ |p| * (2 * δ k * Lf) + |m| * (2 * δ n * Lg) +
          |m * p| * (δ n + 2 * δ k) := by
        bound
    _ ≤ C * (δ n + δ k) := by
        calc
          _ = (2 * |m| * Lg + |m * p|) * δ n +
                (2 * |p| * Lf + 2 * |m * p|) * δ k := by ring
          _ ≤ C * δ n + C * δ k := by
                bound
          _ = C * (δ n + δ k) := by ring
    _ = _ := by dsimp [C, δ, m, p, Lf, Lg]

/-- The diagonal sequence of mixed annular pairings converges to the pinned covariance. -/
theorem tendsto_annularCenteredPairing_gffCov (f g : TestFn) :
    Tendsto
      (fun n => GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn g n))
      atTop (𝓝 (gffCov f g)) := by
  let m  := testMass f
  let p  := testMass g
  let Lf  := ∫ z : ℂ, |f z|
  let Lg  := ∫ z : ℂ, |g z|
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)

  let C  := 2 * (|p| * Lf + |m| * Lg + |m * p|)
  let B  := fun j => C * (δ j + δ j)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext j
    simp [δ, Nat.cast_add]
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa [B] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul (hδ.add hδ)
  have hconst : Tendsto (fun _ : ℕ => gffCov f g) atTop (𝓝 (gffCov f g)) :=
    tendsto_const_nhds
  have hlow : Tendsto (fun j => gffCov f g - B j) atTop (𝓝 (gffCov f g)) := by
    simpa [sub_eq_add_neg, add_comm] using hconst.add hB.neg
  have hupp : Tendsto (fun j => gffCov f g + B j) atTop (𝓝 (gffCov f g)) := by
    simpa using hconst.add hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro j
    have h := abs_le.mp (abs_annularCenteredPairing_sub_gffCov_le_mixed f g j j)
    continuity
  · intro j
    have h := abs_le.mp (abs_annularCenteredPairing_sub_gffCov_le_mixed f g j j)
    grind

end DOZZ

end
