module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalWeakModes
public import RequestProject.PlanarNotation

/-!
# Actual conformal harmonic coefficients with an independent mass forcing

The weak equation may contain a physical H¹ vector `q` distinct from its
solution `u`. Physical inverse-coordinate tests identify the mass term with
the actual Jacobian-weighted forcing of `q`, including for projected regular
solutions and resonant vectors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

/-- The genuine normalized weak equation with an independent physical mass
forcing vector. -/
def IsNormalizedNeumannForcedSolution {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (b : L2Z) (u q : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      ⟪h1Value Ω v, h1Value Ω q⟫_ℂ = ⟪Q v, b⟫_ℂ

private theorem forced_halfTrace_pullback_apply (Φ : SmoothDiskMap)
    (hL : IsLipschitzDomain Φ.domain) (v : NeumannH1 Φ.domain) :
    Φ.pulledBackHalfTrace hL v =
      diskHalfTrace (Φ.h1Pullback hL v) :=
  (by measurability)

private theorem normalize_forced_weak_mode {s t k a I b : ℂ}
    (hs : s ≠ 0) (hk : k ≠ 0)
    (h : s ^ 2 * k * a - I = t * s * b) :
    t * s * a - (t ^ 2 / k) * b = (t / (s * k)) * I := by
  grind

private theorem forced_principal_ratio_pos (m : ℕ) :
    (((sobWeight ((m + 1 : ℕ) : ℤ) /
        |(((m + 1 : ℕ) : ℤ) : ℝ)| : ℝ) : ℂ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_natCast,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  simp only [hweight, Int.cast_natCast,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]

private theorem forced_principal_ratio_neg (m : ℕ) :
    (((sobWeight (-((m + 1 : ℕ) : ℤ)) /
        |((-((m + 1 : ℕ) : ℤ)) : ℝ)| : ℝ) : ℂ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hweight : sobWeight (-((m + 1 : ℕ) : ℤ)) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  simp only [hweight, Int.cast_natCast, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]

section

section

variable (Φ : DiskCoordinates) (b : L2Z) (u q : NeumannH1 Φ.domain)
    (hu : IsNormalizedNeumannForcedSolution (Φ.pulledBackHalfTrace Φ.lipschitzDomain) b u q)
    (m : ℕ)
include hu

theorem localConformal_forced_weak_holomorphic_mode :
    (anglePeriod : ℂ) * (m : ℂ) *
      angleCoeff (Φ.pulledBackTrace Φ.lipschitzDomain u : ℝ → ℂ) (m : ℤ) -
        (∫ z in unitDisk,
          (Φ.massForcing Φ.lipschitzDomain Φ.deriv_upper q : ℂ → ℂ) z * conj z ^ m) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * fourierScale) * b (m : ℤ) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test Φ Φ.chart Φ.chart_eq Φ.source Φ.smoothInverse (contDiff_diskHolomorphicMode m)
  have hp' : Φ.h1Pullback Φ.lipschitzDomain
      (smoothTraceH1 Φ.domain f) = diskHolomorphicH1Test m := hp
  have hg := localConformalH1Pullback_gradient_inner Φ (smoothTraceH1 Φ.domain f) u
  have hm := localConformal_mass_pairing Φ (smoothTraceH1 Φ.domain f) q
  have htrace : Φ.pulledBackHalfTrace Φ.lipschitzDomain
      (smoothTraceH1 Φ.domain f) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * fourierScale) • stdBasisZ (m : ℤ) := by
    rw [forced_halfTrace_pullback_apply, hp']
    exact diskHalfTrace_holomorphicTest m
  have hw := hu (smoothTraceH1 Φ.domain f)
  rw [← hg, hm, hp', disk_gradient_form_holomorphicTest,
    h1Value_diskHolomorphicH1Test, inner_diskHolomorphicArea_eq_integral, htrace] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw

theorem localConformal_forced_weak_antiholomorphic_mode :
    (anglePeriod : ℂ) * (m : ℂ) *
      angleCoeff (Φ.pulledBackTrace Φ.lipschitzDomain u : ℝ → ℂ) (-(m : ℤ)) -
        (∫ z in unitDisk,
          (Φ.massForcing Φ.lipschitzDomain Φ.deriv_upper q : ℂ → ℂ) z * z ^ m) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * fourierScale) * b (-(m : ℤ)) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test Φ Φ.chart Φ.chart_eq Φ.source Φ.smoothInverse (contDiff_diskAntiholomorphicMode m)
  have hp' : Φ.h1Pullback Φ.lipschitzDomain
      (smoothTraceH1 Φ.domain f) = diskAntiholomorphicH1Test m := hp
  have hg := localConformalH1Pullback_gradient_inner Φ (smoothTraceH1 Φ.domain f) u
  have hm := localConformal_mass_pairing Φ (smoothTraceH1 Φ.domain f) q
  have htrace : Φ.pulledBackHalfTrace Φ.lipschitzDomain
      (smoothTraceH1 Φ.domain f) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * fourierScale) • stdBasisZ (-(m : ℤ)) := by
    rw [forced_halfTrace_pullback_apply, hp']
    exact diskHalfTrace_antiholomorphicTest m
  have hw := hu (smoothTraceH1 Φ.domain f)
  rw [← hg, hm, hp', disk_gradient_form_antiholomorphicTest,
    hardy_value_antiholomorphicTest, inner_diskAntiholomorphicArea_eq_integral, htrace] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw

theorem localConformal_forced_principal_mode_pos :
    Φ.pulledBackHalfTrace Φ.lipschitzDomain u ((m + 1 : ℕ) : ℤ) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b ((m + 1 : ℕ) : ℤ) =
        diskMassForcingCoeff (Φ.massForcing Φ.lipschitzDomain Φ.deriv_upper q)
          ((m + 1 : ℕ) : ℤ) := by
  have hw := localConformal_forced_weak_holomorphic_mode Φ b u q hu (m + 1)
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_natCast, abs_of_nonneg (by positivity :
      0 ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  have hs : fourierScale ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity :
    ((m + 1 : ℕ) : ℝ) ≠ 0)
  have hs2 : fourierScale ^ 2 = (anglePeriod : ℂ) := by
    exact_mod_cast Real.sq_sqrt two_pi_pos.le
  have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ))
  rw [hweight] at hw
  have hn := normalize_forced_weak_mode hs hk
    (by simpa only [hs2, Complex.ofReal_natCast] using hw)
  rw [ht2] at hn
  rw [localConformalDiskHalfTrace_apply]
  change (Real.sqrt (sobWeight ((m + 1 : ℕ) : ℤ)) : ℂ) *
      boundaryFourier (Φ.pulledBackTrace Φ.lipschitzDomain u) ((m + 1 : ℕ) : ℤ) - _ = _
  rw [hweight, boundaryFourier_apply]
  simpa [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff, diskMassForcingScale, mul_assoc] using hn

theorem localConformal_forced_principal_mode_neg :
    Φ.pulledBackHalfTrace Φ.lipschitzDomain u (-((m + 1 : ℕ) : ℤ)) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b (-((m + 1 : ℕ) : ℤ)) =
        diskMassForcingCoeff (Φ.massForcing Φ.lipschitzDomain Φ.deriv_upper q)
          (-((m + 1 : ℕ) : ℤ)) := by
  have hw := localConformal_forced_weak_antiholomorphic_mode Φ b u q hu (m + 1)
  have hweight : sobWeight (-((m + 1 : ℕ) : ℤ)) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring
  have hs : fourierScale ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity :
    ((m + 1 : ℕ) : ℝ) ≠ 0)
  have hs2 : fourierScale ^ 2 = (anglePeriod : ℂ) := by
    exact_mod_cast Real.sq_sqrt two_pi_pos.le
  have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ))
  rw [hweight] at hw
  have hn := normalize_forced_weak_mode hs hk
    (by simpa only [hs2, Complex.ofReal_natCast] using hw)
  rw [ht2] at hn
  have hi : -((m + 1 : ℕ) : ℤ) = Int.negSucc m := by omega
  rw [localConformalDiskHalfTrace_apply]
  change (Real.sqrt (sobWeight (-((m + 1 : ℕ) : ℤ))) : ℂ) *
      boundaryFourier (Φ.pulledBackTrace Φ.lipschitzDomain u) (-((m + 1 : ℕ) : ℤ)) - _ = _
  rw [hweight, boundaryFourier_apply, hi]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff,
    diskMassForcingScale, hi, mul_assoc] using hn

theorem localConformal_forced_principal_mode_ne_zero
    (n : ℤ) (hn : n ≠ 0) :
    Φ.pulledBackHalfTrace Φ.lipschitzDomain u n -
      (((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)) * b n =
        diskMassForcingCoeff (Φ.massForcing Φ.lipschitzDomain Φ.deriv_upper q) n := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact (hn rfl).elim
      | succ m =>
          change Φ.pulledBackHalfTrace Φ.lipschitzDomain u ((m + 1 : ℕ) : ℤ) -
            (((sobWeight ((m + 1 : ℕ) : ℤ) /
              |(((m + 1 : ℕ) : ℤ) : ℝ)| : ℝ) : ℂ)) * b ((m + 1 : ℕ) : ℤ) = _
          rw [forced_principal_ratio_pos]
          exact localConformal_forced_principal_mode_pos Φ b u q hu m
  | negSucc m =>
      have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
      rw [hi]
      simp only [Int.cast_neg]
      rw [forced_principal_ratio_neg]
      exact localConformal_forced_principal_mode_neg Φ b u q hu m

end

end

end PolyaNeumann

end
