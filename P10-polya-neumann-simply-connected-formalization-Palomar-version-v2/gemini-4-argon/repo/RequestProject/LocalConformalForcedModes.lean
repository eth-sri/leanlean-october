module

public import RequestProject.LocalConformalWeakModes

/-!
# Actual conformal harmonic coefficients with an independent mass forcing

The weak equation may contain a physical H¹ vector `q` distinct from its
solution `u`. Physical inverse-coordinate tests identify the mass term with
the actual Jacobian-weighted forcing of `q`, including for projected regular
solutions and resonant vectors.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace ContDiff

/-- The genuine normalized weak equation with an independent physical mass
forcing vector. -/
def IsNormalizedNeumannForcedSolution 
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (b : L2Z) (u q : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      ⟪h1Value Ω v, h1Value Ω q⟫_ℂ = ⟪Q v, b⟫_ℂ

private theorem forced_halfTrace_pullback_apply {R : ℝ} (hR : 1 < R) F
    hFs
    hL
    v :
    localConformalDiskHalfTrace hR F hFs hL v =
      diskHalfTrace (localConformalH1Pullback hR F hFs hL v) :=
  ContinuousLinearMap.comp_apply diskHalfTrace (localConformalH1Pullback hR F hFs hL) v

private theorem normalize_forced_weak_mode {s t k a I b : ℂ}
    (hs : s ≠ 0) (hk : k ≠ 0)
    (h : s ^ 2 * k * a - I = t * s * b) :
    t * s * a - (t ^ 2 / k) * b = t / (s * k) * I := by
  calc
    _ = t / (s * k) * (s ^ 2 * k * a - t * s * b) := by
      field_simp [hs, hk]
    _ = _ := by rw [← (show I = s ^ 2 * k * a - t * s * b by linear_combination -h)]

private theorem forced_principal_ratio_pos m :
    (((sobWeight ((m + 1 : ℕ) : ℤ) /
        |(((m + 1 : ℕ) : ℤ) : ℝ)| : ℝ) : ℂ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  simp only [show sobWeight ((m + 1 : ℕ) : ℤ) = (m + 2 : ℕ) by
    simp only [sobWeight, Int.cast_natCast,
      abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring, Int.cast_natCast,
    abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]

private theorem forced_principal_ratio_neg m :
    (((sobWeight (-((m + 1 : ℕ) : ℤ)) /
        |((-((m + 1 : ℕ) : ℤ)) : ℝ)| : ℝ) : ℂ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  simp only [show sobWeight (-((m + 1 : ℕ) : ℤ)) = (m + 2 : ℕ) by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]
    push_cast
    ring, Int.cast_natCast, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)


local notation "Φ0" => localConformalDiskHalfTrace hR F hFs hL

local notation "Φ1" => ball 0 1

local notation "Φ2" => localConformalDiskH1Trace hR F hFs hL

local notation "Φ3" => exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC e he hsource hes

local notation "Φ4" => localConformalMassForcing hR F hFs hL hK
include hb hhol hinj hC e he hsource hes in
theorem localConformal_forced_weak_holomorphic_mode
    b u q
    (hu : IsNormalizedNeumannForcedSolution
      (Φ0) b u q) (m : ℕ) :
    (2 * π : ℂ) * (m : ℂ) *
      fourierCoeffOn two_pi_pos (Φ2 u : ℝ → ℂ) (m : ℤ) -
        (∫ z in Φ1,
          (Φ4 q : ℂ → ℂ) z * conj z ^ m) =
      (Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt (2 * π) : ℂ) * b (m : ℤ) := by
  obtain ⟨f, _, hp⟩ := Φ3 (contDiff_diskHolomorphicMode m)
  have hp' : localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' Φ1) f) = diskHolomorphicH1Test m := hp
  have hw := hu (smoothTraceH1 (F '' Φ1) f)
  rw [← localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC (smoothTraceH1 (F '' Φ1) f) u, localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK (smoothTraceH1 (F '' Φ1) f) q, hp', disk_gradient_form_holomorphicTest,
    h1Value_diskHolomorphicH1Test, inner_diskHolomorphicArea_eq_integral, show Φ0 (smoothTraceH1 (F '' Φ1) f) = ((Real.sqrt (sobWeight m) : ℂ) * (Real.sqrt (2 * π))) • stdBasisZ m by
      rw [forced_halfTrace_pullback_apply, hp']
      exact diskHalfTrace_holomorphicTest m] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw

include hb hhol hinj hC e he hsource hes in
theorem localConformal_forced_weak_antiholomorphic_mode
    b u q
    (hu : IsNormalizedNeumannForcedSolution
      (Φ0) b u q) (m : ℕ) :
    (2 * π : ℂ) * (m : ℂ) *
      fourierCoeffOn two_pi_pos (Φ2 u : ℝ → ℂ) (-(m : ℤ)) -
        (∫ z in Φ1,
          (Φ4 q : ℂ → ℂ) z * z ^ m) =
      (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt (2 * π) : ℂ) * b (-(m : ℤ)) := by
  obtain ⟨f, _, hp⟩ := Φ3 (contDiff_diskAntiholomorphicMode m)
  have hp' : localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' Φ1) f) = diskAntiholomorphicH1Test m := hp
  have hw := hu (smoothTraceH1 (F '' Φ1) f)
  rw [← localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC (smoothTraceH1 (F '' Φ1) f) u, localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK (smoothTraceH1 (F '' Φ1) f) q, hp', disk_gradient_form_antiholomorphicTest,
    h1Value_diskAntiholomorphicH1Test, inner_diskAntiholomorphicArea_eq_integral, show Φ0 (smoothTraceH1 (F '' Φ1) f) = ((Real.sqrt (sobWeight (-m)) : ℂ) * (Real.sqrt (2 * π))) • stdBasisZ (-m) by
      rw [forced_halfTrace_pullback_apply, hp']
      exact diskHalfTrace_antiholomorphicTest m] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw



include hb hhol hinj hC e he hsource hes in
theorem localConformal_forced_principal_mode_ne_zero
    b u q
    (hu : IsNormalizedNeumannForcedSolution
      (Φ0) b u q) n (hn : n ≠ 0) :
    Φ0 u n -
      ((sobWeight n / |(n : ℝ)| : ℝ) : ℂ) * b n =
        diskMassForcingCoeff (Φ4 q) n := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact (hn rfl).elim
      | succ m =>
          change Φ0 u ((m + 1 : ℕ) : ℤ) -
            ((sobWeight ((m + 1 : ℕ) : ℤ) /
              |(((m + 1 : ℕ) : ℤ) : ℝ)| : ℝ) : ℂ) * b ((m + 1 : ℕ) : ℤ) = _
          rw [forced_principal_ratio_pos]
          have hw := localConformal_forced_weak_holomorphic_mode hR F hFs hb hL hhol hinj hC hK
            e he hsource hes b u q hu (m + 1)
          have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = (m + 2 : ℕ) := by
            simp only [sobWeight, Int.cast_natCast, abs_of_nonneg (by positivity :
              0 ≤ ((m + 1 : ℕ) : ℝ))]
            push_cast
            ring
          rw [hweight] at hw
          have hn := normalize_forced_weak_mode (show (Real.sqrt (2 * π) : ℂ) ≠ 0 by
            exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne') (show (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 by
            exact_mod_cast (by positivity :
            ((m + 1 : ℕ) : ℝ) ≠ 0))
            (by simpa only [(show (Real.sqrt (2 * π) : ℂ) ^ 2 = (2 * π : ℂ) by
              exact_mod_cast Real.sq_sqrt two_pi_pos.le), Complex.ofReal_natCast] using hw)
          rw [show (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = ((m + 2 : ℕ) : ℝ) by
            exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ ((m + 2 : ℕ) : ℝ))] at hn
          rw [localConformalDiskHalfTrace_apply]
          change Real.sqrt (sobWeight ((m + 1 : ℕ) : ℤ)) *
              boundaryFourier (Φ2 u) (m + 1 : ℕ) - _ = _
          rw [hweight, boundaryFourier_apply]
          simpa [diskMassForcingCoeff, diskMassForcingScale, mul_assoc] using hn
  | negSucc m =>
      rw [show Int.negSucc m = -((m + 1 : ℕ) : ℤ) by omega]
      simp only [Int.cast_neg]
      rw [forced_principal_ratio_neg]
      have hw := localConformal_forced_weak_antiholomorphic_mode hR F hFs hb hL hhol hinj hC hK
        e he hsource hes b u q hu (m + 1)
      have hweight : sobWeight (-((m + 1 : ℕ) : ℤ)) = (m + 2 : ℕ) := by
        simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
          abs_of_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]
        push_cast
        ring
      rw [hweight] at hw
      have hn := normalize_forced_weak_mode (show (Real.sqrt (2 * π) : ℂ) ≠ 0 by
        exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne') (show (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 by
        exact_mod_cast (by positivity :
        ((m + 1 : ℕ) : ℝ) ≠ 0))
        (by simpa only [(show (Real.sqrt (2 * π) : ℂ) ^ 2 = (2 * π : ℂ) by
          exact_mod_cast Real.sq_sqrt two_pi_pos.le), Complex.ofReal_natCast] using hw)
      rw [show (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = ((m + 2 : ℕ) : ℝ) by
        exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ ((m + 2 : ℕ) : ℝ))] at hn
      have hi : -(m + 1 : ℕ) = Int.negSucc m := by omega
      rw [localConformalDiskHalfTrace_apply]
      change Real.sqrt (sobWeight (-((m + 1 : ℕ) : ℤ))) *
          boundaryFourier (Φ2 u) (-(m + 1 : ℕ)) - _ = _
      rw [hweight, boundaryFourier_apply, hi]
      simpa only [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff,
        diskMassForcingScale, hi, mul_assoc] using hn

end

end PolyaNeumann

end
