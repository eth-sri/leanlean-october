module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalWeakModes

/-!
# Actual conformal harmonic coefficients with an independent mass forcing

The weak equation may contain a physical H¹ vector `q` distinct from its
solution `u`. Physical inverse-coordinate tests identify the mass term with
the actual Jacobian-weighted forcing of `q`, including for projected regular
solutions and resonant vectors.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

/-- The genuine normalized weak equation with an independent physical mass
forcing vector. -/
def IsNormalizedNeumannForcedSolution {Ω : PlanarSet}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (b : L2Z) (u q : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      ⟪h1Value Ω v, h1Value Ω q⟫_ℂ = ⟪Q v, b⟫_ℂ

private theorem forced_halfTrace_pullback_apply  hR F
    (hFs : RealSmoothOnBall F R)
    hL
    v :
    localConformalDiskHalfTrace hR F hFs hL v =
      diskHalfTrace (localConformalH1Pullback hR F hFs hL v) :=
  ContinuousLinearMap.comp_apply diskHalfTrace (localConformalH1Pullback hR F hFs hL) v

private theorem normalize_forced_weak_mode {s t k a I b : ℂ}
    (hs : s ≠ 0) (hk : k ≠ 0)
    (h : s ^ 2 * k * a - I = t * s * b) :
    t * s * a - (t ^ 2 / k) * b = (t / (s * k)) * I := by
  grind

private theorem forced_principal_ratio_pos m :
    (((sobWeight ((m + 1 : ℕ) : ℤ) /
        |(((m + 1 : ℕ) : ℤ) : ℝ)| : ℝ) : ℂ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight,  Int.cast_natCast,  Nat.abs_cast]
    push_cast
    ring
  grind only [PolyaNeumann.sobWeight]

private theorem forced_principal_ratio_neg m :
    (((sobWeight (-((m + 1 : ℕ) : ℤ)) /
        |((-((m + 1 : ℕ) : ℤ)) : ℝ)| : ℝ) : ℂ)) =
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  simpa only [sobWeight, Int.cast_neg, abs_neg] using forced_principal_ratio_pos m


section

variable {R } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) {C K }
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
local notation "diskHalfTraceFixed" => localConformalDiskHalfTrace hR F hFs hL


section
variable (b ) (u q ) (hu : IsNormalizedNeumannForcedSolution
      (localConformalDiskHalfTrace hR F hFs hL) b u q)
local notation "massForcingFixed" => localConformalMassForcing hR F hFs hL hK q

include b u q hu

section
include hb hhol hinj hC e he hsource hes

theorem localConformal_forced_weak_holomorphic_mode (m : ℕ) :
    (2 * π : ℂ) * (m : ℂ) *
      fourierCoeffOn two_pi_pos (localConformalDiskH1Trace hR F hFs hL u : ComplexCurve) (m : ℤ) -
        (∫ z in unitDisk,
          (massForcingFixed : PlaneMap) z * conj z ^ m) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt circlePeriod : ℂ)) * b (m : ℤ) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC
    e he hsource hes (contDiff_diskHolomorphicMode m)
  have hp' : localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' unitDisk) f) = diskHolomorphicH1Test m := hp
  have hg := localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC
    (smoothTraceH1 (F '' ball 0 1) f) u
  have hm := localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK
    (smoothTraceH1 (F '' ball 0 1) f) q
  have htrace : diskHalfTraceFixed
      (smoothTraceH1 (F '' unitDisk) f) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt circlePeriod : ℂ)) • stdBasisZ (m : ℤ) := by
    rw [forced_halfTrace_pullback_apply, hp']
    exact diskHalfTrace_holomorphicTest m
  have hw := hu (smoothTraceH1 (F '' ball 0 1) f)
  rw [← hg, hm, hp', disk_gradient_form_holomorphicTest,
    h1Value_diskHolomorphicH1Test, inner_diskHolomorphicArea_eq_integral, htrace] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw

theorem localConformal_forced_weak_antiholomorphic_mode (m : ℕ) :
    (2 * π : ℂ) * (m : ℂ) *
      fourierCoeffOn two_pi_pos (localConformalDiskH1Trace hR F hFs hL u : ComplexCurve) (-(m : ℤ)) -
        (∫ z in unitDisk,
          (massForcingFixed : PlaneMap) z * z ^ m) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt circlePeriod : ℂ)) * b (-(m : ℤ)) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test hR F hFs hb hL hhol hinj hC
    e he hsource hes (contDiff_diskAntiholomorphicMode m)
  have hp' : localConformalH1Pullback hR F hFs hL
      (smoothTraceH1 (F '' unitDisk) f) = diskAntiholomorphicH1Test m := hp
  have hg := localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC
    (smoothTraceH1 (F '' ball 0 1) f) u
  have hm := localConformal_mass_pairing hR F hFs hb hL hhol hinj hC hK
    (smoothTraceH1 (F '' ball 0 1) f) q
  have htrace : diskHalfTraceFixed
      (smoothTraceH1 (F '' unitDisk) f) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt circlePeriod : ℂ)) • stdBasisZ (-(m : ℤ)) := by
    rw [forced_halfTrace_pullback_apply, hp']
    exact diskHalfTrace_antiholomorphicTest m
  have hw := hu (smoothTraceH1 (F '' ball 0 1) f)
  rw [← hg, hm, hp', disk_gradient_form_antiholomorphicTest,
    h1Value_diskAntiholomorphicH1Test, inner_diskAntiholomorphicArea_eq_integral, htrace] at hw
  simp only [inner_smul_left, stdBasisZ_apply, lp.inner_single_left,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal, map_one, one_mul] at hw
  exact hw

theorem localConformal_forced_principal_mode_pos m :
    diskHalfTraceFixed u ((m + 1 : ℕ) : ℤ) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b ((m + 1 : ℕ) : ℤ) =
        diskMassForcingCoeff massForcingFixed
          ((m + 1 : ℕ) : ℤ) := by
  have hw := localConformal_forced_weak_holomorphic_mode hR F hFs hb hL hhol hinj hC hK
    e he hsource hes b u q hu (m + 1)
  have hweight : sobWeight ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight,  Int.cast_natCast,  Nat.abs_cast]
    push_cast
    ring
  have hs : (Real.sqrt circlePeriod : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity :
    ((m + 1 : ℕ) : ℝ) ≠ 0)
  have hs2 : (Real.sqrt circlePeriod : ℂ) ^ 2 = (2 * π : ℂ) := by
    exact_mod_cast Real.sq_sqrt two_pi_pos.le
  have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity)
  rw [hweight] at hw
  have hn := normalize_forced_weak_mode hs hk
    (by simpa only [hs2, Complex.ofReal_natCast] using hw)
  rw [ht2] at hn
  change (Real.sqrt (sobWeight ((m + 1 : ℕ)))) *
      boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) ((m + 1 : ℕ)) - _ = _
  rw [hweight, boundaryFourier_apply]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff,
    diskMassForcingScale, mul_assoc] using hn

theorem localConformal_forced_principal_mode_neg m :
    diskHalfTraceFixed u (-((m + 1 : ℕ) : ℤ)) -
      ((((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b (-((m + 1 : ℕ) : ℤ)) =
        diskMassForcingCoeff massForcingFixed
          (-((m + 1 : ℕ) : ℤ)) := by
  have hw := localConformal_forced_weak_antiholomorphic_mode hR F hFs hb hL hhol hinj hC hK
    e he hsource hes b u q hu (m + 1)
  have hweight : sobWeight (-((m + 1 : ℕ) : ℤ)) = ((m + 2 : ℕ) : ℝ) := by
    simp only [sobWeight, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    push_cast
    ring
  have hs : (Real.sqrt circlePeriod : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hk : (((m + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity :
    ((m + 1 : ℕ) : ℝ) ≠ 0)
  have hs2 : (Real.sqrt circlePeriod : ℂ) ^ 2 = (2 * π : ℂ) := by
    exact_mod_cast Real.sq_sqrt two_pi_pos.le
  have ht2 : (Real.sqrt ((m + 2 : ℕ) : ℝ) : ℂ) ^ 2 = (((m + 2 : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity)
  rw [hweight] at hw
  have hn := normalize_forced_weak_mode hs hk
    (by simpa only [hs2, Complex.ofReal_natCast] using hw)
  rw [ht2] at hn
  have hi : -((m + 1 : ℕ) : ℤ) = Int.negSucc m := by omega
  change (Real.sqrt (sobWeight (-((m + 1 : ℕ) : ℤ)))) *
      boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) (-((m + 1 : ℕ))) - _ = _
  rw [hweight, boundaryFourier_apply, hi]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff,
    diskMassForcingScale, hi, mul_assoc] using hn

theorem localConformal_forced_principal_mode_ne_zero n (hn : n ≠ 0) :
    diskHalfTraceFixed u n -
      (((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)) * b n =
        diskMassForcingCoeff massForcingFixed n := by
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact (hn rfl).elim
      | succ m =>
          change diskHalfTraceFixed u ((m + 1)) -
            (((sobWeight ((m + 1 : ℕ) : ℤ) /
              |(((m + 1 : ℕ) : ℤ) : ℝ)| : ℝ))) * b ((m + 1)) = _
          rw [forced_principal_ratio_pos]
          exact localConformal_forced_principal_mode_pos hR F hFs hb hL hhol hinj hC hK
            e he hsource hes b u q hu m
  | negSucc m =>
      have hi : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
      rw [hi]
      simp only [Int.cast_neg]
      rw [forced_principal_ratio_neg]
      exact localConformal_forced_principal_mode_neg hR F hFs hb hL hhol hinj hC hK
        e he hsource hes b u q hu m

end


end


end

end PolyaNeumann

end
