module

public import NearlyMinimax.HighCompleteSourceTail


@[expose] public section

/-! The all-count numerator cap for the actual periodic source field.
Frame and amplitude thresholds are fixed before the grid, selector orders,
history, and extension domain. No field/profile/cap premise remains. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

structure HighFrameOriginalLocalGuards (d k D : ℕ) [NeZero k] (Cfr eta rho : ℝ)
    (c : HighWindowLabels d k → HighFrameVector d D) : Prop where
  amplitude_nonneg : 0 ≤ eta
  amplitude_half : eta ≤ rho/2
  coefficient_ball : ∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹
  weight_abs : ∀ j x, |highPeriodicTensor (d := d) (k := k) j x| ≤ 1
  without_abs : ∀ j x, |highLocalFieldWithout eta c j x| ≤ rho/2
  profile_abs : ∀ j (v : HighFrameVector d D), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |∑ γ, highLocalFrameFeature (k := k) j x γ*v γ| ≤ 1
  regression_abs : ∀ j (v : HighFrameVector d D), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |highLocalFieldWithout eta c j x + eta*highPeriodicTensor j x*
      (∑ γ, highLocalFrameFeature j x γ*v γ)| ≤ rho

theorem highFrame_original_local_guards {d : ℕ} {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ Cfr cf,
      Cfr0 ≤ Cfr → 0 ≤ cf → cf*k^(-C.smoothness) ≤ eta0 →
      ∀ c,
      (∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹) →
      HighFrameOriginalLocalGuards d k D Cfr (cf*k^(-C.smoothness)) Q.ρ c := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let eta0 := Q.ρ/(2*(2^d+1))
  refine ⟨Cfr0,eta0,hfr0,div_pos Q.ρ_pos (by positivity),?_⟩
  intro k D hk0 hk Cfr cf hfr hcf heta c hc
  letI := hk0
  let eta := cf*k^(-C.smoothness)
  have hfr1  := hfr0.trans hfr
  have hen : 0 ≤ eta := by positivity
  have hamp : (2^d+1)*eta ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ (by positivity)).mp heta
    nlinarith
  have hehalf : eta ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (j) : frameCoefficientL1 (highFramePolynomial (c j)) ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (hc j).trans ((inv_le_inv₀ (by linarith) (by linarith)).mpr hfr)
  have hF := (hfield k hk0 hk cf hcf (highFramePolynomial ∘ c) hP).1
  have hw (j) (x) : |highPeriodicTensor (d := d) (k := k) j x| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg j x)]
    exact highPeriodicTensor_le_one (by omega) j x
  have hprof (j) (v : HighFrameVector d D) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x)  :=
    highLocalFrameFeature_ball_abs_le_one (k := k) j x hfr1 hv
  have hterm (j) (v : HighFrameVector d D) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |eta*highPeriodicTensor j x*(∑ γ, highLocalFrameFeature (k := k) j x γ*v γ)| ≤ eta := by
    rw [abs_mul,abs_mul,abs_of_nonneg hen]
    have ht := mul_le_mul (hw j x) (hprof j v hv x) (abs_nonneg _) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left ht hen]
  have hg (j) (x) : |highLocalFieldWithout eta c j x| ≤ Q.ρ/2 := by
    have hd := highFrameField_local_decomposition hk eta c j x
    have he : highLocalFieldWithout eta c j x =
        highFrameField k eta (fun l => highFramePolynomial (c l)) x -
          eta*highPeriodicTensor j x*(∑ γ, highLocalFrameFeature j x γ*c j γ) := by
      linarith [hd]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hF x) (hterm j (c j) (hc j) x)).trans
      (by nlinarith only [hamp]))
  refine ⟨hen,hehalf,hc,hw,hg,hprof,?_⟩
  intro j v hv x
  exact (abs_add_le _ _).trans (by linarith only [hg j x,hterm j v hv x,hehalf])

variable {d : ℕ} [NeZero d] {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C)

theorem completeSource_original_local_guards :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ M →
      ∀ Cfr lam ell N mu cf, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf*k^(-C.smoothness) ≤ eta0 →
      ∀ h,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      HighFrameOriginalLocalGuards d k D Cfr (cf*k^(-C.smoothness)) Q.ρ
        (highUnionSourceState C R h).2 := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hguards⟩ := highFrame_original_local_guards Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have G := completeSourceRows_guards k hD hq hM lam mu
    (hfr0.trans hfr) hell hellN
  exact hguards k D hk0 hk Cfr cf hfr hcf heta (highUnionSourceState C R h).2
    (highUnionSourceState_coefficient_ball C R G h)

end NearlyMinimax
