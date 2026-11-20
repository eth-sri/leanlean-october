/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianJets
public import DOZZ.Hypergeom.ClassificationCanonicalHermitian
public import DOZZ.Hypergeom.ClassificationCutCrossingBranch
public import DOZZ.Hypergeom.ClassificationMonodromy
public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! Matching values and first Wirtinger derivatives across the negative cut. -/

@[expose] public section

open Filter
open scoped Topology

namespace DOZZ.Proofs

private noncomputable def gaussNegativeCrossingCenter : ℂ := -1 / 2

private def gaussNegativeCrossingLowerSet : Set ℂ :=
  gaussNegativeCrossingDisk ∩ {z : ℂ | z.im < 0}

private theorem gaussNegativeCrossingLowerSet_isOpen :
    IsOpen gaussNegativeCrossingLowerSet := gaussNegativeCrossingDisk_isOpen.inter (isOpen_Iio.preimage Complex.continuous_im)

private theorem gaussNegativeCrossingDisk_subset_regularPlane :
    gaussNegativeCrossingDisk ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  have hx := gaussNegativeCrossingDisk_real_bounds hz
  constructor
  · intro he
    have hre : z.re = 0 := by rw [he]; simp
    linarith
  · intro he
    have hre : z.re = 1 := by rw [he]; simp
    linarith

private theorem gaussNegativeCrossingPhase_star
    (c : ℝ) :
    star (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) =
      Complex.exp (-((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) := by
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_sub, map_one]
  ring_nf

private theorem gaussNegativeCrossingPhase_star_mul_self
    (c : ℝ) :
    star (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ))) = 1 := by
  rw [gaussNegativeCrossingPhase_star, ← Complex.exp_add, show -((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ))) +
        (2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)) = 0 by ring, Complex.exp_zero]

private theorem gaussNegativeCrossingCenter_mem :
    gaussNegativeCrossingCenter ∈ gaussNegativeCrossingDisk :=
  Metric.mem_ball_self (by norm_num)

/-- Lift a one-sided real approach to the crossing point along its vertical line. -/
private theorem gaussNegativeCrossing_closure {S : Set ℝ} (hS : 0 ∈ closure S) :
    gaussNegativeCrossingCenter ∈ closure (gaussNegativeCrossingDisk ∩ Complex.im ⁻¹' S) := by
  let w (t : ℝ) := gaussNegativeCrossingCenter + (t : ℂ) * Complex.I
  have hw : Continuous w := by dsimp [w]; fun_prop
  have him (t : ℝ) : (w t).im = t := by
    simp [w, gaussNegativeCrossingCenter, Complex.add_im]
  have hm : Set.MapsTo w S (Complex.im ⁻¹' S) := fun t ht => by
    simpa [Set.mem_preimage, him] using ht
  apply gaussNegativeCrossingDisk_isOpen.inter_closure
  exact ⟨gaussNegativeCrossingCenter_mem, by simpa [w] using hm.closure hw hS⟩

private theorem crossing_functions_match_jets_of_eqOn
    {S : Set ℂ} {z : ℂ} (hS : IsOpen S) (hz : z ∈ closure S)
    {F G : ℂ → ℂ}
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z)
    (hEq : ∀ w ∈ S, F w = G w) :
    F z = G z ∧ wirtingerZ F z = wirtingerZ G z := by
  have hfreq := mem_closure_iff_frequently.mp hz
  have hvalueFreq  := hfreq.mono hEq
  have hvalue := tendsto_nhds_unique_of_frequently_eq
    hF.continuousAt.tendsto hG.continuousAt.tendsto hvalueFreq
  have hFz  :=
    differentiableAt_wirtingerZ_of_contDiffAt_two hF
  have hGz  :=
    differentiableAt_wirtingerZ_of_contDiffAt_two hG
  have hderivFreq := hfreq.mono fun w hw => by
      have hnear : F =ᶠ[𝓝 w] G := by
        filter_upwards [hS.mem_nhds hw] with v hv
        exact hEq v hv
      exact wirtingerZ_congr_of_eventuallyEq hnear
  have hderiv := tendsto_nhds_unique_of_frequently_eq
    hFz.continuousAt.tendsto hGz.continuousAt.tendsto hderivFreq
  exact ⟨hvalue, hderiv⟩

/-- The canonical Hermitian tensor of a real Gauss solution has no off-diagonal term. The
negative-cut crossing compares its two local representatives at the seam, including their value
and first `∂z` jet; a nonzero Wronskian then removes the off-diagonal entries. -/
theorem realGaussSolution_canonical_hermitian_offDiagonal_zero
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    ∃ α δ : ℝ, ∃ β : ℂ,
      (∀ z ∈ gaussCutPlane,
        (T z : ℂ) =
          gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
              star ((α : ℂ) * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
                β * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
            gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z *
              star (star β * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
                (δ : ℂ) * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z)) ∧
      β = 0 := by
  obtain ⟨α, δ, β, hrep⟩ :=
    realGaussSolution_canonical_hermitian_representation hH a b c hc T hT
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hc n
    exact_mod_cast hn
  have hcNat : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n hn
    apply hcC (-(n : ℤ))
    exact hn.trans (by simp)
  let f : ℂ → ℂ := gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)
  let g : ℂ → ℂ := gaussNegativeCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ)
  let F : ℂ → ℂ := fun z => (T z : ℂ)
  have hf : AnalyticOnNhd ℂ f gaussNegativeCrossingDisk :=
    gaussFMinus_analyticOnNhd_crossingDisk hH _ _ _ hcNat
  have hg : AnalyticOnNhd ℂ g gaussNegativeCrossingDisk :=
    gaussNegativeCrossingSecond_analyticOnNhd hH _ _ _ hcC
  let z₀ := gaussNegativeCrossingCenter
  have hcenter : z₀ ∈ gaussNegativeCrossingDisk := gaussNegativeCrossingCenter_mem
  have hFcont : ContDiffAt ℝ 2 F z₀ := by
    have hzReg := gaussNegativeCrossingDisk_subset_regularPlane hcenter
    have hTAt := (hT.1 z₀ hzReg).contDiffAt
      (gaussRegularPlane_isOpen.mem_nhds hzReg)
    change ContDiffAt ℝ 2 (fun w => Complex.ofRealCLM (T w)) z₀
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z₀ hTAt
  let phase : ℂ :=
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))
  have hphaseNe : phase ≠ 1 := by
    simpa [phase] using gaussZeroMonodromyPhase_ne_one c hc
  have hphaseUnit : star phase * phase = 1 := by
    dsimp [phase]
    exact gaussNegativeCrossingPhase_star_mul_self c
  have hphase0 : phase ≠ 0 := Complex.exp_ne_zero _
  have hphaseStar : star phase = phase⁻¹ := eq_inv_of_mul_eq_one_left hphaseUnit
  have hphaseInvStar : star (phase⁻¹) = phase := by
    calc
      star (phase⁻¹) = (star phase)⁻¹ := by simp
      _ = (phase⁻¹)⁻¹ := by rw [hphaseStar]
      _ = phase := by simp
  have hphaseMulInvUnit : phase * phase⁻¹ = 1 := mul_inv_cancel₀ hphase0
  let Qup : ℂ → ℂ := hermitianQuadraticTensor f g
    (α : ℂ) (star β) β (δ : ℂ)
  let Bdown : ℂ := star β * phase
  let Cdown : ℂ := β * phase⁻¹
  let Qdown : ℂ → ℂ := hermitianQuadraticTensor f g
    (α : ℂ) Bdown Cdown (δ : ℂ)
  have hUpperEq : ∀ z ∈ gaussNegativeCrossingUpper, F z = Qup z := by
    intro z hz
    have hrepz := hrep z (Or.inl (ne_of_gt hz.2))
    change F z = _ at hrepz
    calc
      F z = _ := hrepz
      _ = Qup z := by
        dsimp [F, Qup, f, g, hermitianQuadraticTensor]
        rw [gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos
          (a : ℂ) (b : ℂ) (c : ℂ) z hz.2]
        simp only [map_add, map_mul, Complex.conj_conj,
          Complex.conj_ofReal]
        ring_nf
  have hLowerEq : ∀ z ∈ gaussNegativeCrossingLowerSet, F z = Qdown z := by
    intro z hz
    have hrepz := hrep z (Or.inl (ne_of_lt hz.2))
    have htrans := gaussNegativeCrossingSecond_eq_phase_mul_gaussFPlus_of_im_neg
      (H := H)
      (a : ℂ) (b : ℂ) (c : ℂ) z hz.2
    have hplus : gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z = phase⁻¹ * g z := by
      change _ = phase⁻¹ * gaussNegativeCrossingSecond H _ _ _ z
      rw [htrans]
      exact (inv_mul_cancel_left₀ hphase0 _).symm
    change F z = _ at hrepz
    calc
      F z = _ := hrepz
      _ = Qdown z := by
        dsimp [F, Qdown, Bdown, Cdown, f, g, hermitianQuadraticTensor]
        rw [hplus]
        simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal]
        rw [show (starRingEnd ℂ) (phase⁻¹) = phase from hphaseInvStar]
        linear_combination ((δ : ℂ) * g z * (starRingEnd ℂ) (g z)) * hphaseMulInvUnit
  have hJetsUp := crossing_functions_match_jets_of_eqOn
    gaussNegativeCrossingUpper_isOpen
    (gaussNegativeCrossing_closure (S := Set.Ioi 0) (by simp [closure_Ioi]))
    hFcont (hermitianQuadraticTensor_contDiffAt_two hf hg _ _ _ _ hcenter) hUpperEq
  have hJetsDown := crossing_functions_match_jets_of_eqOn
    gaussNegativeCrossingLowerSet_isOpen
    (gaussNegativeCrossing_closure (S := Set.Iio 0) (by simp [closure_Iio]))
    hFcont (hermitianQuadraticTensor_contDiffAt_two hf hg _ _ _ _ hcenter) hLowerEq
  have hW : f z₀ * deriv g z₀ -
      deriv f z₀ * g z₀ ≠ 0 := by
    have h := gaussNegativeCrossing_wronskian_ne_zero hH
      (a : ℂ) (b : ℂ) (c : ℂ) hcC z₀ hcenter
    simpa [gaussCramerWronskian, f, g] using h
  have hβHerm : Cdown - β = star (Bdown - star β) := by
    simp only [Bdown, Cdown, star_sub, star_mul, star_star, hphaseStar]
    ring
  have h₀ : (Bdown - star β) * f z₀ *
        star (g z₀) +
      (Cdown - β) * g z₀ *
        star (f z₀) = 0 := by
    have hvalue := hJetsDown.1.symm.trans hJetsUp.1
    simp only [hermitianQuadraticTensor] at hvalue
    linear_combination hvalue
  have h₁ : (Bdown - star β) * deriv f z₀ *
        star (g z₀) +
      (Cdown - β) * deriv g z₀ *
        star (f z₀) = 0 := by
    have hderiv := hJetsDown.2.symm.trans hJetsUp.2
    rw [hermitianQuadraticTensor_wirtingerZ hf hg (α : ℂ) Bdown Cdown (δ : ℂ) hcenter,
      hermitianQuadraticTensor_wirtingerZ hf hg (α : ℂ) (star β) β (δ : ℂ) hcenter] at hderiv
    simp only [hermitianQuadraticTensorZ] at hderiv
    linear_combination hderiv
  have hOffDiag := hermitianOffDiagonal_eq_zero_of_value_and_z_derivative
    (f z₀) (g z₀)
    (deriv f z₀) (deriv g z₀)
    (Bdown - star β) (Cdown - β) hW hβHerm h₀ h₁
  have hphaseInvNe : phase⁻¹ ≠ 1 := by simpa
  have hβfactor : β * (phase⁻¹ - 1) = 0 := by
    simpa only [Cdown, mul_sub, mul_one] using hOffDiag.2
  exact ⟨α, δ, β, hrep, (mul_eq_zero.mp hβfactor).resolve_right (sub_ne_zero.mpr hphaseInvNe)⟩

end DOZZ.Proofs
