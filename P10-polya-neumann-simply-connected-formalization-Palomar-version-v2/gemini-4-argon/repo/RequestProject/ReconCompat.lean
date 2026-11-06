module

public import RequestProject.ReconBasic

/-!
# Compatible traces annihilate the plane waves on the energy circle

If `h` is a compatible trace at energy `E > 0` (orthogonal to the conormal traces of all
Herglotz waves), then the double-layer pairing of `h` with every plane wave
`ePlane ξ`, `4π²|ξ|² = E`, vanishes (`doubleLayer_ePlane_eq_zero`).

The proof writes the Herglotz conormal trace as a superposition of the conormal traces of
plane waves, exchanges the integrals (Fubini), and tests the resulting continuous function
of the direction against itself.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {μ : Measure ℝ} {Q : ℝ → ℝ → ℂ}

/-- The conormal derivative `D(planeWave k · φ)(γ θ)(-i γ'(θ))` of a single plane wave. -/
def pwQ (k : ℝ) (γ : ℝ → ℂ) (θ φ : ℝ) : ℂ :=
  planeWave k (γ θ) φ * ((k / 2 : ℂ) * (conj (deriv γ θ) * Complex.exp (φ * Complex.I) -
    deriv γ θ * Complex.exp (-(φ * Complex.I))))

lemma norm_exp_mul_I' (φ : ℝ) : ‖Complex.exp (φ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I φ

lemma norm_pwQ_le k γ θ φ : ‖pwQ k γ θ φ‖ ≤ |k| * ‖deriv γ θ‖ := by
  unfold pwQ
  rw [norm_mul, norm_planeWave, one_mul, norm_mul]
  rw [show ‖(k / 2 : ℂ)‖ = |k| / 2 by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]; norm_num]
  calc _
      ≤ |k| / 2 * (‖deriv γ θ‖ + ‖deriv γ θ‖) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, norm_exp_mul_I', norm_exp_neg_mul_I, mul_one]
    _ = |k| * ‖deriv γ θ‖ := by ring

lemma continuous_pwQ k γ θ : Continuous (pwQ k γ θ) := by
  unfold pwQ
  exact (continuous_planeWave k _).mul (by fun_prop)

lemma measurable_pwQ k  (hγ : Continuous γ) :
    Measurable (Function.uncurry (pwQ k γ)) := by
  have h2 : Measurable fun p : ℝ × ℝ => deriv γ p.1 := (measurable_deriv γ).comp measurable_fst
  exact (show Continuous fun p : ℝ × ℝ => planeWave k (γ p.1) p.2 by
    unfold planeWave; fun_prop).measurable.mul (measurable_const.mul
    (((Complex.continuous_conj.measurable.comp h2).mul (show Continuous fun p : ℝ × ℝ => Complex.exp (p.2 * Complex.I) by fun_prop).measurable).sub (h2.mul (show Continuous fun p : ℝ × ℝ => Complex.exp (-(p.2 * Complex.I)) by fun_prop).measurable)))

/-- The Herglotz conormal trace is the superposition of the plane-wave conormal traces. -/
lemma fderiv_ePlane_apply (k ψ : ℝ) z w :
    fderiv ℝ (ePlane (-(((k / (2 * π) : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)))) z w =
      conj ((planeWave k z ψ * -(Complex.I * k)) * reMulCLM ψ w) := by
  have hfun : ePlane (-((k / (2 * π) : ℝ) * Complex.exp (ψ * Complex.I))) =
      fun z => Complex.conjCLE.toContinuousLinearMap (planeWave k z ψ) :=
    funext fun z => (show ePlane (-((k / (2 * π) : ℝ) * Complex.exp (ψ * Complex.I))) z = conj (planeWave k z ψ) by
      unfold ePlane planeWave
      rw [← Complex.exp_conj]
      congr 1
      rw [show (conj z * -((k / (2 * π) : ℝ) * Complex.exp (ψ * Complex.I))).re = -(k / (2 * π)) * (z * Complex.exp (-(ψ * Complex.I))).re by
        rw [← Complex.conj_re, map_mul, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal, show conj (Complex.exp (ψ * Complex.I)) = Complex.exp (-(ψ * Complex.I)) by
          rw [← Complex.exp_conj]; simp]
        simp only [mul_neg, Complex.neg_re]
        rw [mul_left_comm, Complex.re_ofReal_mul]
        ring]
      simp
      have hπ : π ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp)
  have hd' := ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := planeWave k z ψ)).comp z (hasFDerivAt_planeWave k z ψ)).fderiv
  simp only [Function.comp_def] at hd'
  rw [hfun, hd']
  simp

lemma fderiv_ePlane_conormal (k ψ : ℝ) γ θ :
    fderiv ℝ (ePlane (-(((k / (2 * π) : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)))) (γ θ)
      (-(Complex.I * deriv γ θ)) = conj (pwQ k γ θ ψ) := by
  rw [fderiv_ePlane_apply, reMulCLM_apply]
  congr 1
  rw [show conj (Complex.exp (-(ψ * Complex.I))) = Complex.exp (ψ * Complex.I) by
    rw [← Complex.exp_conj]; simp]
  simp [pwQ]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem recon_continuous_kernel_pairing 
      
    (hQm : Measurable (Function.uncurry Q)) (hQc : ∀ θ, Continuous (Q θ))
    (hQb : ∀ θ φ, ‖Q θ φ‖ ≤ B) (hhi : Integrable h μ) :
    Continuous (fun φ => ∫ θ, conj (Q θ φ) * h θ ∂μ) := by
  have hQθ φ : Measurable (fun θ => Q θ φ) :=
    hQm.comp (measurable_id.prodMk measurable_const)
  refine continuous_of_dominated (bound := fun θ => B * ‖h θ‖)
    (fun φ => ((Complex.continuous_conj.measurable.comp (hQθ φ)).aestronglyMeasurable).mul
      hhi.aestronglyMeasurable)
    (fun φ => Eventually.of_forall fun θ => ?_) (hhi.norm.const_mul B)
    (Eventually.of_forall fun θ =>
      (Complex.continuous_conj.comp (hQc θ)).mul continuous_const)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (hQb θ φ) (norm_nonneg _)

private theorem recon_pairing_integral_swap  [SFinite μ]
      
    (hQm : Measurable (Function.uncurry Q)) (hQb : ∀ θ φ, ‖Q θ φ‖ ≤ B)
    (hhi : Integrable h μ) (hai : Integrable a μ) :
    (∫ θ, ∫ φ, conj (a φ) * (conj (Q θ φ) * h θ) ∂μ ∂μ) =
      ∫ φ, conj (a φ) * (∫ θ, conj (Q θ φ) * h θ ∂μ) ∂μ := by
  rw [integral_integral_swap (show Integrable (fun p : ℝ × ℝ => conj (a p.2) * (conj (Q p.1 p.2) * h p.1)) (μ.prod μ) by
    refine Integrable.mono' ((hhi.norm.const_mul B).mul_prod hai.norm) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable
        hai.aestronglyMeasurable.comp_snd).mul
        ((Complex.continuous_conj.measurable.comp hQm).aestronglyMeasurable.mul
          hhi.aestronglyMeasurable.comp_fst)
    · simp
      calc
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hQb p.1 p.2) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring)]
  apply integral_congr_ae
  filter_upwards [] with φ
  exact integral_const_mul _ _

private theorem recon_herglotz_pairing_superposition {a : ℝ → ℂ} (ha : IsDirDensity a)
    (k : ℝ) (γ h : ℝ → ℂ) (θ : ℝ) :
    conj (herglotzConormal k a γ θ) * h θ = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ φ in Ioc 0 (2 * π), conj (a φ) * (conj (pwQ k γ θ φ) * h θ) := by
  have h_inl k γ θ : herglotzConormal k a γ θ = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in 0..(2 * π), a φ * pwQ k γ θ φ := by
    rw [herglotzConormal_eq ha.intervalIntegrable, herglotzCoeff, herglotzCoeff, show ∫ φ in 0..(2 * π), a φ * pwQ k γ θ φ = k / 2 * (conj (deriv γ θ) * (∫ φ in 0..(2 * π), Complex.exp (-((-1 : ℤ) * φ * Complex.I)) * (a φ * planeWave k (γ θ) φ)) - deriv γ θ * ∫ φ in (0 : ℝ)..(2 * π), Complex.exp (-((1 : ℤ) * φ * Complex.I)) * (a φ * planeWave k (γ θ) φ)) by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub ((intervalIntegrable_herglotz ha.intervalIntegrable k (-1) (γ θ)).const_mul _) ((intervalIntegrable_herglotz ha.intervalIntegrable k 1 (γ θ)).const_mul _),
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun φ _ => ?_
      have e1 : Complex.exp (-((-1 : ℤ) * φ * Complex.I)) = Complex.exp (φ * Complex.I) := by
        congr 1; push_cast; ring
      have e2 : Complex.exp (-((1 : ℂ) * φ * Complex.I)) =
          Complex.exp (-(φ * Complex.I)) := by
        congr 1; ring
      simp [pwQ]
      ring]
    ring
  rw [h_inl,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, map_mul, map_inv₀,
    Complex.conj_ofReal, ← integral_conj, mul_assoc, ← integral_mul_const]
  congr 2
  funext φ
  rw [map_mul]
  ring

private theorem recon_continuous_dirDensity  (hGc : Continuous G) :
    IsDirDensity G := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc 0 (2 * π))) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hGc.continuousOn (s := Icc 0 (2 * π)))
  refine MemLp.of_bound hGc.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with φ hφ
  exact hM φ (Ioc_subset_Icc_self hφ)

private theorem recon_continuous_zero_of_self_pairing {G : ℝ → ℂ}
    (hGc : Continuous G)
    (hsq : (∫ φ in Ioc 0 (2 * π), conj (G φ) * G φ) = 0) :
    ∀ φ ∈ Icc 0 (2 * π), G φ = 0 := by
  have hsq' : (∫ φ in 0..(2 * π), ‖G φ‖ ^ 2) = 0 := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rw [show (∫ φ in Ioc 0 (2 * π), conj (G φ) * G φ) = (∫ φ in Ioc 0 (2 * π), ‖G φ‖ ^ 2 : ℝ) by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [] with φ
      rw [Complex.conj_mul']
      push_cast
      ring] at hsq
    exact_mod_cast hsq
  intro φ hφ
  by_contra hne
  have hpos := intervalIntegral.integral_pos Real.two_pi_pos
    (f := fun φ => ‖G φ‖ ^ 2) (hGc.norm.pow 2).continuousOn
    (fun _ _ => by positivity)
    ⟨φ, hφ, by have := norm_pos_iff.mpr hne; positivity⟩
  linarith

private theorem recon_energy_circle_direction  
    (hξn : ‖ξ‖ = k / (2 * π)) :
    ∃ ψ ∈ Icc 0 (2 * π),
      ξ = -(((k / (2 * π) : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) := by
  have hrep :=
    Complex.norm_mul_exp_arg_mul_I (-ξ)
  rw [norm_neg, hξn] at hrep
  rcases le_or_gt 0 (Complex.arg (-ξ)) with h0 | h0
  · refine ⟨Complex.arg (-ξ), ⟨h0, ?_⟩, ?_⟩
    · linarith [Complex.arg_le_pi (-ξ), Real.pi_pos]
    · rw [hrep, neg_neg]
  · refine ⟨Complex.arg (-ξ) + 2 * π,
      ⟨by linarith [Complex.neg_pi_lt_arg (-ξ)], by linarith⟩, ?_⟩
    rw [show Complex.exp ((Complex.arg (-ξ) + 2 * π : ℝ) * Complex.I) = Complex.exp ((Complex.arg (-ξ)) * Complex.I) by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one], hrep, neg_neg]

/-- Compatible traces annihilate the plane waves `e^{-2πi⟨z, ξ⟩}` with `4π²|ξ|² = E`. -/
theorem doubleLayer_ePlane_eq_zero {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) 
    (hE : 0 < E) {h : ℝ → ℂ} (hh : h ∈ compatibleTraces γ E) {ξ : ℂ}
    (hξ : 4 * π ^ 2 * ‖ξ‖ ^ 2 = E) : doubleLayer γ h (ePlane ξ) = 0 := by
  obtain ⟨⟨Kh, hKh⟩, -, hcomp⟩ := hh
  set k := Real.sqrt E with hk
  set μ := volume.restrict (Ioc 0 (2 * π)) with hμ
  have h2π : 0 < 2 * π := by positivity
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hhi : Integrable h μ := hKh.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hQm := measurable_pwQ k hK.continuous
  have hbd : ∀ θ φ, ‖pwQ k γ θ φ‖ ≤ |k| * K := fun θ φ =>
    (norm_pwQ_le k γ θ φ).trans (by gcongr; exact norm_deriv_le_of_lipschitz hK)
  -- the plane-wave pairing as a function of the direction
  set G : ℝ → ℂ := fun φ => ∫ θ, conj (pwQ k γ θ φ) * h θ ∂μ with hG
  have hGc :=
    recon_continuous_kernel_pairing hQm (continuous_pwQ k γ) hbd hhi
  -- Fubini: pairing of a compatible trace with a Herglotz conormal trace
  -- test with `a = G`
  -- represent `ξ` on the circle
  obtain ⟨ψ, hψ, hξψ⟩ := recon_energy_circle_direction (show ‖ξ‖ = k / (2 * π) by
    rw [hk, eq_div_iff h2π.ne', ← hξ]
    rw [show 4 * π ^ 2 * ‖ξ‖ ^ 2 = (‖ξ‖ * (2 * π)) ^ 2 by ring,
      Real.sqrt_sq (by positivity)])
  -- conclude
  rw [hξψ, doubleLayer, intervalIntegral.integral_of_le h2π.le]
  calc
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with θ
      rw [fderiv_ePlane_conormal, mul_comm]
    _ = 0 := (recon_continuous_zero_of_self_pairing hGc ((show ∀ a, IsDirDensity a → ∫ φ, conj (a φ) * G φ ∂μ = 0 by
      intro a ha
      obtain ⟨-, hz⟩ := hcomp a ha
      rw [intervalIntegral.integral_of_le h2π.le] at hz
      simp_rw [recon_herglotz_pairing_superposition ha k γ h] at hz
      rw [integral_const_mul, mul_eq_zero] at hz
      rcases hz with hz | hz
      · exfalso
        exact inv_ne_zero (by exact_mod_cast h2π.ne') hz
      exact (recon_pairing_integral_swap hQm hbd hhi (ha.integrable (by norm_num))).symm.trans hz) G (recon_continuous_dirDensity hGc))) ψ hψ

end PolyaNeumann
