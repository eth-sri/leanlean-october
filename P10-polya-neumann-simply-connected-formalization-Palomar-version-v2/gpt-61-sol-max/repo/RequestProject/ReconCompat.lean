module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

/-- The conormal derivative `D(planeWave k · φ)(γ θ)(-i γ'(θ))` of a single plane wave. -/
def pwQ k γ (θ φ : ℝ)  :=
  planeWave k (γ θ) φ * ((k / 2 : ℂ) * (conj (deriv γ θ) * Complex.exp (φ * Complex.I) -
    deriv γ θ * Complex.exp (-(φ * Complex.I))))

lemma norm_exp_mul_I' (φ : ℝ) : ‖Complex.exp (φ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I φ

lemma norm_pwQ_le k γ θ φ : ‖pwQ k γ θ φ‖ ≤ |k| * ‖deriv γ θ‖ := by
  unfold pwQ
  rw [norm_mul, norm_planeWave, one_mul, norm_mul]
  have hk : ‖(k / 2 : ℂ)‖ = |k| / 2 := by
    simp_all
  rw [hk]
  calc |k| / 2 * ‖conj (deriv γ θ) * Complex.exp (φ * Complex.I) -
        deriv γ θ * Complex.exp (-(φ * Complex.I))‖
      ≤ |k| / 2 * (‖deriv γ θ‖ + ‖deriv γ θ‖) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, norm_exp_mul_I', norm_exp_neg_mul_I, mul_one]
    _ = |k| * ‖deriv γ θ‖ := by ring

lemma continuous_pwQ k γ θ : Continuous (pwQ k γ θ) := by
  fun_prop [pwQ]

lemma measurable_pwQ k  (hγ : Continuous γ) :
    Measurable (Function.uncurry (pwQ k γ)) := by
  have h1 : Continuous fun p : ℝ × ℝ => planeWave k (γ p.1) p.2 := by
    unfold planeWave; fun_prop
  have h2 : Measurable fun p : ℝ × ℝ => deriv γ p.1 := (measurable_deriv γ).comp measurable_fst
  have h3 : Continuous fun p : ℝ × ℝ => Complex.exp (p.2 * Complex.I) := by fun_prop
  have h4 : Continuous fun p : ℝ × ℝ => Complex.exp (-(p.2 * Complex.I)) := by fun_prop
  exact h1.measurable.mul (measurable_const.mul
    (((Complex.continuous_conj.measurable.comp h2).mul h3.measurable).sub (h2.mul h4.measurable)))

/-- The Herglotz conormal trace is the superposition of the plane-wave conormal traces. -/
lemma herglotzConormal_eq_integral  (ha : IntervalIntegrable a volume 0 circlePeriod)
    k γ θ :
    herglotzConormal k a γ θ =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, a φ * pwQ k γ θ φ := by
  rw [herglotzConormal_eq ha, herglotzCoeff, herglotzCoeff]
  have h1 := intervalIntegrable_herglotz ha k (-1) (γ θ)
  have h2 := intervalIntegrable_herglotz ha k 1 (γ θ)
  have key : ∫ φ in (0 : ℝ)..circlePeriod, a φ * pwQ k γ θ φ = (k / 2 : ℂ) * (conj (deriv γ θ) *
      (∫ φ in (0 : ℝ)..circlePeriod, Complex.exp (-(((-1 : ℤ) : ℂ) * φ * Complex.I)) *
        (a φ * planeWave k (γ θ) φ)) - deriv γ θ *
      ∫ φ in (0 : ℝ)..circlePeriod, Complex.exp (-(((1 : ℤ) : ℂ) * φ * Complex.I)) *
        (a φ * planeWave k (γ θ) φ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (h1.const_mul _) (h2.const_mul _),
      ← intervalIntegral.integral_const_mul]
    grind only [pwQ]
  rw [key]
  ring

/-- The plane wave `ePlane ξ` on the circle `2π|ξ| = k` is a conjugate plane wave. -/
lemma ePlane_eq_conj_planeWave (k ψ : ℝ) z :
    ePlane (-(((k / circlePeriod : ℝ) : ℂ) * Complex.exp (ψ * Complex.I))) z =
      conj (planeWave k z ψ) := by
  unfold ePlane planeWave
  rw [← Complex.exp_conj]
  have hc : conj (Complex.exp (ψ * Complex.I)) = Complex.exp (-(ψ * Complex.I)) := by
    rw [← Complex.exp_conj]; simp
  have hre : (conj z * -(((k / circlePeriod : ℝ) : ℂ) * Complex.exp (ψ * Complex.I))).re =
      -(k / circlePeriod) * (z * Complex.exp (-(ψ * Complex.I))).re := by
    rw [← Complex.conj_re, map_mul, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal, hc]
    simp only [mul_neg, Complex.neg_re]
    rw [mul_left_comm, Complex.re_ofReal_mul]
    ring
  rw [hre]
  simp  
  push_cast
  field_simp

lemma fderiv_ePlane_apply (k ψ : ℝ) z w :
    fderiv ℝ (ePlane (-(((k / circlePeriod : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)))) z w =
      conj ((planeWave k z ψ * -(Complex.I * k)) * reMulCLM ψ w) := by
  have hfun : ePlane (-(((k / circlePeriod : ℝ) : ℂ) * Complex.exp (ψ * Complex.I))) =
      fun z => Complex.conjCLE.toContinuousLinearMap (planeWave k z ψ) :=
    funext (ePlane_eq_conj_planeWave k ψ)
  have hd := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := planeWave k z ψ)).comp z
    (hasFDerivAt_planeWave k z ψ)
  have hd' := hd.fderiv
  simp only [Function.comp_def] at hd'
  rw [hfun, hd']
  simp

lemma fderiv_ePlane_conormal (k ψ : ℝ) γ θ :
    fderiv ℝ (ePlane (-(((k / circlePeriod : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)))) (γ θ)
      (-(Complex.I * deriv γ θ)) = conj (pwQ k γ θ ψ) := by
  rw [fderiv_ePlane_apply, reMulCLM_apply]
  congr 1
  have hc : conj (Complex.exp (-(ψ * Complex.I))) = Complex.exp (ψ * Complex.I) := by
    rw [← Complex.exp_conj]; simp
  rw [hc]
  simp  [pwQ]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem recon_continuous_kernel_pairing {μ : Measure ℝ}
    {Q : ℝ → ComplexCurve}  
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
  bound

private theorem recon_pairing_product_integrable  [SFinite μ]
     {h a : ComplexCurve} 
    (hQm : Measurable (Function.uncurry Q)) (hQb : ∀ θ φ, ‖Q θ φ‖ ≤ B)
    (hhi : Integrable h μ) (hai : Integrable a μ) :
    Integrable (fun p : ℝ × ℝ => conj (a p.2) * (conj (Q p.1 p.2) * h p.1))
      (μ.prod μ) := by
  refine Integrable.mono' ((hhi.norm.const_mul B).mul_prod hai.norm) ?_
    (Eventually.of_forall fun p => ?_)
  · exact (Complex.continuous_conj.comp_aestronglyMeasurable
      hai.aestronglyMeasurable.comp_snd).mul
      ((Complex.continuous_conj.measurable.comp hQm).aestronglyMeasurable.mul
        hhi.aestronglyMeasurable.comp_fst)
  · simp  
    calc
      ‖a p.2‖ * (‖Q p.1 p.2‖ * ‖h p.1‖) ≤
          ‖a p.2‖ * (B * ‖h p.1‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hQb p.1 p.2) (norm_nonneg _)) (norm_nonneg _)
      _ = B * ‖h p.1‖ * ‖a p.2‖ := by ring

private theorem recon_pairing_integral_swap {μ : Measure ℝ} [SFinite μ]
     {h a : ComplexCurve} 
    (hQm : Measurable (Function.uncurry Q)) (hQb : ∀ θ φ, ‖Q θ φ‖ ≤ B)
    (hhi : Integrable h μ) (hai : Integrable a μ) :
    (∫ θ, ∫ φ, conj (a φ) * (conj (Q θ φ) * h θ) ∂μ ∂μ) =
      ∫ φ, conj (a φ) * (∫ θ, conj (Q θ φ) * h θ ∂μ) ∂μ := by
  rw [integral_integral_swap (recon_pairing_product_integrable hQm hQb hhi hai)]
  apply integral_congr_ae
  filter_upwards [] with φ
  exact integral_const_mul _ _

private theorem recon_herglotz_pairing_superposition  (ha : IsDirDensity a)
    k (γ h : ComplexCurve) θ :
    conj (herglotzConormal k a γ θ) * h θ = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ φ in boundaryHalfOpenInterval, conj (a φ) * (conj (pwQ k γ θ φ) * h θ) := by
  rw [herglotzConormal_eq_integral ha.intervalIntegrable,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, map_mul, map_inv₀,
    Complex.conj_ofReal, ← integral_conj, mul_assoc, ← integral_mul_const]
  grind

private theorem recon_continuous_dirDensity  (hGc : Continuous G) :
    IsDirDensity G := (Exists.casesOn (IsCompact.exists_bound_of_continuousOn isCompact_Icc (Continuous.continuousOn hGc)) fun M hM => MemLp.of_bound (Continuous.aestronglyMeasurable hGc) M (mp_mem (ae_restrict_mem measurableSet_Ioc) (univ_mem' (id fun φ hφ => hM φ (Ioc_subset_Icc_self hφ)))))

private theorem recon_continuous_zero_of_self_pairing {G : ComplexCurve}
    (hGc : Continuous G)
    (hsq : (∫ φ in boundaryHalfOpenInterval, conj (G φ) * G φ) = 0) :
    ∀ φ ∈ boundaryInterval, G φ = 0 := by
  have hsq' : (∫ φ in (0 : ℝ)..circlePeriod, ‖G φ‖ ^ 2) = 0 := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    have he : (∫ φ in boundaryHalfOpenInterval, conj (G φ) * G φ) =
        ((∫ φ in boundaryHalfOpenInterval, ‖G φ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [] with φ
      rw [Complex.conj_mul']
      push_cast
      ring
    rw [he] at hsq
    exact_mod_cast hsq
  intro φ hφ
  by_contra hne
  have hpos := intervalIntegral.integral_pos Real.two_pi_pos
    (f := fun φ => ‖G φ‖ ^ 2) (hGc.norm.pow 2).continuousOn
    (fun _ _ => by positivity)
    ⟨φ, hφ, by positivity⟩
  linarith

private theorem recon_energy_circle_direction  
    (hξn : ‖ξ‖ = k / circlePeriod) :
    ∃ ψ ∈ boundaryInterval,
      ξ = -(((k / circlePeriod : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) := by
  have hrep  :=
    Complex.norm_mul_exp_arg_mul_I (-ξ)
  rw [norm_neg, hξn] at hrep
  rcases le_or_gt 0 (Complex.arg (-ξ)) with h0 | h0
  · refine ⟨Complex.arg (-ξ), ⟨h0, ?_⟩, ?_⟩
    · linarith [Complex.arg_le_pi (-ξ), Real.pi_pos]
    · rw [hrep, neg_neg]
  · refine ⟨Complex.arg (-ξ) + 2 * π,
      ⟨by linarith [Complex.neg_pi_lt_arg (-ξ)], by linarith⟩, ?_⟩
    have he : Complex.exp (((Complex.arg (-ξ) + 2 * π : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((Complex.arg (-ξ) : ℂ) * Complex.I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [he, hrep, neg_neg]

/-- Compatible traces annihilate the plane waves `e^{-2πi⟨z, ξ⟩}` with `4π²|ξ|² = E`. -/
theorem doubleLayer_ePlane_eq_zero   (hK : LipschitzWith K γ) 
    (hE : 0 < E)  (hh : h ∈ compatibleTraces γ E) 
    (hξ : 4 * π ^ 2 * ‖ξ‖ ^ 2 = E) : doubleLayer γ h (ePlane ξ) = 0 := by
  obtain ⟨⟨Kh, hKh⟩, -, hcomp⟩ := hh
  set k := Real.sqrt E with hk
  set μ := volume.restrict (Ioc 0 circlePeriod) with hμ
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hhc  := hKh.continuousOn
  have hhi : Integrable h μ := (hhc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hγc  := hK.continuous
  have hQm := measurable_pwQ k hγc
  have hbd : ∀ θ φ, ‖pwQ k γ θ φ‖ ≤ |k| * K := fun θ φ =>
    (norm_pwQ_le k γ θ φ).trans (by gcongr; exact norm_deriv_le_of_lipschitz hK)
  -- the plane-wave pairing as a function of the direction
  set G : ComplexCurve := fun φ => ∫ θ, conj (pwQ k γ θ φ) * h θ ∂μ with hG
  have hGc  :=
    recon_continuous_kernel_pairing hQm (continuous_pwQ k γ) hbd hhi
  -- Fubini: pairing of a compatible trace with a Herglotz conormal trace
  have hfub : ∀ a, IsDirDensity a → ∫ φ, conj (a φ) * G φ ∂μ = 0 := by
    intro a ha
    obtain ⟨-, hz⟩ := hcomp a ha
    have hai  := ha.integrable (by norm_num)
    rw [intervalIntegral.integral_of_le h2π.le] at hz
    simp_rw [recon_herglotz_pairing_superposition ha k γ h] at hz
    rw [integral_const_mul, mul_eq_zero] at hz
    rcases hz with hz | hz
    · aesop
    exact (recon_pairing_integral_swap hQm hbd hhi hai).symm.trans hz
  -- test with `a = G`
  have hGzero  :=
    recon_continuous_zero_of_self_pairing hGc (hfub G (recon_continuous_dirDensity hGc))
  -- represent `ξ` on the circle
  have hξn : ‖ξ‖ = k / circlePeriod := by
    rw [hk, eq_div_iff h2π.ne', ← hξ]
    rw [show 4 * π ^ 2 * ‖ξ‖ ^ 2 = (‖ξ‖ * circlePeriod) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  obtain ⟨ψ, hψ, hξψ⟩ := recon_energy_circle_direction hξn
  -- conclude
  rw [hξψ, doubleLayer, intervalIntegral.integral_of_le h2π.le]
  grind only [fderiv_ePlane_conormal]

end PolyaNeumann
