module

public import Mathlib.Analysis.Fourier.LpSpace
public import RequestProject.ReconGreen
public import RequestProject.ReconChordArc
public import RequestProject.ReconVanish
public import RequestProject.ReconDensity
public import RequestProject.ReconTrace

/-!
# Cauchy reconstruction with zero conormal data (Lemmas 4.8 and 4.9)

Combines compatibility on the energy circle (`doubleLayer_ePlane_eq_zero`), the Fourier-transform
Helmholtz solver (`exists_helmholtz_solution`), and Green/trace identities to construct the linear
reconstruction `neumann_reconstruction_of_compatible`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology FourierTransform
open scoped ComplexConjugate Real FourierTransform

noncomputable section

namespace PolyaNeumann

/-! ### Compatible traces annihilate plane waves on the energy circle -/

def pwQ (k : ℝ) (γ : ℝ → ℂ) (θ φ : ℝ) : ℂ :=
  planeWave k (γ θ) φ * ((k / 2 : ℂ) * (conj (deriv γ θ) * Complex.exp (φ * Complex.I) -
    deriv γ θ * Complex.exp (-(φ * Complex.I))))

private lemma norm_pwQ_le (k : ℝ) (γ : ℝ → ℂ) (θ φ : ℝ) : ‖pwQ k γ θ φ‖ ≤ |k| * ‖deriv γ θ‖ := by
  unfold pwQ
  rw [norm_mul, norm_planeWave, one_mul, norm_mul,
    show ‖(k / 2 : ℂ)‖ = |k| / 2 by rw [norm_div, Complex.norm_real, Real.norm_eq_abs]; norm_num]
  calc |k| / 2 * ‖conj (deriv γ θ) * Complex.exp (φ * Complex.I) -
        deriv γ θ * Complex.exp (-(φ * Complex.I))‖
      ≤ |k| / 2 * (‖deriv γ θ‖ + ‖deriv γ θ‖) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I,
          norm_exp_neg_mul_I, mul_one]
    _ = |k| * ‖deriv γ θ‖ := by ring

private lemma measurable_pwQ (k : ℝ) {γ : ℝ → ℂ} (hγ : Continuous γ) :
    Measurable (Function.uncurry (pwQ k γ)) := by
  have h1 : Continuous fun p : ℝ × ℝ => planeWave k (γ p.1) p.2 := by unfold planeWave; fun_prop
  have h2 : Measurable fun p : ℝ × ℝ => deriv γ p.1 := (measurable_deriv γ).comp measurable_fst
  have h3 : Continuous fun p : ℝ × ℝ => Complex.exp (p.2 * Complex.I) := by fun_prop
  have h4 : Continuous fun p : ℝ × ℝ => Complex.exp (-(p.2 * Complex.I)) := by fun_prop
  exact h1.measurable.mul (measurable_const.mul
    (((Complex.continuous_conj.measurable.comp h2).mul h3.measurable).sub (h2.mul h4.measurable)))

private lemma herglotzConormal_eq_integral {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (γ : ℝ → ℂ) (θ : ℝ) :
    herglotzConormal k a γ θ =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), a φ * pwQ k γ θ φ := by
  rw [herglotzConormal_eq ha, herglotzCoeff, herglotzCoeff]
  have h1 := intervalIntegrable_herglotz ha k (-1) (γ θ)
  have h2 := intervalIntegrable_herglotz ha k 1 (γ θ)
  have key : ∫ φ in (0 : ℝ)..(2 * π), a φ * pwQ k γ θ φ = (k / 2 : ℂ) * (conj (deriv γ θ) *
      (∫ φ in (0 : ℝ)..(2 * π), Complex.exp (-(((-1 : ℤ) : ℂ) * φ * Complex.I)) *
        (a φ * planeWave k (γ θ) φ)) - deriv γ θ *
      ∫ φ in (0 : ℝ)..(2 * π), Complex.exp (-(((1 : ℤ) : ℂ) * φ * Complex.I)) *
        (a φ * planeWave k (γ θ) φ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (h1.const_mul _) (h2.const_mul _),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    rw [show Complex.exp (-(((-1 : ℤ) : ℂ) * φ * Complex.I)) = Complex.exp (φ * Complex.I) by
        congr 1; push_cast; ring,
      show Complex.exp (-(((1 : ℤ) : ℂ) * φ * Complex.I)) = Complex.exp (-(φ * Complex.I)) by
        congr 1; push_cast; ring, pwQ]
    ring
  rw [key]; ring

private lemma fderiv_ePlane_conormal (k ψ : ℝ) (γ : ℝ → ℂ) (θ : ℝ) :
    fderiv ℝ (ePlane (-(((k / (2 * π) : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)))) (γ θ)
      (-(Complex.I * deriv γ θ)) = conj (pwQ k γ θ ψ) := by
  have heq : ePlane (-(((k / (2 * π) : ℝ) : ℂ) * Complex.exp (ψ * Complex.I))) =
      fun z => Complex.conjCLE.toContinuousLinearMap (planeWave k z ψ) := funext fun z => by
    show ePlane _ z = conj (planeWave k z ψ)
    unfold ePlane planeWave; rw [← Complex.exp_conj]; congr 1
    have hc : conj (Complex.exp (ψ * Complex.I)) = Complex.exp (-(ψ * Complex.I)) := by
      rw [← Complex.exp_conj]; simp
    have hre : (conj z * -(((k / (2 * π) : ℝ) : ℂ) * Complex.exp (ψ * Complex.I))).re =
        -(k / (2 * π)) * (z * Complex.exp (-(ψ * Complex.I))).re := by
      rw [← Complex.conj_re, map_mul, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal, hc]
      simp only [mul_neg, Complex.neg_re]; rw [mul_left_comm, Complex.re_ofReal_mul]; ring
    rw [hre]; simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast; field_simp
  have hd := ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := planeWave k (γ θ) ψ)).comp
    (γ θ) (hasFDerivAt_planeWave k (γ θ) ψ)).fderiv
  simp only [Function.comp_def] at hd
  rw [heq, hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, reMulCLM_apply]
  congr 1
  rw [show conj (Complex.exp (-(ψ * Complex.I))) = Complex.exp (ψ * Complex.I) by
    rw [← Complex.exp_conj]; simp]
  simp only [pwQ, map_neg, map_mul, Complex.conj_I]
  ring_nf; rw [Complex.I_sq]; ring

theorem doubleLayer_ePlane_eq_zero {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    (hE : 0 < E) {h : ℝ → ℂ} (hh : h ∈ compatibleTraces γ E) {ξ : ℂ}
    (hξ : 4 * π ^ 2 * ‖ξ‖ ^ 2 = E) : doubleLayer γ h (ePlane ξ) = 0 := by
  obtain ⟨⟨Kh, hKh⟩, -, hcomp⟩ := hh
  set k := Real.sqrt E with hk
  set μ := volume.restrict (Ioc (0 : ℝ) (2 * π))
  have h2π : (0 : ℝ) < 2 * π := by positivity
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hhi : Integrable h μ := hKh.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hQm := measurable_pwQ k hK.continuous
  have hbd : ∀ θ φ, ‖pwQ k γ θ φ‖ ≤ |k| * K := fun θ φ =>
    (norm_pwQ_le k γ θ φ).trans (by gcongr; exact norm_deriv_le_of_lipschitz hK)
  set G : ℝ → ℂ := fun φ => ∫ θ, conj (pwQ k γ θ φ) * h θ ∂μ
  have hGc : Continuous G :=
    continuous_of_dominated (bound := fun θ => (|k| * K) * ‖h θ‖)
      (fun φ => ((Complex.continuous_conj.measurable.comp
        (hQm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable).mul
        hhi.aestronglyMeasurable)
      (fun φ => Eventually.of_forall fun θ => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hbd θ φ) (norm_nonneg _))
      (hhi.norm.const_mul _)
      (Eventually.of_forall fun θ => (Complex.continuous_conj.comp
        (by unfold pwQ; exact (continuous_planeWave k _).mul (by fun_prop))).mul continuous_const)
  have hfub : ∀ a, IsDirDensity a → ∫ φ, conj (a φ) * G φ ∂μ = 0 := fun a ha => by
    obtain ⟨-, hz⟩ := hcomp a ha
    have hai : Integrable a μ := ha.integrable (by norm_num)
    rw [intervalIntegral.integral_of_le h2π.le] at hz
    have hsup : ∀ θ, conj (herglotzConormal k a γ θ) * h θ = ((2 * π : ℝ) : ℂ)⁻¹ *
        ∫ φ, conj (a φ) * (conj (pwQ k γ θ φ) * h θ) ∂μ := fun θ => by
      rw [herglotzConormal_eq_integral ha.intervalIntegrable,
        intervalIntegral.integral_of_le h2π.le, map_mul, map_inv₀,
        Complex.conj_ofReal, ← integral_conj, mul_assoc, ← integral_mul_const]
      congr 2; funext _; rw [map_mul]; ring
    simp_rw [hsup] at hz
    rw [integral_const_mul, mul_eq_zero] at hz
    have hpi0 : ((2 * π : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast h2π.ne')
    have hprod : Integrable (fun p : ℝ × ℝ => conj (a p.2) * (conj (pwQ k γ p.1 p.2) * h p.1))
        (μ.prod μ) :=
      ((hhi.norm.const_mul (|k| * K)).mul_prod hai.norm).mono'
        ((Complex.continuous_conj.comp_aestronglyMeasurable hai.aestronglyMeasurable.comp_snd).mul
          ((Complex.continuous_conj.measurable.comp hQm).aestronglyMeasurable.mul
            hhi.aestronglyMeasurable.comp_fst))
        (Eventually.of_forall fun p => by
          simp only [norm_mul, Complex.norm_conj]
          calc ‖a p.2‖ * (‖pwQ k γ p.1 p.2‖ * ‖h p.1‖)
              ≤ ‖a p.2‖ * ((|k| * K) * ‖h p.1‖) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (hbd p.1 p.2) (norm_nonneg _)) (norm_nonneg _)
            _ = (|k| * K) * ‖h p.1‖ * ‖a p.2‖ := by ring)
    have hswap : (∫ θ, ∫ φ, conj (a φ) * (conj (pwQ k γ θ φ) * h θ) ∂μ ∂μ) =
        ∫ φ, conj (a φ) * G φ ∂μ := by
      rw [integral_integral_swap hprod]
      exact integral_congr_ae (Eventually.of_forall fun _ => integral_const_mul _ _)
    exact hswap.symm.trans (hz.resolve_left hpi0)
  have hGd : IsDirDensity G := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hGc.continuousOn (s := Icc (0 : ℝ) (2 * π)))
    exact MemLp.of_bound hGc.aestronglyMeasurable M
      ((ae_restrict_mem measurableSet_Ioc).mono fun φ hφ => hM φ (Ioc_subset_Icc_self hφ))
  have hsq' : (∫ φ in (0 : ℝ)..(2 * π), ‖G φ‖ ^ 2) = 0 := by
    have hsq := hfub G hGd
    rw [intervalIntegral.integral_of_le h2π.le]
    have he : (∫ φ, conj (G φ) * G φ ∂μ) = ((∫ φ, ‖G φ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall fun _ => by
        simp only; rw [Complex.conj_mul']; push_cast; ring)
    rw [he] at hsq; exact_mod_cast hsq
  have hGzero : ∀ φ ∈ Icc (0 : ℝ) (2 * π), G φ = 0 := fun φ hφ => by
    by_contra hne
    linarith [intervalIntegral.integral_pos h2π (f := fun φ => ‖G φ‖ ^ 2)
      (hGc.norm.pow 2).continuousOn (fun _ _ => by positivity)
      ⟨φ, hφ, by have := norm_pos_iff.mpr hne; positivity⟩]
  have hξn : ‖ξ‖ = k / (2 * π) := by
    rw [hk, eq_div_iff h2π.ne', ← hξ,
      show 4 * π ^ 2 * ‖ξ‖ ^ 2 = (‖ξ‖ * (2 * π)) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  obtain ⟨ψ, hψ, hξψ⟩ : ∃ ψ ∈ Icc (0 : ℝ) (2 * π),
      ξ = -(((k / (2 * π) : ℝ) : ℂ) * Complex.exp (ψ * Complex.I)) := by
    have hrep := Complex.norm_mul_exp_arg_mul_I (-ξ)
    rw [norm_neg, hξn] at hrep
    rcases le_or_gt 0 (Complex.arg (-ξ)) with h0 | h0
    · exact ⟨Complex.arg (-ξ), ⟨h0, by linarith [Complex.arg_le_pi (-ξ), Real.pi_pos]⟩,
        by rw [hrep, neg_neg]⟩
    · refine ⟨Complex.arg (-ξ) + 2 * π,
        ⟨by linarith [Complex.neg_pi_lt_arg (-ξ)], by linarith⟩, ?_⟩
      rw [show (((Complex.arg (-ξ) + 2 * π : ℝ) : ℂ) * Complex.I) =
          (Complex.arg (-ξ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, hrep, neg_neg]
  rw [hξψ, doubleLayer, intervalIntegral.integral_of_le h2π.le]
  exact (integral_congr_ae (Eventually.of_forall fun θ => by
    rw [fderiv_ePlane_conormal, mul_comm])).trans (hGzero ψ hψ)

/-! ### Fourier transform on `ℂ = ℝ²` and Helmholtz solver -/

private lemma ePlane_eq_fourierChar (ξ x : ℂ) : ePlane ξ x = ((𝐞 (-inner ℝ x ξ) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, ePlane, Complex.inner, mul_comm]
  congr 1; push_cast; ring

private lemma fourier_eq_ePlane (f : ℂ → ℂ) (ξ : ℂ) : 𝓕 f ξ = ∫ x, ePlane ξ x * f x := by
  rw [Real.fourier_eq]; congr 1; funext x
  rw [ePlane_eq_fourierChar, Circle.smul_def, smul_eq_mul]

private lemma conj_ePlane (ξ x : ℂ) : conj (ePlane ξ x) = ePlane (-ξ) x := by
  unfold ePlane; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I, mul_neg,
    Complex.neg_re, Complex.ofReal_neg]
  ring

private lemma fourierInv_eq_ePlane (f : ℂ → ℂ) (ξ : ℂ) : 𝓕⁻ f ξ = ∫ x, conj (ePlane ξ x) * f x := by
  rw [Real.fourierInv_eq]; congr 1; funext x
  rw [Circle.smul_def, smul_eq_mul, conj_ePlane, ePlane_eq_fourierChar]
  congr 3; rw [inner_neg_right, neg_neg]

private lemma ePlane_comm (ξ x : ℂ) : ePlane ξ x = ePlane x ξ := by
  unfold ePlane; rw [← Complex.conj_re (conj x * ξ)]; simp [mul_comm]

private lemma norm_ePlane (ξ x : ℂ) : ‖ePlane ξ x‖ = 1 := by
  rw [ePlane_eq_fourierChar]; exact Circle.norm_coe _

private lemma continuous_ePlane_prod : Continuous fun p : ℂ × ℂ => ePlane p.2 p.1 := by
  unfold ePlane; fun_prop

private lemma integrable_ePlane_mul {f : ℂ → ℂ} (hf : Integrable f) (ξ : ℂ) :
    Integrable fun x => ePlane ξ x * f x :=
  hf.bdd_mul (c := 1) ((continuous_ePlane_prod.comp
    (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun x => (norm_ePlane ξ x).le)

private lemma integrable_conj_ePlane_mul {f : ℂ → ℂ} (hf : Integrable f) (ξ : ℂ) :
    Integrable fun x => conj (ePlane ξ x) * f x :=
  hf.bdd_mul (c := 1) ((Complex.continuous_conj.comp (continuous_ePlane_prod.comp
    (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
    (Eventually.of_forall fun x => by rw [Complex.norm_conj, norm_ePlane])

private lemma norm_ePlane_sub_le (ξ η x : ℂ) : ‖ePlane ξ x - ePlane η x‖ ≤ 2 * π * ‖x‖ * ‖ξ - η‖ := by
  have h : ePlane ξ x - ePlane η x = ePlane η x *
      (Complex.exp (Complex.I * ((-(2 * π * (conj x * (ξ - η)).re)) : ℝ)) - 1) := by
    unfold ePlane; rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2; simp only [mul_sub, Complex.sub_re]; push_cast; ring
  rw [h, norm_mul, norm_ePlane, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have h1 : |(conj x * (ξ - η)).re| ≤ ‖x‖ * ‖ξ - η‖ :=
    (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  linarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)]

private lemma norm_fourier_le (f : ℂ → ℂ) (ξ : ℂ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [fourier_eq_ePlane]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1; funext x; rw [norm_mul, norm_ePlane, one_mul]

private lemma norm_fourier_sub_le {f : ℂ → ℂ} (hf : Integrable f)
    (hf' : Integrable fun x => ‖x‖ * ‖f x‖) (ξ η : ℂ) :
    ‖𝓕 f ξ - 𝓕 f η‖ ≤ 2 * π * (∫ x, ‖x‖ * ‖f x‖) * ‖ξ - η‖ := by
  rw [fourier_eq_ePlane, fourier_eq_ePlane,
    ← integral_sub (integrable_ePlane_mul hf ξ) (integrable_ePlane_mul hf η)]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [show 2 * π * (∫ x, ‖x‖ * ‖f x‖) * ‖ξ - η‖ = ∫ x, 2 * π * (‖x‖ * ‖f x‖) * ‖ξ - η‖ by
    rw [integral_mul_const, integral_const_mul]]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    ((hf'.const_mul _).mul_const _) (Eventually.of_forall fun x => ?_)
  simp only; rw [← sub_mul, norm_mul]
  calc ‖ePlane ξ x - ePlane η x‖ * ‖f x‖ ≤ (2 * π * ‖x‖ * ‖ξ - η‖) * ‖f x‖ := by
        gcongr; exact norm_ePlane_sub_le ξ η x
    _ = 2 * π * (‖x‖ * ‖f x‖) * ‖ξ - η‖ := by ring

private lemma integral_fourier_mul {g h : ℂ → ℂ} (hg : Integrable g) (hh : Integrable h) :
    ∫ ξ, 𝓕 g ξ * h ξ = ∫ x, g x * 𝓕 h x := by
  have hint : Integrable (fun p : ℂ × ℂ => ePlane p.2 p.1 * g p.1 * h p.2)
      ((volume : Measure ℂ).prod volume) :=
    (hg.norm.mul_prod hh.norm).mono'
      ((continuous_ePlane_prod.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_fst).mul
        hh.aestronglyMeasurable.comp_snd)
      (Eventually.of_forall fun p => by rw [norm_mul, norm_mul, norm_ePlane, one_mul])
  have L : ∫ ξ, 𝓕 g ξ * h ξ = ∫ ξ, ∫ x, ePlane ξ x * g x * h ξ :=
    integral_congr_ae (Eventually.of_forall fun _ => by
      simp only; rw [fourier_eq_ePlane, integral_mul_const])
  have R : ∫ x, g x * 𝓕 h x = ∫ x, ∫ ξ, ePlane ξ x * g x * h ξ :=
    integral_congr_ae (Eventually.of_forall fun _ => by
      simp only; rw [fourier_eq_ePlane, ← integral_const_mul]
      congr 1; funext _; rw [ePlane_comm]; ring)
  rw [L, R]
  exact (integral_integral_swap (f := fun x ξ => ePlane ξ x * g x * h ξ) hint).symm

def TestFunction.schwartz {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) : SchwartzMap ℂ ℂ :=
  hφ.2.1.toSchwartzMap hφ.1

@[simp] lemma TestFunction.schwartz_apply {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ)
    (x : ℂ) : hφ.schwartz x = φ x := rfl

private lemma inner_toLp_eq_integral {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
    (B : Lp ℂ 2 (volume : Measure ℂ)) :
    inner ℂ ((hφ.conj).schwartz.toLp 2 volume) B = ∫ x, φ x * B x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (hφ.conj).schwartz 2 volume] with x hx
  rw [hx, TestFunction.schwartz_apply, RCLike.inner_apply, Complex.conj_conj, mul_comm]

private lemma integral_fourierInv_Lp_mul (A : Lp ℂ 2 (volume : Measure ℂ)) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) :
    ∫ x, (𝓕⁻ A : Lp ℂ 2 (volume : Measure ℂ)) x * φ x = ∫ ξ, A ξ * 𝓕⁻ φ ξ := by
  set s := (hφ.conj).schwartz
  have h2 : inner ℂ (s.toLp 2 volume) (𝓕⁻ A) = inner ℂ ((𝓕 s).toLp 2 volume) A := by
    rw [← Lp.inner_fourier_eq (s.toLp 2 volume) (𝓕⁻ A), fourier_fourierInv_eq,
      SchwartzMap.toLp_fourier_eq]
  rw [show (∫ x, _ * φ x) = ∫ x, φ x * _ from
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _),
    ← inner_toLp_eq_integral hφ (𝓕⁻ A), h2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 s) 2 volume] with ξ hξ
  rw [hξ, RCLike.inner_apply, SchwartzMap.fourier_coe, fourier_eq_ePlane, fourierInv_eq_ePlane,
    ← integral_conj]
  congr 2; funext _; simp [s, map_mul]

private lemma integral_fourier_Lp_mul (A : Lp ℂ 2 (volume : Measure ℂ)) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) :
    ∫ x, (𝓕 A : Lp ℂ 2 (volume : Measure ℂ)) x * φ x = ∫ ξ, A ξ * 𝓕 φ ξ := by
  set s := (hφ.conj).schwartz
  have h2 : inner ℂ (s.toLp 2 volume) (𝓕 A) = inner ℂ ((𝓕⁻ s).toLp 2 volume) A := by
    conv_lhs => rw [← fourier_fourierInv_eq (E := Lp ℂ 2 (volume : Measure ℂ))
      (F := Lp ℂ 2 (volume : Measure ℂ)) (s.toLp 2 volume)]
    rw [Lp.inner_fourier_eq, SchwartzMap.toLp_fourierInv_eq]
  rw [show (∫ x, _ * φ x) = ∫ x, φ x * _ from
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _),
    ← inner_toLp_eq_integral hφ (𝓕 A), h2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕⁻ s) 2 volume] with ξ hξ
  rw [hξ, RCLike.inner_apply, SchwartzMap.fourierInv_coe, fourier_eq_ePlane,
    fourierInv_eq_ePlane, ← integral_conj]
  congr 2; funext _; simp [s, map_mul]

private lemma integrable_of_memLp_two_hasCompactSupport {G : ℂ → ℂ} (hG : MemLp G 2 volume)
    (hc : HasCompactSupport G) : Integrable G := by
  haveI : IsFiniteMeasure (volume.restrict (tsupport G)) :=
    isFiniteMeasure_restrict.mpr hc.isCompact.measure_lt_top.ne
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport G)).mp
    ((hG.restrict _).integrable (by norm_num))

private lemma integrable_norm_mul_of_hasCompactSupport {G : ℂ → ℂ} (hG : Integrable G)
    (hc : HasCompactSupport G) : Integrable fun x => ‖x‖ * ‖G x‖ := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine (hG.norm.const_mul R).mono' (continuous_norm.aestronglyMeasurable.mul
    hG.aestronglyMeasurable.norm) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_norm, norm_norm]
  by_cases hx : x ∈ tsupport G
  · exact mul_le_mul_of_nonneg_right (by simpa [Metric.mem_closedBall] using hR hx) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, mul_zero]

private lemma continuous_fourier_of_moment {f : ℂ → ℂ} (hf : Integrable f)
    (hf' : Integrable fun x => ‖x‖ * ‖f x‖) : Continuous (𝓕 f) :=
  LipschitzWith.continuous (K := ⟨2 * π * ∫ x, ‖x‖ * ‖f x‖,
      mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)⟩)
    (LipschitzWith.of_dist_le_mul fun ξ η => by
      rw [dist_eq_norm, dist_eq_norm]; exact norm_fourier_sub_le hf hf' ξ η)

private lemma memLp_fourier {G : ℂ → ℂ} (hG2 : MemLp G 2 volume) (hG1 : Integrable G)
    (hG' : Integrable fun x => ‖x‖ * ‖G x‖) : MemLp (𝓕 G) 2 volume := by
  set A := hG2.toLp G
  have hc := continuous_fourier_of_moment hG1 hG'
  have hloc : LocallyIntegrable (fun ξ => (𝓕 A : Lp ℂ 2 (volume : Measure ℂ)) ξ - 𝓕 G ξ) volume :=
    ((Lp.memLp (𝓕 A)).locallyIntegrable (by norm_num)).sub hc.locallyIntegrable
  have h0 := ae_eq_zero_of_integral_mul_test isOpen_univ hloc fun φ hφ => by
    have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
    simp_rw [sub_mul]
    rw [integral_sub (integrable_mul_test (Lp.memLp _) hφ)
        (hφi.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall (norm_fourier_le G))),
      integral_fourier_Lp_mul A hφ, integral_fourier_mul hG1 hφi, sub_eq_zero]
    refine integral_congr_ae ?_
    filter_upwards [hG2.coeFn_toLp] with _ hx
    rw [hx]
  rw [Measure.restrict_univ] at h0
  exact (Lp.memLp (𝓕 A)).ae_eq (h0.mono fun _ hξ => sub_eq_zero.mp hξ)

private lemma hasFDerivAt_ePlane (ξ z : ℂ) :
    HasFDerivAt (ePlane ξ) ((ePlane ξ z * (-(2 * π * Complex.I))) •
      (Complex.ofRealCLM.comp (Complex.reCLM.comp
        ((((ContinuousLinearMap.mul ℂ ℂ).flip ξ).restrictScalars ℝ).comp
          Complex.conjCLE.toContinuousLinearMap)))) z := by
  set L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp (Complex.reCLM.comp
    ((((ContinuousLinearMap.mul ℂ ℂ).flip ξ).restrictScalars ℝ).comp
      Complex.conjCLE.toContinuousLinearMap))
  have h1 : HasFDerivAt (fun z : ℂ => -(2 * π * Complex.I) * ((conj z * ξ).re : ℂ))
      ((-(2 * π * Complex.I)) • L) z := by
    simpa only [show ∀ w, L w = ((conj w * ξ).re : ℂ) from fun _ => rfl] using
      (L.hasFDerivAt (x := z)).const_mul (-(2 * π * Complex.I))
  have := h1.cexp; rwa [smul_smul] at this

private lemma dirD_ePlane (ξ v : ℂ) :
    dirD (ePlane ξ) v = fun z => -(2 * π * Complex.I) * (conj v * ξ).re * ePlane ξ z :=
  funext fun z => by
    show fderiv ℝ (ePlane ξ) z v = _
    rw [(hasFDerivAt_ePlane ξ z).fderiv]
    simp [mul_comm, mul_left_comm, mul_assoc]

private lemma fourier_symbol_sq (ξ : ℂ) :
    (-(2 * π * Complex.I) * ((conj (1 : ℂ) * ξ).re : ℂ)) ^ 2 +
      (-(2 * π * Complex.I) * ((conj Complex.I * ξ).re : ℂ)) ^ 2 =
    -(4 * π ^ 2 * (‖ξ‖ : ℂ) ^ 2) := by
  have hn : (‖ξ‖ : ℂ) ^ 2 = (ξ.re : ℂ) ^ 2 + (ξ.im : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
  simp only [map_one, one_mul, Complex.conj_I, hn, Complex.mul_re, Complex.neg_re, Complex.I_re,
    Complex.I_im, Complex.neg_im]
  ring_nf; rw [Complex.I_sq]; ring

private lemma lap_ePlane (ξ z : ℂ) : lap (ePlane ξ) z = -(4 * π ^ 2 * ‖ξ‖ ^ 2) * ePlane ξ z := by
  have h : ∀ v : ℂ, dirD (dirD (ePlane ξ) v) v z =
      (-(2 * π * Complex.I) * (conj v * ξ).re) ^ 2 * ePlane ξ z := fun v => by
    rw [dirD_ePlane]; unfold dirD
    rw [fderiv_const_mul (hasFDerivAt_ePlane ξ z).differentiableAt,
      ContinuousLinearMap.smul_apply, show fderiv ℝ (ePlane ξ) z v =
        -(2 * π * Complex.I) * (conj v * ξ).re * ePlane ξ z from congrFun (dirD_ePlane ξ v) z,
      smul_eq_mul]
    ring
  rw [lap, h, h, ← add_mul, fourier_symbol_sq]

private lemma fourierInv_dirD {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (v ξ : ℂ) :
    𝓕⁻ (dirD φ v) ξ = -(2 * π * Complex.I) * (conj v * ξ).re * 𝓕⁻ φ ξ := by
  have hlip : LipschitzWith ⟨2 * π * ‖ξ‖, by positivity⟩ (ePlane (-ξ)) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, ePlane_comm (-ξ) x, ePlane_comm (-ξ) y]
      have := norm_ePlane_sub_le x y (-ξ)
      rw [norm_neg] at this; change _ ≤ (2 * π * ‖ξ‖) * _; linarith
  have hibp := integral_mul_fderiv_of_lipschitz hlip (hφ.1.of_le (by exact_mod_cast le_top))
    hφ.2.1 v
  rw [fourierInv_eq_ePlane, fourierInv_eq_ePlane]; simp_rw [conj_ePlane]; unfold dirD
  rw [hibp, ← integral_const_mul, ← integral_neg]
  congr 1; funext x
  rw [show fderiv ℝ (ePlane (-ξ)) x v = -(2 * π * Complex.I) * (conj v * (-ξ)).re * ePlane (-ξ) x
    from congrFun (dirD_ePlane (-ξ) v) x]
  simp only [mul_neg, Complex.neg_re, Complex.ofReal_neg]; ring

private lemma fourierInv_lap {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (ξ : ℂ) :
    𝓕⁻ (lap φ) ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2) * 𝓕⁻ φ ξ := by
  have hi : ∀ v : ℂ, Integrable (dirD (dirD φ v) v) := fun v =>
    ((hφ.dirD v).dirD v).1.continuous.integrable_of_hasCompactSupport ((hφ.dirD v).dirD v).2.1
  have hsplit : 𝓕⁻ (lap φ) ξ = 𝓕⁻ (dirD (dirD φ 1) 1) ξ +
      𝓕⁻ (dirD (dirD φ Complex.I) Complex.I) ξ := by
    rw [fourierInv_eq_ePlane, fourierInv_eq_ePlane, fourierInv_eq_ePlane,
      ← integral_add (integrable_conj_ePlane_mul (hi 1) ξ) (integrable_conj_ePlane_mul (hi _) ξ)]
    congr 1; funext x; rw [lap]; ring
  rw [hsplit, fourierInv_dirD (hφ.dirD 1), fourierInv_dirD hφ, fourierInv_dirD (hφ.dirD _),
    fourierInv_dirD hφ]
  linear_combination 𝓕⁻ φ ξ * fourier_symbol_sq ξ

private lemma fourierInv_eq_schwartz {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    𝓕⁻ φ = ((𝓕⁻ hφ.schwartz : SchwartzMap ℂ ℂ) : ℂ → ℂ) := by
  rw [SchwartzMap.fourierInv_coe]; rfl

private lemma integral_fourier_mul_fourierInv {g : ℂ → ℂ} (hg : Integrable g) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) : ∫ ξ, 𝓕 g ξ * 𝓕⁻ φ ξ = ∫ x, g x * φ x := by
  rw [integral_fourier_mul hg (by rw [fourierInv_eq_schwartz hφ]; exact (𝓕⁻ hφ.schwartz).integrable)]
  congr 1; funext x
  rw [fourierInv_eq_schwartz hφ, ← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  rfl

def cdir (i : Fin 2) (ξ : ℂ) : ℝ := (conj (coordDir i) * ξ).re

private lemma abs_cdir_le (i : Fin 2) (ξ : ℂ) : |cdir i ξ| ≤ ‖ξ‖ :=
  (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, Complex.norm_conj, norm_coordDir, one_mul])

private lemma norm_two_pi_I_mul (x : ℝ) : ‖-(2 * π * Complex.I) * (x : ℂ)‖ = 2 * π * |x| := by
  rw [norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

def symN (F : ℂ → ℂ) (F' : Fin 2 → ℂ → ℂ) (ξ : ℂ) : ℂ :=
  -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * F ξ + ∑ i, (-(2 * π * Complex.I) * cdir i ξ) * F' i ξ

def symS (E : ℝ) (F : ℂ → ℂ) (F' : Fin 2 → ℂ → ℂ) (ξ : ℂ) : ℂ :=
  -(E : ℂ) * F ξ + ∑ i, (-(2 * π * Complex.I) * cdir i ξ) * F' i ξ

def symD (E : ℝ) (ξ : ℂ) : ℂ := ((E - 4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)

private lemma symS_eq (E : ℝ) (F : ℂ → ℂ) (F' : Fin 2 → ℂ → ℂ) (ξ : ℂ) :
    symS E F F' ξ = symN F F' ξ - symD E ξ * F ξ := by
  simp only [symS, symN, symD]; push_cast; ring

private lemma norm_symD (E : ℝ) (ξ : ℂ) : ‖symD E ξ‖ = |E - 4 * π ^ 2 * ‖ξ‖ ^ 2| := by
  rw [symD, Complex.norm_real, Real.norm_eq_abs]

private lemma norm_mul_sub_mul_le {a f : ℂ → ℂ} {A B Ka Kf : ℝ} (ξ η : ℂ)
    (ha : ‖a ξ - a η‖ ≤ Ka * ‖ξ - η‖) (hf : ‖f ξ - f η‖ ≤ Kf * ‖ξ - η‖)
    (haη : ‖a η‖ ≤ A) (hfξ : ‖f ξ‖ ≤ B) :
    ‖a ξ * f ξ - a η * f η‖ ≤ (Ka * B + A * Kf) * ‖ξ - η‖ := by
  rw [show a ξ * f ξ - a η * f η = (a ξ - a η) * f ξ + a η * (f ξ - f η) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  calc ‖a ξ - a η‖ * ‖f ξ‖ + ‖a η‖ * ‖f ξ - f η‖
      ≤ Ka * ‖ξ - η‖ * B + A * (Kf * ‖ξ - η‖) := add_le_add
        (mul_le_mul ha hfξ (norm_nonneg _) ((norm_nonneg _).trans ha))
        (mul_le_mul haη hf (norm_nonneg _) ((norm_nonneg _).trans haη))
    _ = _ := by ring

private lemma symS_div_bound {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {B K k E : ℝ} (hk0 : 0 < k)
    (hk : 4 * π ^ 2 * k ^ 2 = E) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hFb : ∀ ξ, ‖F ξ‖ ≤ B) (hF'b : ∀ i ξ, ‖F' i ξ‖ ≤ B)
    (hFl : ∀ ξ η, ‖F ξ - F η‖ ≤ K * ‖ξ - η‖) (hF'l : ∀ i ξ η, ‖F' i ξ - F' i η‖ ≤ K * ‖ξ - η‖)
    (hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0) :
    ∃ M : ℝ, ∀ ξ, ‖symS E F F' ξ / symD E ξ‖ * (1 + ‖ξ‖) ≤
      M * ((Metric.closedBall (0 : ℂ) (2 * k)).indicator (fun _ => (1 : ℝ)) ξ + ‖F ξ‖ +
        ∑ i, ‖F' i ξ‖) := by
  set L := (8 * π ^ 2 * (2 * k) * B + 4 * π ^ 2 * (2 * k) ^ 2 * K) +
        2 * (2 * π * B + 2 * π * (2 * k) * K)
  set C1 := L / (4 * π ^ 2 * k)
  set M2 := (E / (4 * k ^ 2) + E / (2 * k) + π / k + 2 * π) / (3 * π ^ 2)
  have hE : 0 < E := by rw [← hk]; positivity
  have hC1 : 0 ≤ C1 := by positivity
  have hM2 : 0 ≤ M2 := by positivity
  refine ⟨(1 + 2 * k) * C1 + (1 + 2 * k) + M2, fun ξ => ?_⟩
  have hs : 0 ≤ ‖F ξ‖ := norm_nonneg _
  have ht : 0 ≤ ∑ i, ‖F' i ξ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  by_cases hξ : ‖ξ‖ ≤ 2 * k
  · rw [indicator_of_mem (by rw [Metric.mem_closedBall, dist_zero_right]; exact hξ)]
    have hw : ‖symS E F F' ξ / symD E ξ‖ ≤ C1 + ‖F ξ‖ := by
      by_cases hD : symD E ξ = 0
      · rw [hD, div_zero, norm_zero]; positivity
      · rw [symS_eq, sub_div, mul_div_cancel_left₀ _ hD]
        obtain ⟨ξ₀, h0, hd⟩ : ∃ ξ₀ : ℂ, ‖ξ₀‖ = k ∧ ‖ξ - ξ₀‖ = |‖ξ‖ - k| := by
          by_cases h : ξ = 0
          · exact ⟨(k : ℂ), by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0],
              by rw [h, zero_sub, norm_neg, norm_zero, zero_sub, abs_neg, Complex.norm_real,
                Real.norm_eq_abs]⟩
          · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr h
            exact ⟨((k / ‖ξ‖ : ℝ) : ℂ) * ξ,
              by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hk0,
                abs_norm, div_mul_cancel₀ _ hn],
              by rw [show ξ - ((k / ‖ξ‖ : ℝ) : ℂ) * ξ = (((‖ξ‖ - k) / ‖ξ‖ : ℝ) : ℂ) * ξ by
                have : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hn
                push_cast; field_simp,
                norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
                div_mul_cancel₀ _ hn]⟩
        set R := 2 * k
        have hR0 : 0 ≤ R := by positivity
        have hη : ‖ξ₀‖ ≤ R := by rw [h0]; linarith
        set a : ℂ → ℂ := fun ζ => -((4 * π ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ)
        set b : Fin 2 → ℂ → ℂ := fun i ζ => -(2 * π * Complex.I) * cdir i ζ
        have ha : ‖a ξ - a ξ₀‖ ≤ (8 * π ^ 2 * R) * ‖ξ - ξ₀‖ := by
          rw [show a ξ - a ξ₀ = ((-(4 * π ^ 2) * ((‖ξ‖ - ‖ξ₀‖) * (‖ξ‖ + ‖ξ₀‖)) : ℝ) : ℂ) by
              simp only [a]; push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
            abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ + ‖ξ₀‖)]
          have h3 : |‖ξ‖ - ‖ξ₀‖| * (‖ξ‖ + ‖ξ₀‖) ≤ ‖ξ - ξ₀‖ * (2 * R) :=
            mul_le_mul (abs_norm_sub_norm_le ξ ξ₀) (by linarith) (by positivity) (norm_nonneg _)
          linarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * π ^ 2)]
        have haη : ‖a ξ₀‖ ≤ 4 * π ^ 2 * R ^ 2 := by
          simp only [a]; rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [pow_le_pow_left₀ (norm_nonneg _) hη 2, Real.pi_pos]
        have hb : ∀ i, ‖b i ξ - b i ξ₀‖ ≤ (2 * π) * ‖ξ - ξ₀‖ := fun i => by
          rw [show b i ξ - b i ξ₀ = -(2 * π * Complex.I) * (cdir i (ξ - ξ₀) : ℂ) by
              simp only [b, cdir, mul_sub, Complex.sub_re]; push_cast; ring,
            norm_two_pi_I_mul]
          exact mul_le_mul_of_nonneg_left (abs_cdir_le i _) (by positivity)
        have hbη : ∀ i, ‖b i ξ₀‖ ≤ 2 * π * R := fun i => by
          simp only [b]; rw [norm_two_pi_I_mul]
          exact mul_le_mul_of_nonneg_left ((abs_cdir_le i _).trans hη) (by positivity)
        have hLip : ‖symN F F' ξ‖ ≤ L * |‖ξ‖ - k| := by
          have e : symN F F' ξ - symN F F' ξ₀ = (a ξ * F ξ - a ξ₀ * F ξ₀) +
              ((b 0 ξ * F' 0 ξ - b 0 ξ₀ * F' 0 ξ₀) + (b 1 ξ * F' 1 ξ - b 1 ξ₀ * F' 1 ξ₀)) := by
            simp only [symN, Fin.sum_univ_two, a, b]; ring
          have t1 := norm_mul_sub_mul_le ξ ξ₀ ha (hFl ξ ξ₀) haη (hFb ξ)
          have t2 := norm_mul_sub_mul_le ξ ξ₀ (hb 0) (hF'l 0 ξ ξ₀) (hbη 0) (hF'b 0 ξ)
          have t3 := norm_mul_sub_mul_le ξ ξ₀ (hb 1) (hF'l 1 ξ ξ₀) (hbη 1) (hF'b 1 ξ)
          have hsub := (norm_add_le _ _).trans ((add_le_add t1 (norm_add_le _ _)).trans
            (add_le_add le_rfl (add_le_add t2 t3)))
          rw [← e, hN ξ₀ h0, sub_zero, hd] at hsub
          exact hsub.trans (by dsimp [L, R]; nlinarith [abs_nonneg (‖ξ‖ - k)])
        have hDbd : 4 * π ^ 2 * k * |‖ξ‖ - k| ≤ ‖symD E ξ‖ := by
          rw [norm_symD, ← hk,
            show 4 * π ^ 2 * k ^ 2 - 4 * π ^ 2 * ‖ξ‖ ^ 2 = 4 * π ^ 2 * ((k - ‖ξ‖) * (k + ‖ξ‖)) by ring,
            abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2), abs_mul,
            abs_of_pos (by positivity : (0 : ℝ) < k + ‖ξ‖), abs_sub_comm k ‖ξ‖]
          have h2 := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg ξ] : k ≤ k + ‖ξ‖)
              (abs_nonneg (‖ξ‖ - k)))
            (by positivity : (0 : ℝ) ≤ 4 * π ^ 2)
          linarith
        have hdiv : ‖symN F F' ξ / symD E ξ‖ ≤ C1 := by
          rw [norm_div]
          refine div_le_of_le_mul₀ (norm_nonneg _) hC1 ?_
          calc ‖symN F F' ξ‖ ≤ L * |‖ξ‖ - k| := hLip
            _ = C1 * (4 * π ^ 2 * k * |‖ξ‖ - k|) := by dsimp [C1]; field_simp
            _ ≤ C1 * ‖symD E ξ‖ := mul_le_mul_of_nonneg_left hDbd hC1
        exact (norm_sub_le _ _).trans (by linarith)
    calc ‖symS E F F' ξ / symD E ξ‖ * (1 + ‖ξ‖) ≤ (C1 + ‖F ξ‖) * (1 + 2 * k) :=
          mul_le_mul hw (by linarith) (by positivity) (by positivity)
      _ ≤ _ := by
        have ha : 0 ≤ 1 + 2 * k := by linarith
        nlinarith [mul_nonneg (mul_nonneg ha hC1) hs, mul_nonneg (mul_nonneg ha hC1) ht,
          mul_nonneg ha ht, mul_nonneg hM2 (show 0 ≤ 1 + ‖F ξ‖ + ∑ i, ‖F' i ξ‖ by positivity)]
  · push_neg at hξ
    rw [indicator_of_notMem (by rw [Metric.mem_closedBall, dist_zero_right]; linarith), zero_add]
    set r := ‖ξ‖
    set s := ‖F ξ‖
    set t := ‖F' 0 ξ‖ + ‖F' 1 ξ‖
    have hr0 : 0 < r := by linarith
    have hS : ‖symS E F F' ξ‖ ≤ E * s + 2 * π * r * t := by
      simp only [symS, Fin.sum_univ_two]
      refine (norm_add_le _ _).trans ((add_le_add_right (norm_add_le _ _) _).trans ?_)
      rw [norm_mul (-(E : ℂ)), norm_mul _ (F' 0 ξ), norm_mul _ (F' 1 ξ), norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE, norm_two_pi_I_mul, norm_two_pi_I_mul]
      have : 2 * π * |cdir 0 ξ| * ‖F' 0 ξ‖ ≤ 2 * π * r * ‖F' 0 ξ‖ := by
        gcongr; exact abs_cdir_le 0 ξ
      have : 2 * π * |cdir 1 ξ| * ‖F' 1 ξ‖ ≤ 2 * π * r * ‖F' 1 ξ‖ := by
        gcongr; exact abs_cdir_le 1 ξ
      simp only [t]; linarith
    have hD : 3 * π ^ 2 * r ^ 2 ≤ ‖symD E ξ‖ := by
      rw [norm_symD, ← hk, abs_sub_comm]
      have : 4 * π ^ 2 * k ^ 2 ≤ π ^ 2 * r ^ 2 := by nlinarith [show 4 * k ^ 2 ≤ r ^ 2 by nlinarith, Real.pi_pos]
      exact le_trans (by linarith) (le_abs_self _)
    have hDpos : 0 < ‖symD E ξ‖ := lt_of_lt_of_le (by positivity) hD
    have hfar : ‖symS E F F' ξ / symD E ξ‖ * (1 + r) ≤ M2 * (s + ∑ i, ‖F' i ξ‖) := by
      rw [show ∑ i, ‖F' i ξ‖ = t from Fin.sum_univ_two _, norm_div, div_mul_eq_mul_div,
        div_le_iff₀ hDpos]
      have h1 : 1 ≤ r ^ 2 / (4 * k ^ 2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
      have h2 : r ≤ r ^ 2 / (2 * k) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
      have ht0 : 0 ≤ t := by positivity
      have key : (E * s + 2 * π * r * t) * (1 + r) ≤
          ((E / (4 * k ^ 2) + E / (2 * k)) * s + (π / k + 2 * π) * t) * r ^ 2 := by
        have a1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ E * s)
        have a2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ E * s)
        have a3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * π * t)
        have e1 : E * s * (r ^ 2 / (4 * k ^ 2)) + E * s * (r ^ 2 / (2 * k)) +
            2 * π * t * (r ^ 2 / (2 * k)) + 2 * π * t * r ^ 2 =
            ((E / (4 * k ^ 2) + E / (2 * k)) * s + (π / k + 2 * π) * t) * r ^ 2 := by
          field_simp; ring
        nlinarith
      calc ‖symS E F F' ξ‖ * (1 + r) ≤ (E * s + 2 * π * r * t) * (1 + r) :=
            mul_le_mul_of_nonneg_right hS (by positivity)
        _ ≤ ((E / (4 * k ^ 2) + E / (2 * k)) * s + (π / k + 2 * π) * t) * r ^ 2 := key
        _ ≤ (E / (4 * k ^ 2) + E / (2 * k) + π / k + 2 * π) * (s + t) * r ^ 2 := by
            gcongr
            nlinarith [Real.pi_pos, show 0 ≤ E / (4 * k ^ 2) + E / (2 * k) by positivity,
              show 0 ≤ π / k + 2 * π by positivity]
        _ = M2 * (s + t) * (3 * π ^ 2 * r ^ 2) := by dsimp [M2]; field_simp
        _ ≤ M2 * (s + t) * ‖symD E ξ‖ := mul_le_mul_of_nonneg_left hD (by positivity)
    exact hfar.trans (by nlinarith [show 0 ≤ (1 + 2 * k) * C1 + (1 + 2 * k) by positivity])

theorem exists_helmholtz_solution {E : ℝ} (hE : 0 < E) {G : ℂ → ℂ} {G' : Fin 2 → ℂ → ℂ}
    (hG : MemLp G 2 volume) (hGc : HasCompactSupport G) (hG' : ∀ i, MemLp (G' i) 2 volume)
    (hG'c : ∀ i, HasCompactSupport (G' i))
    (hvan : ∀ ξ : ℂ, 4 * π ^ 2 * ‖ξ‖ ^ 2 = E →
      ∫ z, (G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z) = 0) :
    ∃ (w : ℂ → ℂ) (gw : Fin 2 → ℂ → ℂ), MemLp w 2 volume ∧ (∀ i, MemLp (gw i) 2 volume) ∧
      IsWeakGradOn univ w gw ∧
      ∀ φ : ℂ → ℂ, TestFunction univ φ →
        ∫ z, (G z + w z) * (lap φ z + E * φ z) =
          ∫ z, (G z * lap φ z + ∑ i : Fin 2, G' i z * dirD φ (coordDir i) z) := by
  have hG1 : Integrable G := integrable_of_memLp_two_hasCompactSupport hG hGc
  have hG'1 : ∀ i, Integrable (G' i) := fun i =>
    integrable_of_memLp_two_hasCompactSupport (hG' i) (hG'c i)
  have hGm := integrable_norm_mul_of_hasCompactSupport hG1 hGc
  have hG'm := fun i => integrable_norm_mul_of_hasCompactSupport (hG'1 i) (hG'c i)
  set F : ℂ → ℂ := 𝓕 G
  set F' : Fin 2 → ℂ → ℂ := fun i => 𝓕 (G' i)
  have hFc : Continuous F := continuous_fourier_of_moment hG1 hGm
  have hF'c : ∀ i, Continuous (F' i) := fun i => continuous_fourier_of_moment (hG'1 i) (hG'm i)
  have hF2 : MemLp F 2 volume := memLp_fourier hG hG1 hGm
  have hF'2 : ∀ i, MemLp (F' i) 2 volume := fun i => memLp_fourier (hG' i) (hG'1 i) (hG'm i)
  set B := (∫ x, ‖G x‖) + ∑ i, ∫ x, ‖G' i x‖
  set K := 2 * π * ((∫ x, ‖x‖ * ‖G x‖) + ∑ i, ∫ x, ‖x‖ * ‖G' i x‖) with hKdef
  have hI0 : 0 ≤ ∫ x, ‖G x‖ := integral_nonneg fun _ => norm_nonneg _
  have hI'0 : ∀ i, 0 ≤ ∫ x, ‖G' i x‖ := fun _ => integral_nonneg fun _ => norm_nonneg _
  have hJ0 : 0 ≤ ∫ x, ‖x‖ * ‖G x‖ := integral_nonneg fun _ => by positivity
  have hJ'0 : ∀ i, 0 ≤ ∫ x, ‖x‖ * ‖G' i x‖ := fun _ => integral_nonneg fun _ => by positivity
  have hS0 : 0 ≤ ∑ i, ∫ x, ‖G' i x‖ := Finset.sum_nonneg fun i _ => hI'0 i
  have hT0 : 0 ≤ ∑ i, ∫ x, ‖x‖ * ‖G' i x‖ := Finset.sum_nonneg fun i _ => hJ'0 i
  have hB : 0 ≤ B := by positivity
  have hK : 0 ≤ K := by positivity
  have hFb : ∀ ξ, ‖F ξ‖ ≤ B := fun ξ => (norm_fourier_le G ξ).trans (by linarith)
  have hF'b : ∀ i ξ, ‖F' i ξ‖ ≤ B := fun i ξ => (norm_fourier_le (G' i) ξ).trans <| by
    linarith [Finset.single_le_sum (f := fun i => ∫ x, ‖G' i x‖) (fun i _ => hI'0 i)
      (Finset.mem_univ i)]
  have hFl : ∀ ξ η, ‖F ξ - F η‖ ≤ K * ‖ξ - η‖ := fun ξ η =>
    (norm_fourier_sub_le hG1 hGm ξ η).trans <|
      mul_le_mul_of_nonneg_right (by rw [hKdef]; nlinarith [Real.pi_pos]) (norm_nonneg _)
  have hF'l : ∀ i ξ η, ‖F' i ξ - F' i η‖ ≤ K * ‖ξ - η‖ := fun i ξ η =>
    (norm_fourier_sub_le (hG'1 i) (hG'm i) ξ η).trans <|
      mul_le_mul_of_nonneg_right (by
        have := Finset.single_le_sum (f := fun i => ∫ x, ‖x‖ * ‖G' i x‖) (fun i _ => hJ'0 i)
          (Finset.mem_univ i)
        rw [hKdef]; nlinarith [Real.pi_pos]) (norm_nonneg _)
  set k := Real.sqrt E / (2 * π) with hkdef
  have hk0 : 0 < k := by positivity
  have hk : 4 * π ^ 2 * k ^ 2 = E := by rw [hkdef, div_pow, Real.sq_sqrt hE.le]; field_simp; ring
  have hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0 := fun ξ hξ => by
    have e : ∀ z, G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z =
        -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (ePlane ξ z * G z) +
          ((-(2 * π * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) +
            (-(2 * π * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z)) := fun z => by
      rw [lap_ePlane, Fin.sum_univ_two, dirD_ePlane, dirD_ePlane]
      simp only [cdir]; push_cast; ring
    have h0 := hvan ξ (by rw [hξ, hk])
    simp_rw [e] at h0
    have hi0 := (integrable_ePlane_mul (hG'1 0) ξ).const_mul (-(2 * π * Complex.I) * cdir 0 ξ)
    have hi1 := (integrable_ePlane_mul (hG'1 1) ξ).const_mul (-(2 * π * Complex.I) * cdir 1 ξ)
    have hi01 : Integrable fun z => (-(2 * π * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) +
        (-(2 * π * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z) := hi0.add hi1
    rw [integral_add ((integrable_ePlane_mul hG1 ξ).const_mul _) hi01,
      integral_add hi0 hi1, integral_const_mul, integral_const_mul, integral_const_mul,
      ← fourier_eq_ePlane, ← fourier_eq_ePlane, ← fourier_eq_ePlane] at h0
    simpa only [symN, Fin.sum_univ_two, F, F'] using h0
  obtain ⟨M, hM⟩ := symS_div_bound hk0 hk hB hK hFb hF'b hFl hF'l hN
  set wh : ℂ → ℂ := fun ξ => symS E F F' ξ / symD E ξ with hwhdef
  set gwh : Fin 2 → ℂ → ℂ := fun i ξ => (2 * π * Complex.I * cdir i ξ) * wh ξ with hgwhdef
  set D : ℂ → ℝ := fun ξ => M * ((Metric.closedBall (0 : ℂ) (2 * k)).indicator
    (fun _ => (1 : ℝ)) ξ + ‖F ξ‖ + ∑ i, ‖F' i ξ‖)
  have hD2 : MemLp D 2 volume :=
    (((memLp_indicator_const 2 Metric.isClosed_closedBall.measurableSet (1 : ℝ)
      (Or.inr measure_closedBall_lt_top.ne)).add hF2.norm).add
      (memLp_finset_sum _ fun i _ => (hF'2 i).norm)).const_mul M
  have hcdir_c : ∀ i, Continuous (cdir i) := fun i => by unfold cdir; fun_prop
  have hwhm : AEStronglyMeasurable wh volume :=
    ((((continuous_const.mul hFc).add (continuous_finset_sum _ fun i _ =>
      (continuous_const.mul (Complex.continuous_ofReal.comp (hcdir_c i))).mul (hF'c i))).measurable).div
      (by unfold symD; fun_prop : Continuous (symD E)).measurable).aestronglyMeasurable
  have hwh2 : MemLp wh 2 volume :=
    hD2.of_le hwhm (Eventually.of_forall fun ξ =>
      (by nlinarith [norm_nonneg (wh ξ), norm_nonneg ξ] : ‖wh ξ‖ ≤ ‖wh ξ‖ * (1 + ‖ξ‖)).trans
        ((hM ξ).trans (Real.le_norm_self _)))
  have hgwh2 : ∀ i, MemLp (gwh i) 2 volume := fun i =>
    (hD2.const_mul (2 * π)).of_le
      (((continuous_const.mul (Complex.continuous_ofReal.comp (hcdir_c i))).aestronglyMeasurable).mul hwhm)
      (Eventually.of_forall fun ξ => by
        refine le_trans ?_ (Real.le_norm_self _)
        simp only [hgwhdef]
        rw [norm_mul, show (2 * π * Complex.I * (cdir i ξ : ℂ)) =
          -(-(2 * π * Complex.I) * (cdir i ξ : ℂ)) by ring, norm_neg, norm_two_pi_I_mul]
        have h4 : |cdir i ξ| * ‖wh ξ‖ ≤ ‖wh ξ‖ * (1 + ‖ξ‖) := by
          nlinarith [abs_cdir_le i ξ, norm_nonneg (wh ξ), norm_nonneg ξ]
        nlinarith [hM ξ, Real.pi_pos])
  set W : Lp ℂ 2 (volume : Measure ℂ) := 𝓕⁻ (hwh2.toLp wh)
  set GW : Fin 2 → Lp ℂ 2 (volume : Measure ℂ) := fun i => 𝓕⁻ ((hgwh2 i).toLp (gwh i))
  have hpair : ∀ (A : ℂ → ℂ) (hA : MemLp A 2 volume) {ψ : ℂ → ℂ}, TestFunction univ ψ →
      ∫ x, (𝓕⁻ (hA.toLp A) : Lp ℂ 2 (volume : Measure ℂ)) x * ψ x = ∫ ξ, A ξ * 𝓕⁻ ψ ξ :=
    fun A hA ψ hψ => by
      rw [integral_fourierInv_Lp_mul _ hψ]
      refine integral_congr_ae ?_
      filter_upwards [hA.coeFn_toLp] with _ hξ
      rw [hξ]
  refine ⟨W, fun i => GW i, Lp.memLp _, fun i => Lp.memLp _, ?_, ?_⟩
  · intro φ hφ i
    have h1 : ∫ z, W z * fderiv ℝ φ z (coordDir i) =
        ∫ ξ, wh ξ * 𝓕⁻ (dirD φ (coordDir i)) ξ := hpair wh hwh2 (hφ.dirD _)
    have h2 : ∫ z, GW i z * φ z = ∫ ξ, gwh i ξ * 𝓕⁻ φ ξ := hpair (gwh i) (hgwh2 i) hφ
    rw [h1, h2, ← integral_neg]
    congr 1; funext ξ; rw [fourierInv_dirD hφ]; simp only [hgwhdef, cdir]; ring
  · intro φ hφ
    set H : ℂ → ℂ := fun z => lap φ z + E * φ z with hHdef
    have hH : TestFunction univ H := hφ.helm E
    have hinv_int : ∀ {ψ : ℂ → ℂ}, TestFunction univ ψ → Integrable (𝓕⁻ ψ) := fun {ψ} hψ => by
      rw [fourierInv_eq_schwartz hψ]; exact (𝓕⁻ hψ.schwartz).integrable
    have hFH : Integrable fun ξ => F ξ * 𝓕⁻ H ξ :=
      (hinv_int hH).bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall hFb)
    have hwH : Integrable fun ξ => wh ξ * 𝓕⁻ H ξ :=
      hwh2.integrable_mul (by rw [fourierInv_eq_schwartz hH]; exact (𝓕⁻ hH.schwartz).memLp 2 volume)
    have hFL : Integrable fun ξ => F ξ * 𝓕⁻ (lap φ) ξ :=
      (hinv_int hφ.lap).bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall hFb)
    have hF'd : ∀ i, Integrable fun ξ => F' i ξ * 𝓕⁻ (dirD φ (coordDir i)) ξ := fun i =>
      (hinv_int (hφ.dirD _)).bdd_mul (hF'c i).aestronglyMeasurable (Eventually.of_forall (hF'b i))
    have hG'd : ∀ i, Integrable fun z => G' i z * dirD φ (coordDir i) z := fun i =>
      integrable_mul_test (hG' i) (hφ.dirD _)
    have eL : ∫ z, (G z + W z) * H z = ∫ ξ, (F ξ * 𝓕⁻ H ξ + wh ξ * 𝓕⁻ H ξ) := by
      simp_rw [add_mul]
      rw [integral_add (integrable_mul_test hG hH) (integrable_mul_test (Lp.memLp _) hH),
        integral_add hFH hwH, hpair wh hwh2 hH, ← integral_fourier_mul_fourierInv hG1 hH]
    have hs1 : Integrable fun z => G' 0 z * dirD φ (coordDir 0) z +
        G' 1 z * dirD φ (coordDir 1) z := (hG'd 0).add (hG'd 1)
    have hs2 : Integrable fun ξ => F' 0 ξ * 𝓕⁻ (dirD φ (coordDir 0)) ξ +
        F' 1 ξ * 𝓕⁻ (dirD φ (coordDir 1)) ξ := (hF'd 0).add (hF'd 1)
    have eR : ∫ z, (G z * lap φ z + ∑ i : Fin 2, G' i z * dirD φ (coordDir i) z) =
        ∫ ξ, (F ξ * 𝓕⁻ (lap φ) ξ + (F' 0 ξ * 𝓕⁻ (dirD φ (coordDir 0)) ξ +
          F' 1 ξ * 𝓕⁻ (dirD φ (coordDir 1)) ξ)) := by
      simp only [Fin.sum_univ_two]
      rw [integral_add (integrable_mul_test hG hφ.lap) hs1, integral_add (hG'd 0) (hG'd 1),
        integral_add hFL hs2, integral_add (hF'd 0) (hF'd 1),
        ← integral_fourier_mul_fourierInv hG1 hφ.lap,
        ← integral_fourier_mul_fourierInv (hG'1 0) (hφ.dirD _),
        ← integral_fourier_mul_fourierInv (hG'1 1) (hφ.dirD _)]
    rw [eL, eR]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    have hwD : symS E F F' ξ / symD E ξ * symD E ξ = symS E F F' ξ := by
      by_cases hD : symD E ξ = 0
      · have h0 : E - 4 * π ^ 2 * ‖ξ‖ ^ 2 = 0 := by rwa [symD, Complex.ofReal_eq_zero] at hD
        have hsq : ‖ξ‖ ^ 2 = k ^ 2 := by nlinarith [Real.pi_pos]
        rw [symS_eq, hN ξ ((sq_eq_sq₀ (norm_nonneg ξ) hk0.le).mp hsq), hD]; simp
      · exact div_mul_cancel₀ _ hD
    have e1 : 𝓕⁻ H ξ = symD E ξ * 𝓕⁻ φ ξ := by
      have hi1 : Integrable (lap φ) := hφ.lap.1.continuous.integrable_of_hasCompactSupport hφ.lap.2.1
      have hi2 : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
      have es : 𝓕⁻ H ξ = 𝓕⁻ (lap φ) ξ + E * 𝓕⁻ φ ξ := by
        simp only [hHdef]
        rw [fourierInv_eq_ePlane, fourierInv_eq_ePlane, fourierInv_eq_ePlane, ← integral_const_mul,
          ← integral_add (integrable_conj_ePlane_mul hi1 ξ)
            ((integrable_conj_ePlane_mul hi2 ξ).const_mul _)]
        congr 1; funext _; ring
      rw [es, fourierInv_lap hφ, symD]; push_cast; ring
    simp only
    rw [e1, fourierInv_lap hφ, fourierInv_dirD hφ, fourierInv_dirD hφ,
      show wh ξ * (symD E ξ * 𝓕⁻ φ ξ) = symS E F F' ξ * 𝓕⁻ φ ξ by
        rw [← mul_assoc, hwhdef]; simp only; rw [hwD],
      symS_eq]
    simp only [symN, symD, Fin.sum_univ_two, cdir]; push_cast; ring

/-! ### Domain geometry and the reconstructed eigenfunction -/

def IsReconSol (γ : ℝ → ℂ) (E : ℝ) (h : ℝ → ℂ) (u : Lp ℂ 2 (volume : Measure ℂ)) : Prop :=
  ∀ φ : ℂ → ℂ, TestFunction univ φ → ∫ z, u z * (lap φ z + E * φ z) = doubleLayer γ h φ

section Recon

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {E : ℝ}

private lemma ae_mem_or_mem_exterior (hγ : IsBoundaryParam Ω γ) (hΩo : IsOpen Ω) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω ∨ z ∈ (closure Ω)ᶜ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have h0 : volume (frontier Ω) = 0 := by rw [← hγ.image]; exact volume_image_Icc_eq_zero hK 0 (2 * π)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with z hz
  by_cases hzc : z ∈ closure Ω
  · left; rw [frontier, hΩo.interior_eq] at hz
    exact by_contra fun hzΩ => hz ⟨hzc, hzΩ⟩
  · exact Or.inr hzc

private lemma doubleLayer_add {K : NNReal} (hK : LipschitzWith K γ) {h₁ h₂ : ℝ → ℂ}
    (h₁c : ContinuousOn h₁ (Icc 0 (2 * π))) (h₂c : ContinuousOn h₂ (Icc 0 (2 * π)))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    doubleLayer γ (h₁ + h₂) φ = doubleLayer γ h₁ φ + doubleLayer γ h₂ φ := by
  have hc : Continuous (fun θ => fderiv ℝ φ (γ θ)) :=
    (hφ.continuous_fderiv one_ne_zero).comp hK.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  have hfc : IntervalIntegrable (fun θ => fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) volume 0
      (2 * π) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr <|
      Measure.integrableOn_of_bounded (M := M * K) measure_Ioc_lt_top.ne
        (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hc.aestronglyMeasurable.prodMk
            ((measurable_deriv γ).const_mul _).neg.aestronglyMeasurable)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    calc ‖fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))‖
        ≤ ‖fderiv ℝ φ (γ θ)‖ * ‖-(Complex.I * deriv γ θ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * K := by
          gcongr
          · exact (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
          · exact hM θ (Ioc_subset_Icc_self hθ)
          · rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
            exact norm_deriv_le_of_lipschitz hK
  have hint : ∀ {h : ℝ → ℂ}, ContinuousOn h (Icc 0 (2 * π)) →
      IntervalIntegrable (fun θ => h θ * fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)))
        volume 0 (2 * π) := fun {h} hhc =>
    hfc.continuousOn_mul (by rwa [uIcc_of_le (by positivity)])
  unfold doubleLayer
  rw [← intervalIntegral.integral_add (hint h₁c) (hint h₂c)]
  exact intervalIntegral.integral_congr fun _ _ => by simp only [Pi.add_apply]; ring

private lemma IsReconSol.unique (hE : 0 < E) {h : ℝ → ℂ} {u u' : Lp ℂ 2 (volume : Measure ℂ)}
    (hu : IsReconSol γ E h u) (hu' : IsReconSol γ E h u') : u = u' := by
  have hz := ae_eq_zero_of_helmholtz hE isOpen_univ isConnected_univ (R := 0)
    (fun z _ => mem_univ z) (Lp.memLp (u - u')) fun φ hφ => by
      have hi : ∀ v : Lp ℂ 2 (volume : Measure ℂ),
          Integrable (fun z => v z * (lap φ z + E * φ z)) := fun v =>
        integrable_mul_test (Lp.memLp v) (hφ.helm E)
      rw [integral_congr_ae ((Lp.coeFn_sub u u').mono fun _ hz => by
          rw [hz, Pi.sub_apply, sub_mul]),
        integral_sub (hi u) (hi u'), hu φ hφ, hu' φ hφ, sub_self]
  rw [Measure.restrict_univ] at hz
  rw [← sub_eq_zero]; apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with _ h1 h2
  rw [h1, h2]; rfl

private lemma IsReconSol.ae_eq_zero_exterior (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) (hE : 0 < E) {h : ℝ → ℂ}
    {u : Lp ℂ 2 (volume : Measure ℂ)} (hu : IsReconSol γ E h u) :
    ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), u z = 0 := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : ℂ)
  obtain ⟨K, hK⟩ := hγ.lipschitz
  refine ae_eq_zero_of_helmholtz hE isClosed_closure.isOpen_compl
    (isConnected_compl_closure_of_frontier hb hL
      (by rw [← hγ.image]; exact isPreconnected_Icc.image γ hK.continuous.continuousOn))
    (R := R) (fun z hz hzc => by
      have := hR hzc; rw [Metric.mem_ball, dist_zero_right] at this; linarith)
    (Lp.memLp u) fun φ hφ => ?_
  rw [hu φ hφ.univ']
  unfold doubleLayer
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)), intervalIntegral.integral_zero]
  intro θ hθ
  rw [uIcc_of_le (by positivity)] at hθ
  have hnot : γ θ ∉ tsupport φ := fun h' =>
    hφ.2.2 h' (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ))
  simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]

def restrictL2 (Ω : Set ℂ) : Lp ℂ 2 (volume : Measure ℂ) →ₗ[ℂ] L2 Ω where
  toFun u := MemLp.toLp u ((Lp.memLp u).restrict Ω)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (u + v)).restrict Ω),
      Lp.coeFn_add (MemLp.toLp u ((Lp.memLp u).restrict Ω)) (MemLp.toLp v ((Lp.memLp v).restrict Ω)),
      MemLp.coeFn_toLp ((Lp.memLp u).restrict Ω), MemLp.coeFn_toLp ((Lp.memLp v).restrict Ω),
      ae_restrict_of_ae (Lp.coeFn_add u v)] with _ h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • u)).restrict Ω),
      Lp.coeFn_smul c (MemLp.toLp u ((Lp.memLp u).restrict Ω)),
      MemLp.coeFn_toLp ((Lp.memLp u).restrict Ω),
      ae_restrict_of_ae (Lp.coeFn_smul c u)] with _ h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply]

private lemma integral_eq_setIntegral_of_exterior (hγ : IsBoundaryParam Ω γ) (hΩo : IsOpen Ω)
    {f : ℂ → ℂ} (hf : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), f z = 0) :
    ∫ z, f z = ∫ z in Ω, f z := by
  refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
  filter_upwards [(ae_restrict_iff' isClosed_closure.isOpen_compl.measurableSet).mp hf,
    ae_mem_or_mem_exterior hγ hΩo] with z h1 h2 h3
  exact h2.elim (fun h => absurd h h3) h1

private lemma integrable_bdd_mul_test {f : ℂ → ℂ} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {D : Set ℂ} {φ : ℂ → ℂ}
    (hφ : TestFunction D φ) : Integrable (fun z => f z * φ z) μ :=
  (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).bdd_mul hf (Eventually.of_forall hC)

private lemma norm_dirD_le_of_lipschitz {V : ℂ → ℂ} {K : NNReal} (hV : LipschitzWith K V)
    (v z : ℂ) : ‖dirD V v z‖ ≤ K * ‖v‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hV) (norm_nonneg _))

private lemma aestronglyMeasurable_dirD (V : ℂ → ℂ) (v : ℂ) {μ : Measure ℂ} :
    AEStronglyMeasurable (dirD V v) μ :=
  (measurable_fderiv_apply_const ℝ V v).aestronglyMeasurable

private theorem exists_reconSol_props (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) (hE : 0 < E) {h : ℝ → ℂ}
    (hh : h ∈ compatibleTraces γ E) :
    ∃ u : Lp ℂ 2 (volume : Measure ℂ), IsReconSol γ E h u ∧
      restrictL2 Ω u ∈ neumannEigenspace Ω E ∧
      (restrictL2 Ω u = 0 → ∀ θ ∈ Icc 0 (2 * π), h θ = 0) := by
  have hΩo : IsOpen Ω := hL.1.1
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  have hUm : MeasurableSet (closure Ω)ᶜ := isClosed_closure.isOpen_compl.measurableSet
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hb.measure_lt_top⟩
  obtain ⟨⟨Kh, hKh⟩, hper, -⟩ := id hh
  obtain ⟨V, ⟨KV, hV⟩, hVc, hVh⟩ := exists_lipschitz_extension_of_trace hL hγ hKh hper
  obtain ⟨CV, hCV⟩ := hVc.exists_bound_of_continuous hV.continuous
  have hmem_ind : ∀ {f : ℂ → ℂ}, AEStronglyMeasurable f volume → ∀ {C : ℝ},
      (∀ z, ‖f z‖ ≤ C) → MemLp (Ω.indicator f) 2 volume := fun {f} hf {C} hC =>
    (memLp_indicator_iff_restrict hΩm).mpr (MemLp.of_bound hf.restrict C (Eventually.of_forall hC))
  have hcs_ind : ∀ f : ℂ → ℂ, HasCompactSupport (Ω.indicator f) := fun f =>
    IsCompact.of_isClosed_subset hb.isCompact_closure (isClosed_tsupport _)
      (closure_mono support_indicator_subset)
  set G : ℂ → ℂ := Ω.indicator V
  set G' : Fin 2 → ℂ → ℂ := fun i => Ω.indicator (dirD V (coordDir i))
  have hGm : MemLp G 2 volume := hmem_ind hV.continuous.aestronglyMeasurable hCV
  have hG'm : ∀ i, MemLp (G' i) 2 volume := fun i =>
    hmem_ind (aestronglyMeasurable_dirD V _) (norm_dirD_le_of_lipschitz hV _)
  have hgreen : ∀ φ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ →
      ∫ z, (G z * lap φ z + ∑ i : Fin 2, G' i z * dirD φ (coordDir i) z) =
        doubleLayer γ h φ := fun φ hφ => by
    rw [show ∫ z, (G z * lap φ z + ∑ i : Fin 2, G' i z * dirD φ (coordDir i) z) =
        ∫ z in Ω, (V z * lap φ z + ∑ i : Fin 2, dirD V (coordDir i) z * dirD φ (coordDir i) z) by
      rw [← integral_indicator hΩm]; congr 1; funext z
      by_cases hz : z ∈ Ω <;> simp [G, G', hz],
      doubleLayer_eq_integral hb hL hγ hV hVc hVh hφ]
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨w, gw, hw, hgw, hwg, heq⟩ := exists_helmholtz_solution hE hGm (hcs_ind V) hG'm
    (fun i => hcs_ind _) fun ξ hξ => by
      rw [hgreen _ (by
        unfold ePlane
        exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
          (Complex.reCLM.contDiff.comp (Complex.conjCLE.contDiff.mul contDiff_const)))))]
      exact doubleLayer_ePlane_eq_zero hK hE hh hξ
  set u : Lp ℂ 2 (volume : Measure ℂ) := (hGm.add hw).toLp _
  have hue : (u : ℂ → ℂ) =ᵐ[volume] fun z => G z + w z := MemLp.coeFn_toLp _
  have hu : IsReconSol γ E h u := fun φ hφ => by
    rw [integral_congr_ae (hue.mono fun _ hz => by rw [hz]), heq φ hφ, hgreen φ hφ.1]
  have hext := hu.ae_eq_zero_exterior hb hL hγ hE
  have hw0 : ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), w z = 0 := by
    filter_upwards [hext, ae_restrict_of_ae hue, ae_restrict_mem hUm] with z h1 h2 h3
    have hzΩ : z ∉ Ω := fun h' => h3 (subset_closure h')
    rw [h2] at h1; simpa [G, hzΩ] using h1
  have hgw0 : ∀ i, ∀ᵐ z ∂(volume.restrict (closure Ω)ᶜ), gw i z = 0 := fun i => by
    have hUo : IsOpen (closure Ω)ᶜ := isClosed_closure.isOpen_compl
    refine ae_eq_zero_of_integral_mul_test hUo ((hgw i).locallyIntegrable (by norm_num)) fun φ hφ => ?_
    have e := hwg φ hφ.univ' i
    have hz : ∫ z, w z * fderiv ℝ φ z (coordDir i) = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℂ)), integral_zero]
      filter_upwards [(ae_restrict_iff' hUm).mp hw0] with z hz
      by_cases hzU : z ∈ (closure Ω)ᶜ
      · rw [hz hzU, zero_mul]
      · simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) fun h' => hzU (hφ.2.2 h')]
    rw [hz, eq_comm, neg_eq_zero] at e; exact e
  have hrcoe : (restrictL2 Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] u :=
    MemLp.coeFn_toLp ((Lp.memLp u).restrict Ω)
  refine ⟨u, hu, ?_, ?_⟩
  · have hgm : ∀ i, MemLp (fun z => dirD V (coordDir i) z + gw i z) 2 (volume.restrict Ω) :=
      fun i => (MemLp.of_bound (aestronglyMeasurable_dirD V _) _
        (Eventually.of_forall (norm_dirD_le_of_lipschitz hV _))).add ((hgw i).restrict Ω)
    set g : Fin 2 → L2 Ω := fun i => (hgm i).toLp _ with hgdef
    have hUe : (restrictL2 Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => V z + w z := by
      filter_upwards [hrcoe, ae_restrict_of_ae hue, ae_restrict_mem hΩm] with z h1 h2 h3
      dsimp only [G] at h2
      rw [h1, h2, indicator_of_mem h3]
    refine ⟨g, fun φ hφ i => ?_, fun v hv hvg => ?_⟩
    · have hφ' := hφ.univ'
      have hoff : ∀ z, z ∉ Ω → fderiv ℝ φ z (coordDir i) = 0 := fun z hz => by
        simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) fun h' => hz (hφ.2.2 h')]
      have hoff' : ∀ z, z ∉ Ω → φ z = 0 := fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h' => hz (hφ.2.2 h')
      have hiV : Integrable (fun z => V z * fderiv ℝ φ z (coordDir i)) :=
        integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV (hφ'.dirD (coordDir i))
      have hiw : Integrable (fun z => w z * fderiv ℝ φ z (coordDir i)) :=
        integrable_mul_test hw (hφ'.dirD (coordDir i))
      have hiDV : Integrable (fun z => dirD V (coordDir i) z * φ z) :=
        integrable_bdd_mul_test (aestronglyMeasurable_dirD V _) (norm_dirD_le_of_lipschitz hV _) hφ'
      have hig : Integrable (fun z => gw i z * φ z) := integrable_mul_test (hgw i) hφ'
      have e1 : ∫ z in Ω, (restrictL2 Ω u : ℂ → ℂ) z * fderiv ℝ φ z (coordDir i) =
          ∫ z, (V z * fderiv ℝ φ z (coordDir i) + w z * fderiv ℝ φ z (coordDir i)) := by
        rw [integral_congr_ae (g := fun z => V z * fderiv ℝ φ z (coordDir i) +
            w z * fderiv ℝ φ z (coordDir i))]
        · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [hoff z hz]
        · filter_upwards [hUe] with _ hz; rw [hz, add_mul]
      have e2 : ∫ z in Ω, (g i : ℂ → ℂ) z * φ z =
          ∫ z, (dirD V (coordDir i) z * φ z + gw i z * φ z) := by
        rw [integral_congr_ae (g := fun z => dirD V (coordDir i) z * φ z + gw i z * φ z)]
        · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [hoff' z hz]
        · filter_upwards [MemLp.coeFn_toLp (hgm i)] with _ hz
          rw [hgdef]; simp only; rw [hz, add_mul]
      rw [e1, e2, integral_add hiV hiw, integral_add hiDV hig,
        integral_mul_fderiv_of_lipschitz hV (hφ.1.of_le (by exact_mod_cast le_top)) hφ.2.1,
        hwg φ hφ' i, neg_add]
      rfl
    · obtain ⟨φ, hφ, hconv, hdconv⟩ := exists_testFunction_approx hb hL hvg
      set Φ : ℕ → L2 Ω := fun n => ((hφ n).memLp' 2).toLp (φ n) with hΦ
      set DΦ : ℕ → Fin 2 → L2 Ω := fun n i => (((hφ n).dirD (coordDir i)).memLp' 2).toLp _ with hDΦ
      have hkey : ∀ n, ∑ i, inner ℂ (DΦ n i) (g i) = (E : ℂ) * inner ℂ (Φ n) (restrictL2 Ω u) := by
        intro n
        set ψ : ℂ → ℂ := fun z => conj (φ n z)
        have hψ : TestFunction univ ψ := (hφ n).conj
        have h1 := hu ψ hψ
        rw [doubleLayer_eq_integral hb hL hγ hV hVc hVh hψ.1,
          show (fun z => u z * (lap ψ z + E * ψ z)) =
            fun z => u z * lap ψ z + u z * (E * ψ z) from funext fun _ => mul_add _ _ _,
          integral_add (integrable_mul_test (Lp.memLp u) hψ.lap)
            (integrable_mul_test (Lp.memLp u) (hψ.const_mul _))] at h1
        have hlap : ∫ z, u z * lap ψ z = (∫ z in Ω, V z * lap ψ z) -
            ∑ i : Fin 2, ∫ z in Ω, gw i z * dirD ψ (coordDir i) z := by
          have hiV : Integrable (fun z => G z * lap ψ z) :=
            integrable_bdd_mul_test (hV.continuous.aestronglyMeasurable.indicator hΩm)
              (C := CV) (fun z => by
                by_cases hz : z ∈ Ω <;> simp [G, hz, hCV z]
                exact (norm_nonneg _).trans (hCV z)) hψ.lap
          rw [integral_congr_ae (g := fun z => G z * lap ψ z + w z * lap ψ z),
            integral_add hiV (integrable_mul_test hw hψ.lap),
            show ∫ z, G z * lap ψ z = ∫ z in Ω, V z * lap ψ z by
              rw [← integral_indicator hΩm]; congr 1; funext z
              by_cases hz : z ∈ Ω <;> simp [G, hz]]
          swap
          · filter_upwards [hue] with _ hz; rw [hz, add_mul]
          have e0 := hwg (dirD ψ 1) (hψ.dirD 1) 0
          have e1 := hwg (dirD ψ Complex.I) (hψ.dirD Complex.I) 1
          have hwl : ∫ z, w z * lap ψ z =
              -∑ i : Fin 2, ∫ z, gw i z * dirD ψ (coordDir i) z := by
            unfold lap; simp_rw [mul_add]
            rw [integral_add (integrable_mul_test hw ((hψ.dirD 1).dirD 1))
                (integrable_mul_test hw ((hψ.dirD _).dirD _)),
              Fin.sum_univ_two, show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl]
            unfold dirD at e0 e1 ⊢; rw [show coordDir 0 = 1 from rfl] at e0
            rw [show coordDir 1 = Complex.I from rfl] at e1; rw [e0, e1]; ring
          rw [hwl, ← sub_eq_add_neg]; congr 1
          refine Finset.sum_congr rfl fun i _ => integral_eq_setIntegral_of_exterior hγ hΩo ?_
          filter_upwards [hgw0 i] with _ hz; rw [hz, zero_mul]
        have hEu : ∫ z, u z * (E * ψ z) = E * ∫ z in Ω, ψ z * u z := by
          rw [integral_eq_setIntegral_of_exterior hγ hΩo, ← integral_const_mul]
          · congr 1; funext _; ring
          · filter_upwards [hext] with _ hz; rw [hz, zero_mul]
        have hiVl := integrable_bdd_mul_test (μ := volume.restrict Ω)
          hV.continuous.aestronglyMeasurable hCV hψ.lap
        have hiVd : ∀ i : Fin 2, Integrable (fun z => dirD V (coordDir i) z * dirD ψ (coordDir i) z)
            (volume.restrict Ω) := fun i =>
          integrable_bdd_mul_test (aestronglyMeasurable_dirD V _)
            (norm_dirD_le_of_lipschitz hV _) (hψ.dirD _)
        have hig : ∀ i : Fin 2, Integrable (fun z => gw i z * dirD ψ (coordDir i) z)
            (volume.restrict Ω) := fun i => integrable_mul_test ((hgw i).restrict Ω) (hψ.dirD _)
        rw [hlap, hEu, integral_add hiVl (integrable_finset_sum _ fun i _ => hiVd i),
          integral_finset_sum _ fun i _ => hiVd i] at h1
        have hsp : ∑ i : Fin 2, ∫ z in Ω, dirD ψ (coordDir i) z * (dirD V (coordDir i) z + gw i z) =
            E * ∫ z in Ω, ψ z * u z := by
          have hsplit : ∀ i : Fin 2, ∫ z in Ω, dirD ψ (coordDir i) z *
              (dirD V (coordDir i) z + gw i z) =
              (∫ z in Ω, dirD V (coordDir i) z * dirD ψ (coordDir i) z) +
                ∫ z in Ω, gw i z * dirD ψ (coordDir i) z := fun i => by
            rw [integral_congr_ae (g := fun z => dirD V (coordDir i) z * dirD ψ (coordDir i) z +
              gw i z * dirD ψ (coordDir i) z)]
            · exact integral_add (hiVd i) (hig i)
            · exact Eventually.of_forall fun _ => by simp only; ring
          simp only [hsplit, Finset.sum_add_distrib]; linear_combination -h1
        simp only [L2.inner_def, RCLike.inner_apply']
        convert hsp using 1
        · refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
          filter_upwards [MemLp.coeFn_toLp
              (((hφ n).dirD (coordDir i)).memLp' 2 (μ := volume.restrict Ω)),
            MemLp.coeFn_toLp (hgm i)] with _ ha1 ha2
          rw [ha1, ha2, dirD_conj ((hφ n).1.of_le (by exact_mod_cast le_top))]
        · congr 1; refine integral_congr_ae ?_
          filter_upwards [MemLp.coeFn_toLp ((hφ n).memLp' 2 (μ := volume.restrict Ω)),
            hrcoe] with _ ha1 ha2
          rw [ha1, ha2]
      have hΦt : Tendsto Φ atTop (𝓝 v) := by
        rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
        refine hconv.congr fun n => eLpNorm_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp ((hφ n).memLp' 2 (μ := volume.restrict Ω))] with _ hz
        simp only [Pi.sub_apply, hΦ, hz]
      have hDΦt : ∀ i, Tendsto (fun n => DΦ n i) atTop (𝓝 (hv i)) := fun i => by
        rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
        refine (hdconv i).congr fun n => eLpNorm_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp
          (((hφ n).dirD (coordDir i)).memLp' 2 (μ := volume.restrict Ω))] with _ hz
        simp only [Pi.sub_apply, hDΦ, hz]; rfl
      exact tendsto_nhds_unique
        ((tendsto_finset_sum _ fun i _ => (hDΦt i).inner tendsto_const_nhds).congr hkey)
        ((hΦt.inner tendsto_const_nhds).const_mul _)
  · intro h0
    have hΩ0 : ∀ᵐ z ∂(volume.restrict Ω), u z = 0 := by
      filter_upwards [hrcoe, Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with _ h1 h2
      rw [← h1, h0, h2]; rfl
    have hu0 : ∀ᵐ z ∂(volume : Measure ℂ), u z = 0 := by
      filter_upwards [(ae_restrict_iff' hΩm).mp hΩ0, (ae_restrict_iff' hUm).mp hext,
        ae_mem_or_mem_exterior hγ hΩo] with _ h1 h2 h3
      exact h3.elim h1 h2
    have hwV : ∀ᵐ z ∂(volume : Measure ℂ), w z = -G z := by
      filter_upwards [hu0, hue] with _ h1 h2
      rw [h2] at h1; linear_combination h1
    have hgV : ∀ i, ∀ᵐ z ∂(volume.restrict Ω), gw i z + dirD V (coordDir i) z = 0 := fun i => by
      have hloc : LocallyIntegrable (fun z => gw i z + dirD V (coordDir i) z) volume :=
        ((hgw i).locallyIntegrable (by norm_num)).add ((memLp_top_of_bound
          (aestronglyMeasurable_dirD V _) _ (Eventually.of_forall
            (norm_dirD_le_of_lipschitz hV _))).locallyIntegrable le_top)
      refine ae_eq_zero_of_integral_mul_test hΩo hloc fun χ hχ => ?_
      have hχ' := hχ.univ'
      have e1 := hwg χ hχ' i
      have e2 := integral_mul_fderiv_of_lipschitz hV (hχ.1.of_le (by exact_mod_cast le_top))
        hχ.2.1 (coordDir i)
      have e3 : ∫ z, w z * fderiv ℝ χ z (coordDir i) = -∫ z, V z * fderiv ℝ χ z (coordDir i) := by
        rw [← integral_neg]; refine integral_congr_ae ?_
        filter_upwards [hwV] with z hz
        rw [hz]
        by_cases hzΩ : z ∈ Ω
        · simp [G, hzΩ]
        · simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) fun h' => hzΩ (hχ.2.2 h')]
      rw [show (fun z => (gw i z + dirD V (coordDir i) z) * χ z) =
          fun z => gw i z * χ z + dirD V (coordDir i) z * χ z from funext fun _ => add_mul _ _ _,
        integral_add (integrable_mul_test (hgw i) hχ')
          (integrable_bdd_mul_test (aestronglyMeasurable_dirD V _)
            (norm_dirD_le_of_lipschitz hV _) hχ')]
      unfold dirD; rw [e3, e2, neg_neg] at e1; linear_combination e1
    have hstar : ∀ φ : ℂ → ℂ, TestFunction univ φ → ∀ i : Fin 2,
        ∫ z in Ω, (V z * fderiv ℝ φ z (coordDir i) + dirD V (coordDir i) z * φ z) = 0 :=
      fun φ hφ i => by
        have e1 := hwg φ hφ i
        have e2 : ∫ z, w z * fderiv ℝ φ z (coordDir i) = -∫ z in Ω, V z * fderiv ℝ φ z (coordDir i) := by
          rw [← integral_neg, ← integral_indicator hΩm]; refine integral_congr_ae ?_
          filter_upwards [hwV] with z hz
          rw [hz]; by_cases hzΩ : z ∈ Ω <;> simp [G, hzΩ]
        have e3 : ∫ z, gw i z * φ z = -∫ z in Ω, dirD V (coordDir i) z * φ z := by
          rw [integral_eq_setIntegral_of_exterior hγ hΩo, ← integral_neg]
          · refine integral_congr_ae ?_
            filter_upwards [hgV i] with _ hz
            rw [eq_neg_of_add_eq_zero_left hz]; ring
          · filter_upwards [hgw0 i] with _ hz; rw [hz, zero_mul]
        have hiV : Integrable (fun z => V z * fderiv ℝ φ z (coordDir i)) (volume.restrict Ω) :=
          integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV (hφ.dirD (coordDir i))
        have hiD : Integrable (fun z => dirD V (coordDir i) z * φ z) (volume.restrict Ω) :=
          integrable_bdd_mul_test (aestronglyMeasurable_dirD V _)
            (norm_dirD_le_of_lipschitz hV _) hφ
        rw [integral_add hiV hiD]
        rw [e2, e3] at e1; linear_combination -e1
    have hdbar : ∀ φ : ℂ → ℂ, TestFunction univ φ → ∫ z in Ω, dbar (fun z => V z * φ z) z = 0 :=
      fun φ hφ => by
        have hiV : ∀ i : Fin 2, Integrable (fun z => V z * fderiv ℝ φ z (coordDir i) +
            dirD V (coordDir i) z * φ z) (volume.restrict Ω) := fun i =>
          (integrable_bdd_mul_test hV.continuous.aestronglyMeasurable hCV
            (hφ.dirD (coordDir i))).add
          (integrable_bdd_mul_test (aestronglyMeasurable_dirD V _)
            (norm_dirD_le_of_lipschitz hV _) hφ)
        rw [integral_congr_ae (g := fun z => ((V z * fderiv ℝ φ z (coordDir 0) +
            dirD V (coordDir 0) z * φ z) + Complex.I * (V z * fderiv ℝ φ z (coordDir 1) +
            dirD V (coordDir 1) z * φ z)) / 2)]
        · rw [integral_div, integral_add (hiV 0) ((hiV 1).const_mul _), integral_const_mul,
            hstar φ hφ 0, hstar φ hφ 1]
          simp
        · refine ae_restrict_of_ae (hV.ae_differentiableAt.mono fun z hz => ?_)
          unfold dbar dirD
          rw [fderiv_fun_mul hz ((hφ.1.differentiable (by simp)) z)]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
            show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl]
          ring
    refine eq_zero_of_integral_comp_mul_deriv hγ hKh.continuousOn fun φ hφ => ?_
    obtain ⟨Cφ, hCφ⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
    obtain ⟨Kφ, hKφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
    obtain ⟨Kp, hKp⟩ := lipschitzWith_mul_of_bounded hV hKφ hCV hCφ
    have hg := integral_boundary_eq_dbar hb hL hγ hKp hVc.mul_right
    rw [hdbar φ hφ, mul_zero] at hg; rw [← hg]
    exact intervalIntegral.integral_congr fun θ hθ => by
      rw [uIcc_of_le (by positivity)] at hθ; simp only [hVh θ hθ]

/-- Lemma 4.8 with zero conormal data and the uniqueness of Lemma 4.9: a linear reconstruction
map from compatible traces to Neumann eigenfunctions that only kills traces vanishing on
`[0, 2π]`. -/
theorem neumann_reconstruction_of_compatible (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (hE : 0 < E) :
    ∃ R : compatibleTraces γ E →ₗ[ℂ] neumannEigenspace Ω E,
      ∀ h, R h = 0 → ∀ θ ∈ Icc 0 (2 * π), (h : ℝ → ℂ) θ = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  choose F hspec hmem htr0 using fun h : compatibleTraces γ E =>
    exists_reconSol_props hb hL hγ hE h.2
  have hcont : ∀ h : compatibleTraces γ E, ContinuousOn (h : ℝ → ℂ) (Icc 0 (2 * π)) :=
    fun ⟨_, ⟨_, hKh⟩, _, _⟩ => hKh.continuousOn
  have hadd : ∀ h₁ h₂ : compatibleTraces γ E, F (h₁ + h₂) = F h₁ + F h₂ := fun h₁ h₂ =>
    (hspec (h₁ + h₂)).unique hE fun φ hφ => by
      have hi : ∀ u : Lp ℂ 2 (volume : Measure ℂ),
          Integrable (fun z => u z * (lap φ z + E * φ z)) := fun u =>
        integrable_mul_test (Lp.memLp u) (hφ.helm E)
      rw [integral_congr_ae ((Lp.coeFn_add (F h₁) (F h₂)).mono fun _ hz => by
          rw [hz, Pi.add_apply, add_mul]),
        integral_add (hi _) (hi _), hspec h₁ φ hφ, hspec h₂ φ hφ, Submodule.coe_add,
        doubleLayer_add hK (hcont h₁) (hcont h₂) (hφ.1.of_le (by exact_mod_cast le_top))]
  have hsmul : ∀ (c : ℂ) (h : compatibleTraces γ E), F (c • h) = c • F h := fun c h =>
    (hspec (c • h)).unique hE fun φ hφ => by
      rw [integral_congr_ae ((Lp.coeFn_smul c (F h)).mono fun _ hz => by
          rw [hz, Pi.smul_apply, smul_eq_mul, mul_assoc]),
        integral_const_mul, hspec h φ hφ, Submodule.coe_smul]
      unfold doubleLayer
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  let Flin : compatibleTraces γ E →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  exact ⟨((restrictL2 Ω).comp Flin).codRestrict (neumannEigenspace Ω E) hmem,
    fun h h0 => htr0 h (congrArg Subtype.val h0)⟩

end Recon

end PolyaNeumann
