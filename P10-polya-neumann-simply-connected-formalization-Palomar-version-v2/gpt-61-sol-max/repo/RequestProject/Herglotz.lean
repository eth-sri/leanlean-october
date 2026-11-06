module

public import RequestProject.PlanarTypes
public import Mathlib.Tactic.FunProp

public import RequestProject.PlanarGeometry

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import RequestProject.Driven
public import RequestProject.ArcLength
public import RequestProject.Observation

/-!
# Herglotz waves and their driven transport equation (Lemma 4.4)

For `E = k² ≥ 0` and a direction density `a ∈ L²(0, 2π)`, the Herglotz wave is
`u_a(z) = (2π)⁻¹ ∫₀^{2π} a(φ) e^{-ik Re(z e^{-iφ})} dφ`.
Its "holomorphic jets" `y_{a,n} = (2i/k)ⁿ ∂ⁿ u_a` are the coefficients
`F_n(z) = (2π)⁻¹ ∫₀^{2π} a(φ) e^{-inφ} e^{-ik Re(z e^{-iφ})} dφ` (`herglotzCoeff`), the Fourier
coefficients of `a · e^{-ik Re(z e^{-i·})}`. The vector
`y_a(z) = (F_0(z)/√2, F_1(z), F_2(z), …)` lies in `ℓ²(ℕ₀)` by Parseval (`herglotzVec`).

Along a Lipschitz curve `γ` we prove Lemma 4.4 of the paper (`herglotz_driven`):
`y_a ∘ γ` is continuous and satisfies the driven transport equation
`y_a' = C_E y_a - (i/√2) g_a e₀` in integral form, where
`g_a(θ) = D u_a(γ(θ)) (-i γ'(θ))` is the conormal derivative `|γ'| ∂_ν u_a` (`herglotzConormal`);
moreover `h_a = u_a ∘ γ` satisfies `h_a' = -i g_a - i k γ' y_{a,1}`.

As a consequence (the pairing step of Lemma 10.5) a fixed vector `v` of `V_E = W_E(L)` has an
observation `O_E v` orthogonal to every Herglotz conormal trace:
`∫₀^{2π} conj(g_a) (O_E v) = 0` (`integral_conj_herglotzConormal_mul_observation`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

/-- The plane wave `e^{-ik Re(z e^{-iφ})}`. -/
def planeWave (k : ℝ) z (φ : ℝ)  :=
  Complex.exp (-(Complex.I * k) * ((z * Complex.exp (-(φ * Complex.I))).re : ℂ))

/-- The Herglotz coefficients `F_m(z) = (2π)⁻¹ ∫₀^{2π} e^{-imφ} a(φ) e^{-ik Re(z e^{-iφ})} dφ`.
For `m ≥ 1`, `F_m = (2i/k)^m ∂^m u_a`. -/
def herglotzCoeff k (a : ComplexCurve) (m : ℤ) z  :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod,
    Complex.exp (-((m : ℂ) * φ * Complex.I)) * (a φ * planeWave k z φ)

/-- The Herglotz wave `u_a(z) = (2π)⁻¹ ∫₀^{2π} a(φ) e^{-ik Re(z e^{-iφ})} dφ`. -/
def herglotzWave k (a : ComplexCurve) z  :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, a φ * planeWave k z φ

/-- The coordinates `y_{a,0} = u_a/√2`, `y_{a,n} = F_n` (`n ≥ 1`) of the Herglotz vector. -/
def herglotzSeq k a z (n : ℕ)  :=
  if n = 0 then herglotzCoeff k a 0 z / (Real.sqrt 2 : ℂ) else herglotzCoeff k a n z

/-- The conormal derivative `g_a(θ) = |γ'(θ)| (∂_ν u_a)(γ(θ))` of the Herglotz wave along `γ`,
with outward unit normal `-iγ'/|γ'|`: the derivative of `u_a` at `γ(θ)` in the direction
`-i γ'(θ)`. -/
def herglotzConormal k a γ (θ : ℝ)  :=
  fderiv ℝ (herglotzWave k a) (γ θ) (-(Complex.I * deriv γ θ))

/-- `L²` direction densities on `(0, 2π]`. -/
abbrev IsDirDensity (a : ComplexCurve)  := MemLp a 2 (volume.restrict boundaryHalfOpenInterval)

/-! ### Basic properties -/

lemma planeWave_eq k z φ :
    planeWave k z φ = Complex.exp (Complex.I *
      ((-(k * (z * Complex.exp (-(φ * Complex.I))).re) : ℝ) : ℂ)) := by
  unfold planeWave
  push_cast
  ring

lemma norm_planeWave k z φ : ‖planeWave k z φ‖ = 1 := by
  rw [planeWave_eq, Complex.norm_exp_I_mul_ofReal]

lemma norm_exp_neg_mul_I (φ : ℝ) : ‖Complex.exp (-(φ * Complex.I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

lemma norm_planeWave_sub_le k z w φ :
    ‖planeWave k z φ - planeWave k w φ‖ ≤ |k| * ‖z - w‖ := by
  set e := Complex.exp (-(φ * Complex.I))
  have h : planeWave k z φ - planeWave k w φ = planeWave k w φ *
      (Complex.exp (Complex.I * ((-(k * ((z - w) * e).re) : ℝ) : ℂ)) - 1) := by
    rw [planeWave_eq, planeWave_eq, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    simp  
    push_cast
    ring
  rw [h, norm_mul, norm_planeWave, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul]
  gcongr
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_exp_neg_mul_I, mul_one]

lemma herglotzWave_eq k a z :
    herglotzWave k a z = herglotzCoeff k a 0 z := by
  simp [herglotzWave, herglotzCoeff]

@[fun_prop]
lemma continuous_planeWave k z : Continuous (planeWave k z) := by
  unfold planeWave
  fun_prop

@[fun_prop]
lemma continuous_exp_neg_mul (m : ℤ) :
    Continuous fun φ : ℝ => Complex.exp (-((m : ℂ) * φ * Complex.I)) := by
  fun_prop

/-- The normalized Fourier integral on `[0, 2π]` is `fourierCoeffOn`. -/
lemma coeffIntegral_eq_fourierCoeffOn f (m : ℤ) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, Complex.exp (-((m : ℂ) * φ * Complex.I)) * f φ =
      fourierCoeffOn Real.two_pi_pos f m := by
  rw [fourierCoeffOn_eq_integral, Complex.real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun φ _ => ?_
    rw [fourier_coe_apply]
    congr 2
    have : (2 * π - 0 : ℝ) = 2 * π := by ring
    rw [this]
    push_cast
    field_simp

lemma intervalIntegrable_herglotz  (ha : IntervalIntegrable a volume 0 circlePeriod)
    k (m : ℤ) z :
    IntervalIntegrable (fun φ => Complex.exp (-((m : ℂ) * φ * Complex.I)) *
      (a φ * planeWave k z φ)) volume 0 circlePeriod := by
  have := ha.continuousOn_mul
    ((continuous_exp_neg_mul m).mul (continuous_planeWave k z)).continuousOn
  exact this.congr fun φ _ => by simp  ; ring

lemma herglotzCoeff_eq_fourierCoeffOn k a m z :
    herglotzCoeff k a m z =
      fourierCoeffOn Real.two_pi_pos (fun φ => a φ * planeWave k z φ) m :=
  coeffIntegral_eq_fourierCoeffOn _ m

lemma IsDirDensity.intervalIntegrable  (ha : IsDirDensity a) :
    IntervalIntegrable a volume 0 circlePeriod := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  exact ha.integrable (by norm_num)

section
variable {a } (ha : IsDirDensity a) (k : ℝ)

section
include a ha k

/-- Parseval for the differences of Herglotz coefficients. -/
lemma hasSum_sq_herglotzCoeff_sub z w :
    HasSum (fun m : ℤ => ‖herglotzCoeff k a m z - herglotzCoeff k a m w‖ ^ 2)
      (circlePeriod⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, ‖a φ‖ ^ 2 * ‖planeWave k z φ - planeWave k w φ‖ ^ 2) := by
  have hai := ha.intervalIntegrable
  have hdiff : ∀ m : ℤ, herglotzCoeff k a m z - herglotzCoeff k a m w =
      fourierCoeffOn Real.two_pi_pos (fun φ => a φ * (planeWave k z φ - planeWave k w φ)) m := by
    intro m
    rw [← coeffIntegral_eq_fourierCoeffOn, herglotzCoeff, herglotzCoeff, ← mul_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_herglotz hai k m z)
        (intervalIntegrable_herglotz hai k m w)]
    grind
  simp_rw [hdiff]
  have hb : MemLp (((planeWave k z - planeWave k w))) ⊤
      (volume.restrict boundaryHalfOpenInterval) := by
    refine memLp_top_of_bound ((continuous_planeWave k z).sub
      (continuous_planeWave k w)).aestronglyMeasurable 2 (Eventually.of_forall fun φ => ?_)
    refine (norm_sub_le _ _).trans ?_
    grind only [norm_planeWave]
  have hm : MemLp (fun φ => a φ * (planeWave k z φ - planeWave k w φ)) 2
      (volume.restrict boundaryHalfOpenInterval) := by
    have := ha.mul' (r := 2) hb
    assumption
  convert hasSum_sq_fourierCoeffOn Real.two_pi_pos hm using 1
  rw [smul_eq_mul, sub_zero]
  congr 1
  simp  [mul_pow]

lemma summable_sq_herglotzCoeff z :
    Summable (fun m : ℤ => ‖herglotzCoeff k a m z‖ ^ 2) := by
  have hm : MemLp (((a * planeWave k z))) 2 (volume.restrict boundaryHalfOpenInterval) := by
    have hb : MemLp (planeWave k z) ⊤ (volume.restrict boundaryHalfOpenInterval) :=
      memLp_top_of_bound (continuous_planeWave k z).aestronglyMeasurable 1
        (Eventually.of_forall fun φ => (norm_planeWave k z φ).le)
    have := ha.mul' (r := 2) hb
    assumption
  simp_rw [herglotzCoeff_eq_fourierCoeffOn]
  exact (hasSum_sq_fourierCoeffOn Real.two_pi_pos hm).summable

end


lemma norm_herglotzSeq_le k a z w n :
    ‖herglotzSeq k a z n - herglotzSeq k a w n‖ ^ 2 ≤
      ‖herglotzCoeff k a n z - herglotzCoeff k a n w‖ ^ 2 := by
  unfold herglotzSeq
  split_ifs with h
  · subst h
    rw [← sub_div, norm_div]
    have h2 : (1 : ℝ) ≤ ‖(Real.sqrt 2 : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.one_le_sqrt.mpr (by norm_num)
    gcongr
    exact div_le_self (norm_nonneg _) h2
  · exact le_rfl

include a ha k in
lemma memℓp_herglotzSeq z :
    Memℓp (herglotzSeq k a z) 2 := by
  refine memℓp_of_summable_sq ?_
  have hs := (summable_sq_herglotzCoeff ha k z).comp_injective Nat.cast_injective
  refine hs.of_nonneg_of_le (fun _ => by positivity) fun n => ?_
  unfold herglotzSeq
  split_ifs with h
  · subst h
    show _ ≤ ‖herglotzCoeff k a ((0 : ℕ)) z‖ ^ 2
    rw [norm_div, Nat.cast_zero]
    have h2 : (1 : ℝ) ≤ ‖(Real.sqrt 2 : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.one_le_sqrt.mpr (by norm_num)
    gcongr
    exact div_le_self (norm_nonneg _) h2
  · exact le_rfl

/-- The Herglotz vector `y_a(z) = (u_a(z)/√2, F_1(z), F_2(z), …) ∈ ℓ²(ℕ₀)`. -/
def herglotzVec {a : ComplexCurve} (ha : IsDirDensity a) (k : ℝ) (z : ℂ) : Ell2 :=
  ⟨herglotzSeq k a z, memℓp_herglotzSeq ha k z⟩

section
include a ha k

@[simp] lemma herglotzVec_apply z n :
    (herglotzVec ha k z : ComplexSeq) n = herglotzSeq k a z n := rfl

/-- The Herglotz vector is Lipschitz in the base point. -/
lemma norm_herglotzVec_sub_le z w :
    ‖herglotzVec ha k z - herglotzVec ha k w‖ ≤
      |k| * Real.sqrt (circlePeriod⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, ‖a φ‖ ^ 2) * ‖z - w‖ := by
  set A := circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod, ‖a φ‖ ^ 2 with hA
  have hai2 : IntervalIntegrable (fun φ => ‖a φ‖ ^ 2) volume 0 circlePeriod := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    simpa [IntegrableOn] using ha.integrable_norm_rpow (by norm_num) (by norm_num)
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ∫ φ in (0 : ℝ)..circlePeriod, ‖a φ‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by positivity) fun _ _ => by positivity
    positivity
  have hsumZ := hasSum_sq_herglotzCoeff_sub ha k z w
  have hcoord : ∀ n, ((herglotzVec ha k z - herglotzVec ha k w : Ell2) : ComplexSeq) n =
      herglotzSeq k a z n - herglotzSeq k a w n := fun n => by
    rfl
  have hsq : ‖herglotzVec ha k z - herglotzVec ha k w‖ ^ 2 ≤ k ^ 2 * A * ‖z - w‖ ^ 2 := by
    rw [← tsum_sq_eq_norm_sq]
    calc ∑' n, ‖herglotzSeq k a z n - herglotzSeq k a w n‖ ^ 2
        ≤ ∑' n : ℕ, ‖herglotzCoeff k a n z - herglotzCoeff k a n w‖ ^ 2 := by
          refine Summable.tsum_le_tsum ((norm_herglotzSeq_le k a z w)) ?_
            (hsumZ.summable.comp_injective Nat.cast_injective)
          have := summable_sq (herglotzVec ha k z - herglotzVec ha k w)
          simpa [] using this
      _ ≤ ∑' m : ℤ, ‖herglotzCoeff k a m z - herglotzCoeff k a m w‖ ^ 2 :=
          Summable.tsum_le_tsum_of_inj ((↑)) Nat.cast_injective
            (fun _ _ => by positivity) (fun _ => le_rfl)
            (hsumZ.summable.comp_injective Nat.cast_injective) hsumZ.summable
      _ = circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod,
            ‖a φ‖ ^ 2 * ‖planeWave k z φ - planeWave k w φ‖ ^ 2 := hsumZ.tsum_eq
      _ ≤ circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod, ‖a φ‖ ^ 2 * (|k| * ‖z - w‖) ^ 2 := by
          gcongr
          refine intervalIntegral.integral_mono_on (by positivity) ?_ (hai2.mul_const _)
            fun φ _ => ?_
          · refine hai2.mul_continuousOn ?_
            exact (((continuous_planeWave k z).sub (continuous_planeWave k w)).norm.pow 2).continuousOn
          · gcongr
            exact norm_planeWave_sub_le k z w φ
      _ = k ^ 2 * A * ‖z - w‖ ^ 2 := by
          rw [intervalIntegral.integral_mul_const, hA, mul_pow, sq_abs]
          ring
  have hR : 0 ≤ |k| * Real.sqrt A * ‖z - w‖ := by positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp (hsq.trans (le_of_eq ?_))
  rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hA0]

lemma continuous_herglotzVec :
    Continuous (herglotzVec ha k) := by
  set C := |k| * Real.sqrt (circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod, ‖a φ‖ ^ 2)
  have hC : 0 ≤ C := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) fun z w => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_herglotzVec_sub_le ha k z w

end


end


/-! ### Derivatives -/

lemma norm_herglotzCoeff_le  k m z :
    ‖herglotzCoeff k a m z‖ ≤ circlePeriod⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, ‖a φ‖ := by
  rw [herglotzCoeff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp  [norm_planeWave]
  rw [Complex.norm_exp]
  simp

/-- The real-linear map `w ↦ Re(w e^{-iφ}) = (e^{-iφ} w + conj(e^{-iφ}) conj w)/2`, as a
complex-valued map. -/
def reMulCLM (φ : ℝ)  :=
  (Complex.exp (-(φ * Complex.I)) / 2) • ContinuousLinearMap.id ℝ ℂ +
    (conj (Complex.exp (-(φ * Complex.I))) / 2) • Complex.conjCLE.toContinuousLinearMap

lemma reMulCLM_apply φ w :
    reMulCLM φ w = Complex.exp (-(φ * Complex.I)) / 2 * w +
      conj (Complex.exp (-(φ * Complex.I))) / 2 * conj w := by
  simp [reMulCLM]

lemma reMulCLM_apply_eq_re φ w :
    reMulCLM φ w = ((w * Complex.exp (-(φ * Complex.I))).re : ℂ) := by
  rw [reMulCLM_apply, Complex.re_eq_add_conj, map_mul]
  ring

lemma norm_reMulCLM_le φ : ‖reMulCLM φ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [reMulCLM_apply_eq_re, Complex.norm_real, Real.norm_eq_abs, one_mul]
  refine (Complex.abs_re_le_norm _).trans ?_
  simp_all [norm_exp_neg_mul_I]

lemma continuous_reMulCLM : Continuous reMulCLM := by
  unfold reMulCLM
  fun_prop

lemma hasFDerivAt_planeWave k z φ :
    HasFDerivAt (fun z => planeWave k z φ)
      ((planeWave k z φ * -(Complex.I * k)) • reMulCLM φ) z := by
  set e := Complex.exp (-(φ * Complex.I))
  have hlin : (Complex.ofRealCLM.comp (Complex.reCLM.comp
      (((ContinuousLinearMap.mul ℂ ℂ).flip e).restrictScalars ℝ))) = reMulCLM φ := by
    ext1 w
    rw [reMulCLM_apply_eq_re]
    rfl
  have h1 : HasFDerivAt (fun z : ℂ => -(Complex.I * k) * ((z * e).re : ℂ))
      (-(Complex.I * k) • reMulCLM φ) z := by
    rw [← hlin]
    exact ((Complex.ofRealCLM.comp (Complex.reCLM.comp
      (((ContinuousLinearMap.mul ℂ ℂ).flip e).restrictScalars ℝ)))).hasFDerivAt.const_mul _
  have := h1.cexp
  rw [smul_smul] at this
  exact this

section
variable {a : ComplexCurve} (ha : IntervalIntegrable a volume 0 circlePeriod) (k : ℝ)
include a ha k

section
variable (m : ℤ)
include m

/-- The derivative of `F_m`: `D F_m(z) w = -(ik/2) (w F_{m+1}(z) + conj(w) F_{m-1}(z))`. -/
lemma hasFDerivAt_herglotzCoeff z :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (herglotzCoeff k a m) L z ∧ ∀ w, L w =
      -(Complex.I * k / 2) * (w * herglotzCoeff k a (m + 1) z +
        conj w * herglotzCoeff k a (m - 1) z) := by
  set c : ℂ := -(Complex.I * k)
  set ex : ComplexCurve := fun φ => Complex.exp (-(m * φ * Complex.I)) with hex
  set F : ℂ → ComplexCurve := fun z φ => ex φ * (a φ * planeWave k z φ) with hF
  set F' : ℂ → ℝ → ℂ →L[ℝ] ℂ := fun z φ => (ex φ * a φ * planeWave k z φ * c) • reMulCLM φ
    with hF'
  have ham  :=
    (intervalIntegrable_iff.mp ha).aestronglyMeasurable
  have hexc  := continuous_exp_neg_mul m
  have hnex : ∀ φ, ‖ex φ‖ = 1 := fun φ => by rw [hex, Complex.norm_exp]; simp
  have hF'meas  := fun z =>
    (((hexc.aestronglyMeasurable.mul ham).mul
      (continuous_planeWave k z).aestronglyMeasurable).mul_const c).smul
        continuous_reMulCLM.aestronglyMeasurable
  have hbound : ∀ z φ, ‖F' z φ‖ ≤ |k| * ‖a φ‖ := fun z φ => by
    simp only [hF', norm_smul, norm_mul, hnex, norm_planeWave, one_mul, mul_one]
    have hc : ‖c‖ = |k| := by simp [c, Complex.norm_real]
    rw [hc, mul_comm (‖a φ‖)]
    calc |k| * ‖a φ‖ * ‖reMulCLM φ‖ ≤ |k| * ‖a φ‖ * 1 := by gcongr; exact norm_reMulCLM_le φ
      _ = |k| * ‖a φ‖ := mul_one _
  have hbint : IntervalIntegrable (fun φ => |k| * ‖a φ‖) volume 0 circlePeriod := ha.norm.const_mul _
  have hF'int : ∀ z, IntervalIntegrable (F' z) volume 0 circlePeriod := fun z => by
    refine (intervalIntegrable_iff.mpr ?_)
    exact Integrable.mono' (intervalIntegrable_iff.mp hbint) (hF'meas z)
      (Eventually.of_forall (hbound z))
  have hdiff : ∀ z φ, HasFDerivAt (fun z => F z φ) (F' z φ) z := fun z φ => by
    have := (hasFDerivAt_planeWave k z φ).const_mul (ex φ * a φ)
    rw [smul_smul] at this
    convert this using 1
    · funext z; simp only [hF]; ring
    · simp only [hF']; congr 1; ring
  have hint  :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
      Filter.univ_mem (Eventually.of_forall fun z =>
        (intervalIntegrable_iff.mp (intervalIntegrable_herglotz ha k m z)).aestronglyMeasurable)
      (intervalIntegrable_herglotz ha k m z) (hF'meas z)
      (Eventually.of_forall fun φ _ z _ => hbound z φ) hbint
      (Eventually.of_forall fun φ _ z _ => hdiff z φ)
  refine ⟨(((2 * π : ℝ) : ℂ)⁻¹) • ∫ φ in (0)..circlePeriod, F' z φ, hint.const_mul _, fun w => ?_⟩
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.intervalIntegral_apply (hF'int z),
    smul_eq_mul, herglotzCoeff, herglotzCoeff]
  have h1 := intervalIntegrable_herglotz ha k (m + 1) z
  have h2 := intervalIntegrable_herglotz ha k (m - 1) z
  rw [show ∀ A B : ℂ, -(Complex.I * k / 2) * (w * (((2 * π : ℝ) : ℂ)⁻¹ * A) +
      conj w * (((2 * π : ℝ) : ℂ)⁻¹ * B)) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ((c / 2 * w) * A + (c / 2 * conj w) * B) from fun A B => by
        simp only [c]; ring]
  congr 1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (h1.const_mul _) (h2.const_mul _)]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [hF', ContinuousLinearMap.smul_apply, reMulCLM_apply, smul_eq_mul, hex]
  have e1 : Complex.exp (-((m : ℂ) * φ * Complex.I)) * Complex.exp (-(φ * Complex.I)) =
      Complex.exp (-(((m + 1 : ℤ) : ℂ) * φ * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (-((m : ℂ) * φ * Complex.I)) * conj (Complex.exp (-(φ * Complex.I))) =
      Complex.exp (-(((m - 1 : ℤ) : ℂ) * φ * Complex.I)) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]; congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  rw [← e1, ← e2]
  ring

lemma fderiv_herglotzCoeff_apply z w :
    fderiv ℝ (herglotzCoeff k a m) z w =
      -(Complex.I * k / 2) * (w * herglotzCoeff k a (m + 1) z +
        conj w * herglotzCoeff k a (m - 1) z) := by
  obtain ⟨L, hL, hLw⟩ := hasFDerivAt_herglotzCoeff ha k m z
  rw [hL.fderiv, hLw]

lemma differentiable_herglotzCoeff : Differentiable ℝ (herglotzCoeff k a m) := fun z => by
  obtain ⟨L, hL, -⟩ := hasFDerivAt_herglotzCoeff ha k m z
  exact hL.differentiableAt

lemma norm_fderiv_herglotzCoeff_le z :
    ‖fderiv ℝ (herglotzCoeff k a m) z‖ ≤ |k| * (circlePeriod⁻¹ * ∫ φ in (0 : ℝ)..circlePeriod, ‖a φ‖) := by
  set A := circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod, ‖a φ‖
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ∫ φ in (0 : ℝ)..circlePeriod, ‖a φ‖ :=
      intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [fderiv_herglotzCoeff_apply ha, norm_mul]
  have hc : ‖-(Complex.I * k / 2)‖ = |k| / 2 := by
    simp_all
  rw [hc]
  have h1 := norm_herglotzCoeff_le (a := a) k (m + 1) z
  have h2 := norm_herglotzCoeff_le (a := a) k (m - 1) z
  calc |k| / 2 * ‖w * herglotzCoeff k a (m + 1) z + conj w * herglotzCoeff k a (m - 1) z‖
      ≤ |k| / 2 * (‖w‖ * A + ‖w‖ * A) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        gcongr
    _ = |k| * A * ‖w‖ := by ring

lemma lipschitzWith_herglotzCoeff : ∃ C, LipschitzWith C (herglotzCoeff k a m) := by
  set A := circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod, ‖a φ‖
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ∫ φ in (0 : ℝ)..circlePeriod, ‖a φ‖ :=
      intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
    positivity
  refine ⟨⟨|k| * A, by positivity⟩, lipschitzWith_of_nnnorm_fderiv_le
    (differentiable_herglotzCoeff ha k m) fun z => ?_⟩
  solve_by_elim (maxDepth := 5) [norm_fderiv_herglotzCoeff_le]

lemma continuous_herglotzCoeff : Continuous (herglotzCoeff k a m) :=
  (differentiable_herglotzCoeff ha k m).continuous

end


/-- The conormal trace in terms of the Herglotz coefficients:
`g_a = (k/2) (conj(γ') F_{-1}(γ) - γ' F_1(γ))`. -/
lemma herglotzConormal_eq γ θ :
    herglotzConormal k a γ θ = (k / 2 : ℂ) * (conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ) -
      deriv γ θ * herglotzCoeff k a 1 (γ θ)) := by
  have hw  := funext (herglotzWave_eq k a)
  rw [herglotzConormal, hw, fderiv_herglotzCoeff_apply ha]
  simp  
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Along a Lipschitz curve, `F_m ∘ γ` is the primitive of
`-(ik/2) (γ' F_{m+1}(γ) + conj(γ') F_{m-1}(γ))`. -/
lemma herglotzCoeff_comp_eq m   (hK : LipschitzWith K γ) θ :
    herglotzCoeff k a m (γ θ) = herglotzCoeff k a m (γ 0) + ∫ s in (0 : ℝ)..θ,
      -(Complex.I * k / 2) * (deriv γ s * herglotzCoeff k a (m + 1) (γ s) +
        conj (deriv γ s) * herglotzCoeff k a (m - 1) (γ s)) := by
  obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k m
  have hcomp := hC.comp hK
  have hftc := integral_deriv_of_lipschitz hcomp 0 θ
  have key : (∫ s in (0 : ℝ)..θ, -(Complex.I * k / 2) * (deriv γ s * herglotzCoeff k a (m + 1) (γ s) +
        conj (deriv γ s) * herglotzCoeff k a (m - 1) (γ s))) =
      ∫ x in (0 : ℝ)..θ, deriv (herglotzCoeff k a m ∘ γ) x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hK.ae_differentiableAt] with s hs _
    obtain ⟨L, hL, hLw⟩ := hasFDerivAt_herglotzCoeff ha k m (γ s)
    rw [(hL.comp_hasDerivAt s hs.hasDerivAt).deriv, hLw]
  simp_all

/-! ### Lemma 4.4 -/

/-- The conormal trace is measurable and bounded. -/
lemma herglotzConormal_bounded   (hK : LipschitzWith K γ) :
    AEStronglyMeasurable (herglotzConormal k a γ) volume ∧
      ∃ B, ∀ s, ‖herglotzConormal k a γ s‖ ≤ B := by
  have hf  :=
    funext (herglotzConormal_eq ha k γ)
  set A := circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod, ‖a φ‖
  have hd : AEStronglyMeasurable (deriv γ) volume := (measurable_deriv γ).aestronglyMeasurable
  have hc1 := ((continuous_herglotzCoeff ha k (-1)).comp hK.continuous).aestronglyMeasurable
    (μ := volume)
  have hc2 := ((continuous_herglotzCoeff ha k 1).comp hK.continuous).aestronglyMeasurable
    (μ := volume)
  refine ⟨?_, |k| / 2 * (K * A + K * A), fun s => ?_⟩
  · measurability
  · rw [hf, norm_mul]
    have hk : ‖(k / 2 : ℂ)‖ = |k| / 2 := by
      simp_all
    rw [hk]
    have hγ' := norm_deriv_le_of_lipschitzWith hK s
    have h1 := norm_herglotzCoeff_le (a := a) k (-1) (γ s)
    have h2 := norm_herglotzCoeff_le (a := a) k 1 (γ s)
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
    gcongr

end


/-- **Lemma 4.4 (driven equation of the Herglotz data).** For a Lipschitz curve `γ`, `E ≥ 0`
and an `L²` direction density `a`, the Herglotz vector `y_a = y_a(γ(·))` (with `k = √E`)
satisfies `y_a(θ) = y_a(0) + ∫₀^θ (C_E y_a - (i/√2) g_a e₀)` for all `θ`. -/
theorem herglotz_driven {a : ComplexCurve} (ha : IsDirDensity a) {γ : ComplexCurve} {K : NNReal}
    (hK : LipschitzWith K γ) (E : ℝ) (θ : ℝ) :
    herglotzVec ha (Real.sqrt E) (γ θ) = herglotzVec ha (Real.sqrt E) (γ 0) +
      ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (herglotzVec ha (Real.sqrt E) (γ s)) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) * herglotzConormal (Real.sqrt E) a γ s) •
          basisVec 0) := by
  have hai := ha.intervalIntegrable
  set c : ℂ := -(Complex.I / (Real.sqrt 2)) with hc
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded hai (Real.sqrt E) hK
  have hyc : Continuous fun s => herglotzVec ha (Real.sqrt E) (γ s) :=
    (continuous_herglotzVec ha _).comp hK.continuous
  set G : ℝ → Ell2 := fun s => transportCoeff γ E s (herglotzVec ha (Real.sqrt E) (γ s)) +
    (c * herglotzConormal (Real.sqrt E) a γ s) • basisVec 0 with hG
  have hGint : IntervalIntegrable G volume 0 θ := by
    obtain ⟨M, hM⟩ : ∃ M, ∀ s, ‖transportCoeff γ E s‖ ≤ M := ⟨_, transportCoeff_norm_le γ E hK⟩
    have hC := transportCoeff_aestronglyMeasurable γ E
    have happ : Continuous fun p : (ComplexEnd Ell2) × Ell2 => p.1 p.2 := by fun_prop
    have hm : AEStronglyMeasurable G volume :=
      (happ.comp_aestronglyMeasurable (hC.prodMk hyc.aestronglyMeasurable)).add
        ((hgm.const_mul c).smul_const _)
    have hbc : Continuous fun s => M * ‖herglotzVec ha (Real.sqrt E) (γ s)‖ +
        ‖c‖ * B * ‖basisVec 0‖ := by fun_prop
    refine IntervalIntegrable.mono_fun' (hbc.intervalIntegrable 0 θ)
      hm.restrict (Eventually.of_forall fun s => ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ((transportCoeff γ E s).le_opNorm _).trans (by gcongr; exact hM s)
    · rw [norm_smul, norm_mul]
      simp_all [PolyaNeumann.Ell2, PolyaNeumann.basisVec]
  have hcoordInt  := fun n => by
    have := (innerSL ℂ (basisVec n)).intervalIntegral_comp_comm hGint
    simp only [innerSL_apply_apply, basisVec, inner_single] at this
    exact this.symm
  have hr2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hrinv : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) / 2 :=
    inv_eq_of_mul_eq_one_right (by rw [mul_div_assoc', hr2]; norm_num)
  have hsw : ∀ j z, shiftWeight j * herglotzSeq (Real.sqrt E) a z j =
      herglotzCoeff (Real.sqrt E) a j z := fun j z => by
    unfold shiftWeight herglotzSeq
    split_ifs with h
    · subst h; field_simp <;> ring
    · rw [one_mul]
  have hGn : ∀ s n, (G s : ComplexSeq) n = (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
      (deriv γ s * (shiftWeight n * herglotzSeq (Real.sqrt E) a (γ s) (n + 1)) +
        conj (deriv γ s) * (shiftN (herglotzVec ha (Real.sqrt E) (γ s)) : ComplexSeq) n) +
      c * herglotzConormal (Real.sqrt E) a γ s * (if n = 0 then 1 else 0) := fun s n => by
    simp only [hG, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      transportCoeff_apply_coord, herglotzVec_apply, basisVec, lp.single_apply]
    rw [Pi.single_apply]
  have hs0 : ∀ z, herglotzSeq (Real.sqrt E) a z 0 = herglotzCoeff (Real.sqrt E) a 0 z /
      (Real.sqrt 2 : ℂ) := fun z => if_pos rfl
  have hs1 : ∀ j z, herglotzSeq (Real.sqrt E) a z (j + 1) =
      herglotzCoeff (Real.sqrt E) a ((j + 1 : ℕ) : ℤ) z := fun j z => if_neg (Nat.succ_ne_zero j)
  refine lp.ext (funext fun n => ?_)
  rw [lp.coeFn_add, Pi.add_apply, hcoordInt n]
  simp only [hGn, herglotzVec_apply]
  rcases n with _ | j
  · simp only [shiftN_apply_zero, mul_zero, add_zero, hs0, hs1]
    rw [herglotzCoeff_comp_eq hai _ 0 hK θ, add_div, ← intervalIntegral.integral_div]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hc, herglotzConormal_eq hai, shiftWeight, zero_add, zero_sub,
      Nat.cast_one, if_true, mul_one]
    rw [div_eq_mul_inv, div_eq_mul_inv _ (Real.sqrt 2 : ℂ), hrinv]
    ring_nf
  · have e1 : ((j + 1 : ℕ) : ℤ) + 1 = ((j + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by push_cast; ring
    simp only [hs1, shiftN_apply_succ, herglotzVec_apply, hsw, Nat.succ_ne_zero, if_false, mul_zero, add_zero]
    rw [herglotzCoeff_comp_eq hai _ ((j + 1 : ℕ)) hK θ, e1, e2]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [shiftWeight, Nat.succ_ne_zero, if_false, one_mul]
    push_cast
    ring

/-! ### Every vector is Herglotz data (Lemma 4.4, last clause) -/

lemma planeWave_zero k φ : planeWave k 0 φ = 1 := by
  simp [planeWave]

/-- At the origin the Herglotz coefficients are the Fourier coefficients of the density on the
circle of length `2π`. -/
lemma herglotzCoeff_zero_eq_fourierCoeff [Fact (0 < 2 * π)] (f : AddCircle circlePeriod → ℂ) k
    m : herglotzCoeff k (fun φ => f φ) m 0 = fourierCoeff f m := by
  rw [fourierCoeff_eq_intervalIntegral f m 0, zero_add, herglotzCoeff, Complex.real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [planeWave_zero, smul_eq_mul]
    rw [fourier_coe_apply]
    push_cast
    field_simp

/-- **Lemma 4.4 (every vector is Herglotz data).** For every `v ∈ ℓ²(ℕ₀)` there is an `L²`
direction density `a` with `y_a(0) = v` (the value at the boundary origin `γ(0) = 0`). -/
theorem exists_herglotzVec_zero_eq k v :
    ∃ (a : ComplexCurve) (ha : IsDirDensity a), herglotzVec ha k 0 = v := by
  haveI : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  set r : ℂ := (Real.sqrt 2 : ℂ)
  have hr2 : r * r = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hr0 : r ≠ 0 := by measurability
  set c : FourierSeq := fun m => if m = 0 then r * v 0 else
    if 0 < m then v m.toNat else 0 with hc
  have hnr : ‖r‖ ^ 2 = 2 := by
    aesop
  have hbound : ∀ n : ℕ, ‖c n‖ ^ 2 ≤ 2 * ‖(v : ComplexSeq) n‖ ^ 2 ∧
      ‖c (-(n : ℤ))‖ ^ 2 ≤ 2 * ‖(v : ComplexSeq) n‖ ^ 2 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc, mul_pow, hnr]
    · have h1 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      have h2 : (0 : ℤ) < n := by exact_mod_cast hn
      have h3 : -(n : ℤ) ≠ 0 := by omega
      have h4 : ¬ (0 : ℤ) < -(n : ℤ) := by omega
      simp only [hc, h1, h2, h3, h4, if_false, if_true, Int.toNat_natCast]
      constructor
      · nlinarith
      simp_all
  have hsv := summable_sq v
  have hcs : Summable fun m => ‖c m‖ ^ 2 :=
    Summable.of_nat_of_neg
      ((hsv.mul_left 2).of_nonneg_of_le (fun _ => by positivity) fun n => (hbound n).1)
      ((hsv.mul_left 2).of_nonneg_of_le (fun _ => by positivity) fun n => (hbound n).2)
  have hcm : Memℓp c 2 := by
    rw [memℓp_gen_iff (by simp)]
    simpa [two_toReal] using hcs
  set f : Lp ℂ 2 (@AddCircle.haarAddCircle circlePeriod _) :=
    fourierBasis.repr.symm ⟨c, hcm⟩ with hf
  have hfc : ∀ m, fourierCoeff f m = c m := fun m => by
    rw [← fourierBasis_repr, hf, LinearIsometryEquiv.apply_symm_apply]
  have hfm  :=
    memLp_haarAddCircle_iff.mp (Lp.memLp f)
  have ha : IsDirDensity fun φ : ℝ => (f : AddCircle circlePeriod → ℂ) φ := by
    have := hfm.comp_measurePreserving (AddCircle.measurePreserving_mk circlePeriod 0)
    rw [zero_add] at this
    exact this
  refine ⟨_, ha, lp.ext (funext fun n => ?_)⟩
  rw [herglotzVec_apply]
  unfold herglotzSeq
  split_ifs with hn
  · subst hn
    rw [herglotzCoeff_zero_eq_fourierCoeff, hfc]
    simp only [hc, if_true]
    field_simp
    simp only [r]
    ring
  · rw [herglotzCoeff_zero_eq_fourierCoeff, hfc]
    have h1 : (n : ℤ) ≠ 0 := by exact_mod_cast hn
    have h2 : (0 : ℤ) < n := by omega
    simp only [hc, h1, h2, if_false, if_true, Int.toNat_natCast]

/-- **Lemma 10.5 (pairing step).** If `v` is a fixed vector of `V_E = W_E(L)` for a closed
Lipschitz curve, then its observation `O_E v` is orthogonal in `L²(0, L)` to the conormal trace
`g_a` of every Herglotz wave: `∫₀^L conj(g_a) (O_E v) = 0`. -/
theorem integral_conj_herglotzConormal_mul_observation  
    (hK : LipschitzWith K γ) (hclosed : γ circlePeriod = γ 0)  
    (hW : IsTransport γ E W)  (hv : W circlePeriod v = v) 
    (ha : IsDirDensity a) :
    ∫ s in (0 : ℝ)..circlePeriod, conj (herglotzConormal (Real.sqrt E) a γ s) * observation W v s =
      0 := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hy : ContinuousOn (fun s => herglotzVec ha (Real.sqrt E) (γ s)) boundaryInterval :=
    ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
  have hper : herglotzVec ha (Real.sqrt E) (γ circlePeriod) = herglotzVec ha (Real.sqrt E) (γ 0) := by
    rw [hclosed]
  obtain ⟨-, hadj⟩ := driven_endpoint hK hW hgm hgB hy (fun θ _ => herglotz_driven ha hK E θ) hper
  rw [← inner_observationAdj hW.1 hgm hgB v, hadj, inner_smul_left, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hv,
    sub_self, mul_zero]

end PolyaNeumann
