module
import Mathlib
/- Isolated from Scott McColm, smccolm/Lean pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1. MIT-0. See notes/guth-maynard-affine-reuse-audit.md. -/
public import GuthMaynard.AffineSource.LargeValuesAffine

@[expose] public section

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Section 9: smoothing iteration

This module carries the exact smoothing identities from Lemma 9.2 through
the finite natural-number iteration replacing the paper's informal
downward induction in the exponent.
-/

section
variable (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
include T hT f

/- The normalized Section 9 smoother preserves mass up to the fixed
cutoff mass.  This is the exact real-valued convolution identity used in
the `L¹` part of the iteration. -/
theorem integral_gmAffineTildeSchwartz_eq_mul
     :
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u) =
      (∫ x : ℝ, T * gmCubicLocalBump (T * x)) *
        ∫ u : ℝ, f u := by
  let k : ℝ → ℝ := fun x => T * gmCubicLocalBump (T * x)
  have hk : Integrable k := by
    have hcomplex : Integrable (fun x : ℝ => gmAffineSmoothingKernel T hT x) :=
      (gmAffineSmoothingKernel T hT).integrable
    have hreal : Integrable (fun x : ℝ =>
        Complex.re (gmAffineSmoothingKernel T hT x)) :=
      Complex.reCLM.integrable_comp hcomplex
    apply hreal.congr
    filter_upwards with x
    dsimp only [k]
    simp
  have hprod : Integrable (fun p : ℝ × ℝ =>
      (ContinuousLinearMap.mul ℝ ℝ) (k p.2) (f (p.1 - p.2))) :=
    hk.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) f.integrable
  simp_rw [gmAffineTildeSchwartz_apply T hT f]
  change (∫ u : ℝ, ∫ t : ℝ, k t * f (u - t)) =
    (∫ x : ℝ, k x) * ∫ u : ℝ, f u
  calc
    (∫ u : ℝ, ∫ t : ℝ, k t * f (u - t)) =
        ∫ t : ℝ, ∫ u : ℝ, k t * f (u - t) :=
      integral_integral_swap hprod
    _ = ∫ t : ℝ, k t * ∫ u : ℝ, f (u - t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_const_mul]
    _ = ∫ t : ℝ, k t * ∫ u : ℝ, f u := by
      simp_rw [integral_sub_right_eq_self]
    _ = (∫ x : ℝ, k x) * ∫ u : ℝ, f u := by
      rw [integral_mul_const]

/- The source `L¹` estimate for the smoothed function, with the explicit
the constant supplied by the fixed compact cutoff. -/
theorem integral_gmAffineTildeSchwartz_le
    
    (hf : ∀ u, 0 ≤ f u) :
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u) ≤
      4 * ∫ u : ℝ, f u := by
  rw [integral_gmAffineTildeSchwartz_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (integral_gmAffineSmoothingKernelReal_le_four T hT)
    (integral_nonneg hf)
end


/- The fixed cutoff equals one on `[-1,1]`, so its mass is at least two. -/
theorem two_le_integral_gmCubicLocalBump :
    (2 : ℝ) ≤ ∫ tau : ℝ, gmCubicLocalBump tau := by
  have hb : Integrable gmCubicLocalBump := by
    have hc : Integrable (fun tau : ℝ => (gmCubicLocalBump tau : ℂ)) := by
      exact gmAffineLocalBumpSchwartz.integrable
    exact Complex.reCLM.integrable_comp hc
  calc
    (2 : ℝ) = ∫ tau in Set.Icc (-1 : ℝ) 1, (1 : ℝ) := by norm_num
    _ = ∫ tau in Set.Icc (-1 : ℝ) 1, gmCubicLocalBump tau := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro tau htau
      symm
      apply gmCubicLocalBump_one
      rw [abs_le]
      exact htau
    _ ≤ ∫ tau : ℝ, gmCubicLocalBump tau :=
      setIntegral_le_integral hb
        (Eventually.of_forall gmCubicLocalBump_nonneg)

/- Smoothing cannot collapse the positive mass: every step multiplies it
by at least two. -/
theorem two_mul_integral_le_integral_gmAffineTildeSchwartz
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ u, 0 ≤ f u) :
    2 * (∫ u : ℝ, f u) ≤
      ∫ u : ℝ, gmAffineTildeSchwartz T hT f u := by
  rw [integral_gmAffineTildeSchwartz_eq_mul,
    integral_gmAffineSmoothingKernelReal_eq T hT]
  exact mul_le_mul_of_nonneg_right two_le_integral_gmCubicLocalBump
    (integral_nonneg hf)

/- Exact Fourier multiplier identity for the Section 9 smoother. -/
theorem fourier_gmAffineComplexify_tilde
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) :
    fourier (gmAffineComplexify (gmAffineTildeSchwartz T hT f)) =
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        (fourier (gmAffineSmoothingKernel T hT))
        (fourier (gmAffineComplexify f)) := by
  rw [gmAffineComplexify_tilde_eq_convolution,
    SchwartzMap.fourier_convolution]

/- Uniform Fourier-multiplier bound for the normalized smoothing kernel. -/
theorem norm_fourier_gmAffineSmoothingKernel_le_four
    (T : ℝ) (hT : 0 < T) (xi : ℝ) :
    ‖fourier (gmAffineSmoothingKernel T hT) xi‖ ≤ 4 := by
  calc
    ‖fourier (gmAffineSmoothingKernel T hT) xi‖ ≤
        ∫ x : ℝ, ‖gmAffineSmoothingKernel T hT x‖ := by
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 volume (innerₗ ℝ) (gmAffineSmoothingKernel T hT) xi
    _ = ∫ x : ℝ, T * gmCubicLocalBump (T * x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [gmAffineSmoothingKernel_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hT.le (gmCubicLocalBump_nonneg (T * x)))]
    _ ≤ 4 := integral_gmAffineSmoothingKernelReal_le_four T hT

/- A single Section 9 smoothing increases every weighted zeroth-derivative
Fourier seminorm by at most the fixed kernel mass bound `4`.  Crucially, the
the constant is independent of the smoothing scale. -/
theorem seminorm_fourier_gmAffineComplexify_tilde_le_four
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) (n : ℕ) :
    SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify (gmAffineTildeSchwartz T hT f))) ≤
      4 * SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify f)) := by
  apply SchwartzMap.seminorm_le_bound' ℝ n 0 _ (by positivity)
  intro xi
  have hmul :
      ‖fourier (gmAffineComplexify (gmAffineTildeSchwartz T hT f)) xi‖ ≤
        4 * ‖fourier (gmAffineComplexify f) xi‖ := by
    rw [fourier_gmAffineComplexify_tilde T hT f,
      SchwartzMap.pairing_apply_apply]
    change ‖fourier (gmAffineSmoothingKernel T hT) xi *
        fourier (gmAffineComplexify f) xi‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_fourier_gmAffineSmoothingKernel_le_four T hT xi) (norm_nonneg _)
  have hseminorm :=
    SchwartzMap.le_seminorm' ℝ n 0 (fourier (gmAffineComplexify f)) xi
  simp only [iteratedDeriv_zero] at hseminorm ⊢
  calc
    |xi| ^ n *
          ‖fourier (gmAffineComplexify (gmAffineTildeSchwartz T hT f)) xi‖ ≤
        |xi| ^ n * (4 * ‖fourier (gmAffineComplexify f) xi‖) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = 4 * (|xi| ^ n * ‖fourier (gmAffineComplexify f) xi‖) := by ring
    _ ≤ 4 * SchwartzMap.seminorm ℝ n 0
          (fourier (gmAffineComplexify f)) :=
      mul_le_mul_of_nonneg_left hseminorm (by norm_num)

/- The exact `L²` stability estimate for `f_tilde`; the fixed constant
is immaterial to the `T^δ` iteration but is kept explicit. -/
theorem integral_gmAffineTildeSchwartz_sq_le
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) :
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u ^ 2) ≤
      16 * ∫ u : ℝ, f u ^ 2 := by
  let ft := gmAffineComplexify (gmAffineTildeSchwartz T hT f)
  let ff := gmAffineComplexify f
  have hffInt : Integrable (fun xi : ℝ => ‖fourier ff xi‖ ^ 2) := by
    let g := fourier ff
    have hg : Integrable (fun xi : ℝ => ‖g xi‖ ^ (2 : ℝ)) := by
      simpa using (g.memLp (2 : ENNReal)).integrable_norm_rpow
        (by norm_num : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
    simpa only [g, Real.rpow_two] using hg
  have hftInt : Integrable (fun xi : ℝ => ‖fourier ft xi‖ ^ 2) := by
    let g := fourier ft
    have hg : Integrable (fun xi : ℝ => ‖g xi‖ ^ (2 : ℝ)) := by
      simpa using (g.memLp (2 : ENNReal)).integrable_norm_rpow
        (by norm_num : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
    simpa only [g, Real.rpow_two] using hg
  have hpoint : ∀ xi : ℝ,
      ‖fourier ft xi‖ ^ 2 ≤ 16 * ‖fourier ff xi‖ ^ 2 := by
    intro xi
    have hmul : ‖fourier ft xi‖ ≤ 4 * ‖fourier ff xi‖ := by
      dsimp only [ft, ff]
      rw [fourier_gmAffineComplexify_tilde T hT f,
        SchwartzMap.pairing_apply_apply]
      change ‖fourier (gmAffineSmoothingKernel T hT) xi *
          fourier (gmAffineComplexify f) xi‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_fourier_gmAffineSmoothingKernel_le_four T hT xi) (norm_nonneg _)
    calc
      ‖fourier ft xi‖ ^ 2 ≤ (4 * ‖fourier ff xi‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mpr hmul
      _ = 16 * ‖fourier ff xi‖ ^ 2 := by ring
  calc
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u ^ 2) =
        ∫ u : ℝ, ‖ft u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with u
      simp [ft]
    _ = ∫ xi : ℝ, ‖fourier ft xi‖ ^ 2 :=
      (SchwartzMap.integral_norm_sq_fourier ft).symm
    _ ≤ ∫ xi : ℝ, 16 * ‖fourier ff xi‖ ^ 2 := by
      exact integral_mono hftInt (hffInt.const_mul 16)
        hpoint
    _ = 16 * ∫ xi : ℝ, ‖fourier ff xi‖ ^ 2 := by
      rw [integral_const_mul]
    _ = 16 * ∫ u : ℝ, ‖ff u‖ ^ 2 := by
      rw [SchwartzMap.integral_norm_sq_fourier]
    _ = 16 * ∫ u : ℝ, f u ^ 2 := by
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      simp [ff]

/- The two weighted norms appearing in Proposition 9.1 grow by at most
the common factor `16` under one smoothing and passage to a smaller affine
scale. -/
theorem gmAffineTildeSchwartz_weighted_norms_le_sixteen
    {S : ℝ} (hS : 0 < S) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) {M₂ M : ℕ} (hM₂M : M₂ ≤ M) :
    (M₂ : ℝ) ^ 6 *
          (∫ x : ℝ, gmAffineTildeSchwartz S hS f x) ^ 2 +
        (M₂ : ℝ) ^ 4 *
          (∫ x : ℝ, gmAffineTildeSchwartz S hS f x ^ 2) ≤
      16 * ((M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
        (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by
  have hmass := integral_gmAffineTildeSchwartz_le S hS f hf
  have hmassNonneg : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  have htildeNonneg : ∀ x, 0 ≤ gmAffineTildeSchwartz S hS f x :=
    gmAffineTildeSchwartz_nonneg S hS f hf
  have htildeMassNonneg :
      0 ≤ ∫ x : ℝ, gmAffineTildeSchwartz S hS f x :=
    integral_nonneg htildeNonneg
  have hmassSq :
      (∫ x : ℝ, gmAffineTildeSchwartz S hS f x) ^ 2 ≤
        16 * (∫ x : ℝ, f x) ^ 2 := by
    calc
      _ ≤ (4 * ∫ x : ℝ, f x) ^ 2 :=
        (sq_le_sq₀ htildeMassNonneg
          (mul_nonneg (by norm_num) hmassNonneg)).2 hmass
      _ = _ := by ring
  have hL2 := integral_gmAffineTildeSchwartz_sq_le S hS f
  have hM₂real : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
  have hM6 : (M₂ : ℝ) ^ 6 ≤ (M : ℝ) ^ 6 := by gcongr
  have hM4 : (M₂ : ℝ) ^ 4 ≤ (M : ℝ) ^ 4 := by gcongr
  have htildeL2 :
      0 ≤ ∫ x : ℝ, gmAffineTildeSchwartz S hS f x ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  calc
    _ ≤ (M : ℝ) ^ 6 * (16 * (∫ x : ℝ, f x) ^ 2) +
        (M : ℝ) ^ 4 * (16 * ∫ x : ℝ, f x ^ 2) := by
      exact add_le_add
        (mul_le_mul hM6 hmassSq (sq_nonneg _) (by positivity))
        (mul_le_mul hM4 hL2 htildeL2 (by positivity))
    _ = _ := by ring

theorem sqrt_mul_sqrt_add_le_add
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt B * Real.sqrt (A + B) ≤ A + B := by
  have hsqrt : Real.sqrt B ≤ Real.sqrt (A + B) :=
    Real.sqrt_le_sqrt (by linarith)
  calc
    Real.sqrt B * Real.sqrt (A + B) ≤
        Real.sqrt (A + B) * Real.sqrt (A + B) :=
      mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = A + B := by
      rw [← sq]
      exact Real.sq_sqrt (add_nonneg hA hB)

/- Square-root normalization used in the Lemma 9.2 descent. -/
theorem sqrt_le_four_mul_sqrt_rpow_mul_sqrt
    {J C T delta W : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hbound : J ≤ 16 * C * T ^ (3 * delta / 2) * W) :
    Real.sqrt J ≤
      4 * Real.sqrt C * T ^ (3 * delta / 4) * Real.sqrt W := by
  calc
    Real.sqrt J ≤ Real.sqrt (16 * C * T ^ (3 * delta / 2) * W) :=
      Real.sqrt_le_sqrt hbound
    _ = Real.sqrt 16 * Real.sqrt C *
          Real.sqrt (T ^ (3 * delta / 2)) * Real.sqrt W := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16 * C * T ^
        (3 * delta / 2)), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16 * C),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    _ = 4 * Real.sqrt C * T ^ (3 * delta / 4) * Real.sqrt W := by
      have hpow : Real.sqrt (T ^ (3 * delta / 2)) =
          T ^ (3 * delta / 4) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
        congr 1
        ring
      rw [show Real.sqrt 16 = 4 by norm_num, hpow]

/- The mixed factor in Lemma 9.2 is bounded by the full Proposition 9.1
weight. -/
theorem gmAffine_mixed_weight_le
    (f : SchwartzMap ℝ ℝ) (M : ℕ) :
    (M : ℝ) ^ 2 * Real.sqrt (∫ x : ℝ, f x ^ 2) *
        Real.sqrt ((M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
          (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) ≤
      (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
        (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2 := by
  let A : ℝ := (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2
  let B : ℝ := (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsqrtB : Real.sqrt B = (M : ℝ) ^ 2 *
      Real.sqrt (∫ x : ℝ, f x ^ 2) := by
    dsimp only [B]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (M : ℝ) ^ 4)]
    congr 1
    rw [show (M : ℝ) ^ 4 = ((M : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  change (M : ℝ) ^ 2 * Real.sqrt (∫ x : ℝ, f x ^ 2) *
      Real.sqrt (A + B) ≤ A + B
  rw [← hsqrtB]
  exact sqrt_mul_sqrt_add_le_add hA hB

/- The symmetric width-`1/T` interval used in the retained part of the
second Poisson sum. -/
def gmAffineUnitInterval (T x : ℝ) : Set ℝ :=
  Set.Icc (x - 1 / T) (x + 1 / T)

/- The source smoother written in the `u'` variable used after the
second Poisson summation. -/
theorem gmAffineTildeSchwartz_apply_sub
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    gmAffineTildeSchwartz T hT f x =
      ∫ u' : ℝ, T * gmCubicLocalBump (T * (x - u')) * f u' := by
  rw [gmAffineTildeSchwartz_apply]
  let q : ℝ → ℝ := fun t => T * gmCubicLocalBump (T * t) * f (x - t)
  simpa only [q, sub_sub_cancel] using
    (integral_sub_left_eq_self q volume x).symm

/- A retained width-`1/T` neighborhood is majorized by the actual
normalized smoother, with no informal "almost constant" step. -/
theorem setIntegral_gmAffineUnitInterval_le_tilde
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ u, 0 ≤ f u) (x : ℝ) :
    (∫ u' in gmAffineUnitInterval T x, T * f u') ≤
      gmAffineTildeSchwartz T hT f x := by
  let G : ℝ → ℝ := fun u' =>
    T * gmCubicLocalBump (T * (x - u')) * f u'
  have hGint : Integrable G := by
    apply (f.integrable.norm.const_mul T).mono'
    · have hbcont : Continuous gmCubicLocalBump := by
        exact dfiUnitRedundantBump.continuous.comp (continuous_id.div_const 2)
      exact ((continuous_const.mul
        (hbcont.comp (continuous_const.mul
          (continuous_const.sub continuous_id)))).mul f.continuous).aestronglyMeasurable
    · filter_upwards with u'
      dsimp only [G]
      simp only [Real.norm_eq_abs]
      have hb := gmCubicLocalBump_le_one (T * (x - u'))
      calc
        |T * gmCubicLocalBump (T * (x - u')) * f u'| =
            T * gmCubicLocalBump (T * (x - u')) * |f u'| := by
          rw [abs_mul, abs_mul, abs_of_pos hT,
            abs_of_nonneg (gmCubicLocalBump_nonneg _)]
        _ ≤ T * 1 * |f u'| := by gcongr
        _ = T * |f u'| := by ring
  calc
    (∫ u' in gmAffineUnitInterval T x, T * f u') =
        ∫ u' in gmAffineUnitInterval T x, G u' := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u' hu'
      have hwidth : |T * (x - u')| ≤ 1 := by
        have hdiff : |x - u'| ≤ 1 / T := by
          rw [abs_le]
          constructor <;> linarith [hu'.1, hu'.2]
        calc
          |T * (x - u')| = T * |x - u'| := by rw [abs_mul, abs_of_pos hT]
          _ ≤ T * (1 / T) := mul_le_mul_of_nonneg_left hdiff hT.le
          _ = 1 := by field_simp [hT.ne']
      dsimp only [G]
      rw [gmCubicLocalBump_one hwidth]
      ring
    _ ≤ ∫ u' : ℝ, G u' :=
      setIntegral_le_integral hGint
        (Eventually.of_forall fun u' => by
          dsimp only [G]
          exact mul_nonneg
            (mul_nonneg hT.le (gmCubicLocalBump_nonneg _)) (hf u'))
    _ = gmAffineTildeSchwartz T hT f x := by
      rw [gmAffineTildeSchwartz_apply_sub]

/-! ### The exact finite `J(tilde f)` entry in equation (9.8) -/

/- The fixed source support used in Section 9.  Guth--Maynard may choose
the bump around `u = 1` this narrowly before starting the iteration. -/
def GMAffineSourceSupported (f : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, u ∉ Set.Icc (1 / 2 : ℝ) 2 → f u = 0

/- A fixed compact support envelope stable enough for the finite Section 9
iteration.  The source support `[1/2,2]` lies strictly inside `[0,3]`; the
finite collection of normalized smoothings remains in this larger interval
once the common height threshold is chosen. -/
def GMAffineIterationSupported (f : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 3 → f u = 0

/- Quantitative compact-support predicate used to track the finite
sequence of Section 9 smoothings.  Unlike a bare `HasCompactSupport`, it
retains the two endpoints needed to prove that every recursive input stays
inside the fixed central-shift envelope `[0,3]`. -/
def GMAffineSupportedOn (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, u ∉ Set.Icc a b → f u = 0

theorem GMAffineSupportedOn.mono
    {a b c d : ℝ} {f : ℝ → ℝ} (hf : GMAffineSupportedOn a b f)
    (hca : c ≤ a) (hbd : b ≤ d) : GMAffineSupportedOn c d f := by
  intro u hu
  apply hf u
  intro hab
  exact hu ⟨hca.trans hab.1, hab.2.trans hbd⟩

/- Intrinsic Fourier-to-mass ratio used to keep all normalized tail
constants uniform during the finite descent. -/
def GMAffineFourierMassBound
    (n : ℕ) (D : ℝ) (f : SchwartzMap ℝ ℝ) : Prop :=
  SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) ≤
    D * ∫ x : ℝ, f x

theorem GMAffineSourceSupported.supportedOn
    {f : ℝ → ℝ} (hf : GMAffineSourceSupported f) :
    GMAffineSupportedOn (1 / 2 : ℝ) 2 f := hf

theorem GMAffineSupportedOn.iterationSupported
    {a b : ℝ} {f : ℝ → ℝ} (hf : GMAffineSupportedOn a b f)
    (ha : 0 ≤ a) (hb : b ≤ 3) : GMAffineIterationSupported f := by
  intro u hu
  apply hf u
  intro hab
  exact hu ⟨ha.trans hab.1, hab.2.trans hb⟩

theorem GMAffineSourceSupported.iterationSupported
    {f : ℝ → ℝ} (hf : GMAffineSourceSupported f) :
    GMAffineIterationSupported f := by
  intro u hu
  apply hf u
  intro husource
  exact hu ⟨(by linarith [husource.1]), (by linarith [husource.2])⟩

/- The quantitative Fourier-decay hypothesis in Guth--Maynard
Proposition 9.1.  The order-zero Schwartz seminorm is the literal
supremum norm of the complexified source in the normalization used by
Mathlib's Schwartz API.  Quantifying the constants before the frequency
variable records the uniformity required by the paper. -/
def GMAffineFourierDecayAt
    (T : ℝ) (f : SchwartzMap ℝ ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ n : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ xi : ℝ, xi ≠ 0 →
      ‖fourier (gmAffineComplexify f) xi‖ ≤
        C * T ^ epsilon * (T / |xi|) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)

/- For a nonnegative source the order-zero Fourier seminorm is bounded
by its mass.  This is the precise replacement for the paper's use of
`sup |\hat f| ≤ ∫ f` in Region I. -/
theorem seminorm_fourier_gmAffineComplexify_le_integral
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x) :
    SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) ≤
      ∫ x : ℝ, f x := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) 0 0
    (fourier (gmAffineComplexify f)) (integral_nonneg hf)
  intro xi
  simp only [pow_zero, iteratedDeriv_zero, one_mul]
  calc
    ‖fourier (gmAffineComplexify f) xi‖ ≤
        ∫ x : ℝ, ‖gmAffineComplexify f x‖ := by
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 volume (innerₗ ℝ) (gmAffineComplexify f) xi
    _ = ∫ x : ℝ, f x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [abs_of_nonneg (hf x)]

/- The retained first-Poisson envelope in the polynomial form used in
Region I.  All shell cardinalities and the reciprocal `M₁` cancel
explicitly; the only remaining analytic factors are the source mass and
the fixed cutoff seminorm. -/
theorem gmAffinePoissonMainEnvelope_le_mass
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q ≤
      672 * Q * (M₂ : ℝ) ^ 2 * M₃ *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual *
          ∫ x : ℝ, f x := by
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (1 : ℝ) ≤ M₂ := by exact_mod_cast hM₂
  have hM₃r : (1 : ℝ) ≤ M₃ := by exact_mod_cast hM₃
  have hsignedNat := card_gmAffineSignedShell_le M₁
  have hsigned : ((gmAffineSignedShell M₁).card : ℝ) ≤ 4 * M₁ := by
    exact_mod_cast (hsignedNat.trans (by omega : 2 * (M₁ + 1) ≤ 4 * M₁))
  have hpositive : ((gmAffinePositiveShell M₂).card : ℝ) ≤ 2 * M₂ := by
    have hpositiveNat : (gmAffinePositiveShell M₂).card ≤ 2 * M₂ := by
      rw [card_gmAffinePositiveShell]
      omega
    exact_mod_cast hpositiveNat
  have hfourier := seminorm_fourier_gmAffineComplexify_le_integral f hf
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  have hkernel :
      (2 * (Q / (8 * M₃ : ℝ)) + 5) * (8 * M₃ : ℝ) ≤
        42 * Q * M₃ := by
    have hM₃pos : (0 : ℝ) < M₃ := by positivity
    have hQM : (1 : ℝ) ≤ Q * M₃ := by
      nlinarith [mul_le_mul hQ hM₃r (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (0 : ℝ) ≤ Q)]
    field_simp [hM₃pos.ne']
    nlinarith
  unfold gmAffinePoissonMainEnvelope
  have hcut : 0 ≤ SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual := by
    positivity
  calc
    ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) *
        SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
        ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
          ((8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) ≤
      (4 * M₁ : ℝ) * (2 * M₂ : ℝ) *
        ((2 * M₂ : ℝ) / M₁) * (∫ x : ℝ, f x) *
          ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
            ((8 * M₃ : ℝ) *
              SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) := by
      gcongr
    _ = ((4 * M₁ : ℝ) * (2 * M₂ : ℝ) *
          ((2 * M₂ : ℝ) / M₁) * (∫ x : ℝ, f x)) *
          (((2 * (Q / (8 * M₃ : ℝ)) + 5) * (8 * M₃ : ℝ)) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) := by
      ring
    _ ≤ ((4 * M₁ : ℝ) * (2 * M₂ : ℝ) *
          ((2 * M₂ : ℝ) / M₁) * (∫ x : ℝ, f x)) *
          ((42 * Q * M₃) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hkernel hcut
      · positivity
    _ = 672 * Q * (M₂ : ℝ) ^ 2 * M₃ *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual *
            ∫ x : ℝ, f x := by
      field_simp [hM₁r.ne']
      ring

/- Fixed cutoff constant controlling the complete omitted first-Poisson
lattice. -/
noncomputable def gmAffineRegionIFarConstant (n : ℕ) : ℝ :=
  16 * (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual *
      (∑' j : ℤ, gmIntDecayProfile 2 j) +
    16 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual)

theorem gmAffineRegionIFarConstant_nonneg (n : ℕ) :
    0 ≤ gmAffineRegionIFarConstant n := by
  have hsum : 0 ≤ (∑' j : ℤ, gmIntDecayProfile 2 j) :=
    tsum_nonneg fun j => by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
  unfold gmAffineRegionIFarConstant
  positivity

/- The entire omitted first-Poisson envelope has the same polynomial
scale as the retained envelope and an explicit fixed-cutoff constant. -/
theorem gmAffinePoissonFarEnvelope_le_mass
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q ≤
      gmAffineRegionIFarConstant n * (M₂ : ℝ) ^ 2 * M₃ *
        (∫ x : ℝ, f x) := by
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₃r : (1 : ℝ) ≤ M₃ := by exact_mod_cast hM₃
  have hsignedNat := card_gmAffineSignedShell_le M₁
  have hsigned : ((gmAffineSignedShell M₁).card : ℝ) ≤ 4 * M₁ := by
    exact_mod_cast (hsignedNat.trans (by omega : 2 * (M₁ + 1) ≤ 4 * M₁))
  have hpositiveNat : (gmAffinePositiveShell M₂).card ≤ 2 * M₂ := by
    rw [card_gmAffinePositiveShell]
    omega
  have hpositive : ((gmAffinePositiveShell M₂).card : ℝ) ≤ 2 * M₂ := by
    exact_mod_cast hpositiveNat
  have hfourier := seminorm_fourier_gmAffineComplexify_le_integral f hf
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  let S : ℝ := SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual
  let Z : ℝ := ∑' j : ℤ, gmIntDecayProfile 2 j
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact tsum_nonneg fun j => by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
  have hQn : (1 : ℝ) ≤ Q ^ n := one_le_pow₀ hQ
  have hQn2 : (1 : ℝ) ≤ Q ^ (n + 2) := one_le_pow₀ hQ
  have htail :
      (4 * S / Q ^ n) * Z + 2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2)) ≤
        (M₃ : ℝ) * (4 * S * Z + 16 * S) := by
    have hfirst : 4 * S / Q ^ n ≤ 4 * S := div_le_self (by positivity) hQn
    have hsecond : (8 * M₃ : ℝ) * S / Q ^ (n + 2) ≤
        (8 * M₃ : ℝ) * S := div_le_self (by positivity) hQn2
    calc
      (4 * S / Q ^ n) * Z + 2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2)) ≤
          (4 * S) * Z + 2 * ((8 * M₃ : ℝ) * S) := by gcongr
      _ ≤ (M₃ : ℝ) * (4 * S * Z + 16 * S) := by
        nlinarith [mul_le_mul_of_nonneg_right hM₃r (mul_nonneg (mul_nonneg
          (by norm_num : (0 : ℝ) ≤ 4) hS) hZ)]
  unfold gmAffinePoissonFarEnvelope
  change ((gmAffineSignedShell M₁).card : ℝ) *
      ((gmAffinePositiveShell M₂).card : ℝ) * ((2 * M₂ : ℝ) / M₁) *
      SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
      ((4 * S / Q ^ n) * Z + 2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2))) ≤ _
  calc
    ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) * ((2 * M₂ : ℝ) / M₁) *
        SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
        ((4 * S / Q ^ n) * Z + 2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2))) ≤
      (4 * M₁ : ℝ) * (2 * M₂ : ℝ) * ((2 * M₂ : ℝ) / M₁) *
        (∫ x : ℝ, f x) * ((M₃ : ℝ) * (4 * S * Z + 16 * S)) := by
      gcongr
    _ = gmAffineRegionIFarConstant n * (M₂ : ℝ) ^ 2 * M₃ *
          (∫ x : ℝ, f x) := by
      unfold gmAffineRegionIFarConstant
      dsimp only [S, Z]
      field_simp [hM₁r.ne']
      ring

/- The sharper form of the first-Poisson omitted-lattice estimate keeps
the arbitrary negative power of the retained window `Q`.  The cruder
Region-I lemma above intentionally discarded this factor; Region II and
Region III require it for the final `T⁻¹⁰⁰` absorption. -/
theorem gmAffinePoissonFarEnvelope_le_mass_div_pow
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q ≤
      gmAffineRegionIFarConstant n * (M₂ : ℝ) ^ 2 * M₃ *
        (∫ x : ℝ, f x) / Q ^ n := by
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₃r : (1 : ℝ) ≤ M₃ := by exact_mod_cast hM₃
  have hsignedNat := card_gmAffineSignedShell_le M₁
  have hsigned : ((gmAffineSignedShell M₁).card : ℝ) ≤ 4 * M₁ := by
    exact_mod_cast (hsignedNat.trans (by omega : 2 * (M₁ + 1) ≤ 4 * M₁))
  have hpositiveNat : (gmAffinePositiveShell M₂).card ≤ 2 * M₂ := by
    rw [card_gmAffinePositiveShell]
    omega
  have hpositive : ((gmAffinePositiveShell M₂).card : ℝ) ≤ 2 * M₂ := by
    exact_mod_cast hpositiveNat
  have hfourier := seminorm_fourier_gmAffineComplexify_le_integral f hf
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  let S : ℝ := SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual
  let Z : ℝ := ∑' j : ℤ, gmIntDecayProfile 2 j
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact tsum_nonneg fun j => by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQpow : Q ^ n ≤ Q ^ (n + 2) := by
    rw [show n + 2 = n + 2 by rfl, pow_add]
    have hQtwo : (1 : ℝ) ≤ Q ^ 2 := one_le_pow₀ hQ
    nlinarith [mul_le_mul_of_nonneg_left hQtwo
      (pow_nonneg (zero_le_one.trans hQ) n)]
  have hsecond :
      (8 * M₃ : ℝ) * S / Q ^ (n + 2) ≤
        (8 * M₃ : ℝ) * S / Q ^ n :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hQpos n) hQpow
  have htail :
      (4 * S / Q ^ n) * Z + 2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2)) ≤
        ((M₃ : ℝ) * (4 * S * Z + 16 * S)) / Q ^ n := by
    calc
      (4 * S / Q ^ n) * Z +
          2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2)) ≤
        (4 * S / Q ^ n) * Z +
          2 * ((8 * M₃ : ℝ) * S / Q ^ n) := by gcongr
      _ ≤ ((M₃ : ℝ) * (4 * S * Z + 16 * S)) / Q ^ n := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_right hM₃r
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hS) hZ),
          inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hQ) n)]
  unfold gmAffinePoissonFarEnvelope
  change ((gmAffineSignedShell M₁).card : ℝ) *
      ((gmAffinePositiveShell M₂).card : ℝ) * ((2 * M₂ : ℝ) / M₁) *
      SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
      ((4 * S / Q ^ n) * Z + 2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2))) ≤ _
  calc
    ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) * ((2 * M₂ : ℝ) / M₁) *
        SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
        ((4 * S / Q ^ n) * Z + 2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2))) ≤
      (4 * M₁ : ℝ) * (2 * M₂ : ℝ) * ((2 * M₂ : ℝ) / M₁) *
        (∫ x : ℝ, f x) *
          (((M₃ : ℝ) * (4 * S * Z + 16 * S)) / Q ^ n) := by
      gcongr
    _ = gmAffineRegionIFarConstant n * (M₂ : ℝ) ^ 2 * M₃ *
          (∫ x : ℝ, f x) / Q ^ n := by
      unfold gmAffineRegionIFarConstant
      dsimp only [S, Z]
      field_simp [hM₁r.ne']
      ring

/- Fixed constant for the complete Region-I Poisson envelope. -/
noncomputable def gmAffineRegionIConstant (n : ℕ) : ℝ :=
  672 * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual +
    gmAffineRegionIFarConstant n

theorem gmAffineRegionIConstant_nonneg (n : ℕ) :
    0 ≤ gmAffineRegionIConstant n := by
  unfold gmAffineRegionIConstant
  exact add_nonneg (by positivity) (gmAffineRegionIFarConstant_nonneg n)

theorem gmAffinePoissonEnvelopes_le_mass
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
        gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q ≤
      gmAffineRegionIConstant n * Q * (M₂ : ℝ) ^ 2 * M₃ *
        (∫ x : ℝ, f x) := by
  have hmain := gmAffinePoissonMainEnvelope_le_mass
    f hf hM₁ hM₂ hM₃ hQ
  have hfar := gmAffinePoissonFarEnvelope_le_mass
    n f hf hM₁ hM₂ hM₃ hQ
  have hM₂sq : 0 ≤ (M₂ : ℝ) ^ 2 := sq_nonneg _
  have hM₃nonneg : 0 ≤ (M₃ : ℝ) := Nat.cast_nonneg _
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  calc
    gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
        gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q ≤
      672 * Q * (M₂ : ℝ) ^ 2 * M₃ *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual * (∫ x : ℝ, f x) +
        gmAffineRegionIFarConstant n * (M₂ : ℝ) ^ 2 * M₃ *
          (∫ x : ℝ, f x) := add_le_add hmain hfar
    _ ≤ 672 * Q * (M₂ : ℝ) ^ 2 * M₃ *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual * (∫ x : ℝ, f x) +
        gmAffineRegionIFarConstant n * Q * (M₂ : ℝ) ^ 2 * M₃ *
          (∫ x : ℝ, f x) := by
      have hCfar : 0 ≤ gmAffineRegionIFarConstant n :=
        gmAffineRegionIFarConstant_nonneg n
      have hCQ : gmAffineRegionIFarConstant n ≤
          gmAffineRegionIFarConstant n * Q := by
        nlinarith [mul_nonneg hCfar (sub_nonneg.mpr hQ)]
      gcongr
    _ = gmAffineRegionIConstant n * Q * (M₂ : ℝ) ^ 2 * M₃ *
          (∫ x : ℝ, f x) := by
      unfold gmAffineRegionIConstant
      ring

/- One normalized smoothing enlarges an explicitly tracked support by
exactly the radius `2/S` of the compact kernel. -/
theorem gmAffineTildeSchwartz_supportedOn
    {S a b : ℝ} (hS : 0 < S) (f : SchwartzMap ℝ ℝ)
    (hsupp : GMAffineSupportedOn a b f) :
    GMAffineSupportedOn (a - 2 / S) (b + 2 / S)
      (gmAffineTildeSchwartz S hS f) := by
  intro u hu
  rw [gmAffineTildeSchwartz_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases hbump : gmCubicLocalBump (S * t) = 0
  · simp [hbump]
  · have hSt : |S * t| < 2 := by
      exact lt_of_not_ge fun hge =>
        hbump (gmCubicLocalBump_eq_zero_of_two_le_abs hge)
    have ht : |t| < 2 / S := by
      rw [abs_mul, abs_of_pos hS] at hSt
      exact (lt_div_iff₀ hS).mpr (by simpa only [mul_comm] using hSt)
    have hut : u - t ∉ Set.Icc a b := by
      intro hut
      have htLower : -(2 / S) < t := neg_lt_of_abs_lt ht
      have htUpper : t < 2 / S := lt_of_abs_lt ht
      apply hu
      constructor <;> linarith [hut.1, hut.2]
    simp [hsupp (u - t) hut]







/- The positive-sign affine subfamily appearing after Cauchy--Schwarz in
(9.8).  Its shift range is the same finite shell as the project `J`. -/
noncomputable def gmAffinePositiveTransformSum
    (f : ℝ → ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ gmAffinePositiveShell M,
    ∑ m' ∈ gmAffinePositiveShell M,
      ∑ j ∈ gmAffineCentralShell M, gmAffineTerm f m m' j u

theorem gmAffinePositiveTransformSum_nonneg
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (M : ℕ) (u : ℝ) :
    0 ≤ gmAffinePositiveTransformSum f M u := by
  unfold gmAffinePositiveTransformSum
  apply Finset.sum_nonneg
  intro m hm
  apply Finset.sum_nonneg
  intro m' hm'
  apply Finset.sum_nonneg
  bound

/- The positive-sign family is a literal subfamily of the sharp affine
sum defining `J`, not a separately assumed surrogate. -/
theorem gmAffinePositiveTransformSum_le_transformSum
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (M : ℕ) (u : ℝ) :
    gmAffinePositiveTransformSum f M u ≤
      gmAffineTransformSum f M M M u := by
  unfold gmAffinePositiveTransformSum gmAffineTransformSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [mem_gmAffineSignedShell]
    exact Or.inr (mem_gmAffinePositiveShell.mp hm)
  · intro m hmSigned hmPositive
    apply Finset.sum_nonneg
    intro m' hm'
    apply Finset.sum_nonneg
    intro j hj
    exact hf _

theorem integrable_gmAffinePositiveTransformSum_sq
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M : ℕ} (hM : 0 < M) :
    Integrable (fun u : ℝ => gmAffinePositiveTransformSum f M u ^ 2) := by
  have hsmoothInt := integrable_gmAffineSmoothTransformSum_sq
    (M₃ := M) f hM hM
  apply hsmoothInt.mono'
  · exact ((show Continuous (gmAffinePositiveTransformSum f M) by
      unfold gmAffinePositiveTransformSum gmAffineTerm
      fun_prop).pow 2).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hpos := gmAffinePositiveTransformSum_nonneg hf M u
    have hmajor := gmAffineTransformSum_le_smooth
      (M₁ := M) (M₂ := M) hf hM u
    exact (sq_le_sq₀ hpos
      (gmAffineSmoothTransformSum_nonneg hf M M M u)).mpr
        ((gmAffinePositiveTransformSum_le_transformSum hf M u).trans hmajor)

/- Exact square-integral entry into the finite supremum `J`.  This is the
last step in Guth--Maynard (9.8) after support has restricted `j` to the
central shell. -/
theorem integral_gmAffinePositiveTransformSum_sq_le_J
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M : ℕ} (hM : 0 < M) :
    (∫ u : ℝ, gmAffinePositiveTransformSum f M u ^ 2) ≤
      gmAffineJ f M := by
  have hsmooth : ∀ u : ℝ,
      gmAffinePositiveTransformSum f M u ^ 2 ≤
        gmAffineTransformSum f M M M u ^ 2 := by
    intro u
    exact (sq_le_sq₀ (gmAffinePositiveTransformSum_nonneg hf M u)
      (gmAffineTransformSum_nonneg hf M M M u)).mpr
        (gmAffinePositiveTransformSum_le_transformSum hf M u)
  have hright : Integrable (fun u : ℝ =>
      gmAffineTransformSum f M M M u ^ 2) := by
    have hsmoothInt := integrable_gmAffineSmoothTransformSum_sq
      (M₃ := M) f hM hM
    apply hsmoothInt.mono'
    · exact ((continuous_gmAffineTransformSum f.continuous M M M).pow 2).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (gmAffineTransformSum_nonneg hf M M M u)
        (gmAffineSmoothTransformSum_nonneg hf M M M u)).mpr
          (gmAffineTransformSum_le_smooth hf hM u)
  exact (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    hright (Eventually.of_forall hsmooth)).trans
      (gmAffineTransformIntegral_le_J f hM
        (mem_gmAffineScaleTriples.mpr ⟨by omega, le_rfl, by omega, le_rfl,
          by omega, le_rfl⟩))

/- The exact Cauchy--Schwarz step (9.8), already connected to the finite
`J` defined by the source affine family. -/
theorem integral_mul_gmAffinePositiveTransformSum_le
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) {M : ℕ} (hM : 0 < M) :
    (∫ u : ℝ, f u *
        gmAffinePositiveTransformSum
          (gmAffineTildeSchwartz T hT f) M u) ≤
      Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ (gmAffineTildeSchwartz T hT f) M) := by
  let ft := gmAffineTildeSchwartz T hT f
  let A : ℝ → ℝ := fun u => gmAffinePositiveTransformSum ft M u
  have hft : ∀ u, 0 ≤ ft u := gmAffineTildeSchwartz_nonneg T hT f hf
  have hA : ∀ u, 0 ≤ A u := gmAffinePositiveTransformSum_nonneg hft M
  have hfLp : MemLp f 2 volume := by
    simpa using f.memLp (2 : ENNReal)
  have hALp : MemLp A 2 volume := by
    apply (memLp_two_iff_integrable_sq (by
      exact (show Continuous A by
        unfold A gmAffinePositiveTransformSum gmAffineTerm
        fun_prop).aestronglyMeasurable)).2
    exact integrable_gmAffinePositiveTransformSum_sq ft hft hM
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.HolderConjugate.two_two) (Eventually.of_forall hf)
      (Eventually.of_forall hA)
      (show MemLp f (ENNReal.ofReal 2) volume by simpa using hfLp)
      (show MemLp A (ENNReal.ofReal 2) volume by simpa using hALp)
  have hAJ := integral_gmAffinePositiveTransformSum_sq_le_J ft hft hM
  have hJnonneg : 0 ≤ gmAffineJ ft M := by
    have hIntegralNonneg :
        0 ≤ ∫ u : ℝ, gmAffinePositiveTransformSum ft M u ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    exact hIntegralNonneg.trans hAJ
  calc
    (∫ u : ℝ, f u * gmAffinePositiveTransformSum ft M u) ≤
        (∫ u : ℝ, f u ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ u : ℝ, A u ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hHolder
    _ = Real.sqrt (∫ u : ℝ, f u ^ 2) *
          Real.sqrt (∫ u : ℝ, A u ^ 2) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      norm_num
    _ ≤ Real.sqrt (∫ u : ℝ, f u ^ 2) *
          Real.sqrt (gmAffineJ ft M) := by
      gcongr

/- The exact finite retained-neighborhood expression produced by the
second Poisson window in (9.7). -/
noncomputable def gmAffineRetainedNeighborhoodSum
    (f : ℝ → ℝ) (T : ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ gmAffinePositiveShell M,
    ∑ m' ∈ gmAffinePositiveShell M,
      ∑ j ∈ gmAffineCentralShell M,
        ∫ u' in gmAffineUnitInterval T
          (((m : ℝ) * u + (j : ℝ)) / (m' : ℝ)), T * f u'

theorem gmAffineRetainedNeighborhoodSum_nonneg
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (u : ℝ) :
    0 ≤ gmAffineRetainedNeighborhoodSum f T M u := by
  unfold gmAffineRetainedNeighborhoodSum
  apply Finset.sum_nonneg
  intro m hm
  apply Finset.sum_nonneg
  intro m' hm'
  apply Finset.sum_nonneg
  intro j hj
  exact integral_nonneg fun u' => mul_nonneg hT (hf u')

/- Every retained `1/T`-neighborhood is bounded by the actual convolution
defining `f_tilde`; summing gives the literal affine family in `J`. -/
theorem gmAffineRetainedNeighborhoodSum_le_positiveTransform
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) (M : ℕ) (u : ℝ) :
    gmAffineRetainedNeighborhoodSum f T M u ≤
      gmAffinePositiveTransformSum
        (gmAffineTildeSchwartz T hT f) M u := by
  unfold gmAffineRetainedNeighborhoodSum gmAffinePositiveTransformSum
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro m' hm'
  apply Finset.sum_le_sum
  intro j hj
  exact setIntegral_gmAffineUnitInterval_le_tilde hT f hf
    (((m : ℝ) * u + (j : ℝ)) / (m' : ℝ))

/- Equation (9.8) for the exact finite retained-neighborhood sum. -/
theorem integral_mul_gmAffineRetainedNeighborhoodSum_le
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) {M : ℕ} (hM : 0 < M) :
    (∫ u : ℝ, f u * gmAffineRetainedNeighborhoodSum f T M u) ≤
      Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ (gmAffineTildeSchwartz T hT f) M) := by
  let ft := gmAffineTildeSchwartz T hT f
  let A : ℝ → ℝ := fun u => gmAffinePositiveTransformSum ft M u
  have hft : ∀ u, 0 ≤ ft u := gmAffineTildeSchwartz_nonneg T hT f hf
  have hfLp : MemLp f 2 volume := by simpa using f.memLp (2 : ENNReal)
  have hALp : MemLp A 2 volume := by
    apply (memLp_two_iff_integrable_sq (by
      exact (show Continuous A by
        unfold A gmAffinePositiveTransformSum gmAffineTerm
        fun_prop).aestronglyMeasurable)).2
    exact integrable_gmAffinePositiveTransformSum_sq ft hft hM
  have hright : Integrable (fun u : ℝ => f u * A u) :=
    hfLp.integrable_mul hALp
  have hpoint : ∀ u : ℝ,
      f u * gmAffineRetainedNeighborhoodSum f T M u ≤ f u * A u := by
    intro u
    exact mul_le_mul_of_nonneg_left
      (gmAffineRetainedNeighborhoodSum_le_positiveTransform hT f hf M u) (hf u)
  calc
    (∫ u : ℝ, f u * gmAffineRetainedNeighborhoodSum f T M u) ≤
        ∫ u : ℝ, f u * A u := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun u => mul_nonneg (hf u)
          (gmAffineRetainedNeighborhoodSum_nonneg hf hT.le M u))
        hright (Eventually.of_forall hpoint)
    _ ≤ Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ ft M) := by
      simpa only [A, ft] using
        integral_mul_gmAffinePositiveTransformSum_le hT f hf hM

/-! ### Finite replacement for the paper's downward induction in `epsilon` -/

/- A positive exponent can be raised past the crude exponent `100` by
finitely many multiplications by `3/2`.  This is the natural-number
termination certificate used in Proposition 9.1. -/
theorem exists_nat_three_halves_pow_mul_ge_hundred
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ j : ℕ, (100 : ℝ) ≤ (3 / 2 : ℝ) ^ j * epsilon := by
  have htend : Tendsto (fun j : ℕ => (3 / 2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ j : ℕ in atTop, 100 / epsilon < (3 / 2 : ℝ) ^ j :=
    htend.eventually_gt_atTop (100 / epsilon)
  rw [eventually_atTop] at hevent
  obtain ⟨j, hj⟩ := hevent
  refine ⟨j, ?_⟩
  have hquot : 100 / epsilon < (3 / 2 : ℝ) ^ j := hj j le_rfl
  rw [div_lt_iff₀ hepsilon] at hquot
  exact hquot.le

/- Crude base case for the finite Section 9 descent.  The preliminary
range `M ≤ T⁴` costs only `T⁸`, hence any exponent at least `100` absorbs
the elementary `M⁶‖f‖₂²` estimate. -/
theorem gmAffineJ_le_proposition9_base
    {delta T : ℝ} (hdelta : (100 : ℝ) ≤ delta) (hT : 2 ≤ T)
    (f : SchwartzMap ℝ ℝ) {M : ℕ} (hM : 0 < M)
    (hMT : (M : ℝ) ≤ T ^ 4) :
    gmAffineJ f M ≤ 36992 * T ^ delta *
      ((M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
        (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by
  have hfSqInt : Integrable (fun x : ℝ => f x ^ 2) := by
    apply (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).1
    simpa using f.memLp (2 : ENNReal)
  have hcrude := gmAffineJ_le_crude hfSqInt hM
  have hTone : (1 : ℝ) ≤ T := by linarith
  have hM2 : (M : ℝ) ^ 2 ≤ T ^ (8 : ℕ) := by
    calc
      (M : ℝ) ^ 2 ≤ (T ^ 4) ^ 2 := by gcongr
      _ = T ^ (8 : ℕ) := by ring
  have hT8 : T ^ (8 : ℕ) ≤ T ^ delta := by
    rw [← Real.rpow_natCast T 8]
    have h8delta : (8 : ℝ) ≤ delta := le_trans (by norm_num) hdelta
    exact Real.rpow_le_rpow_of_exponent_le hTone h8delta
  have hM2T : (M : ℝ) ^ 2 ≤ T ^ delta := hM2.trans hT8
  have hL2 : 0 ≤ ∫ x : ℝ, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2 := by positivity
  have hA : 0 ≤ (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 := by positivity
  calc
    gmAffineJ f M ≤ 36992 * (M : ℝ) ^ 6 * ∫ x : ℝ, f x ^ 2 := hcrude
    _ = 36992 * (M : ℝ) ^ 2 *
        ((M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by ring
    _ ≤ 36992 * T ^ delta *
        ((M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by gcongr
    _ ≤ 36992 * T ^ delta *
        ((M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
          (M : ℝ) ^ 4 * ∫ x : ℝ, f x ^ 2) := by
      have hfac : 0 ≤ (36992 : ℝ) * T ^ delta := by positivity
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) hfac

/-! ### The first-Poisson product fibers in the middle region -/

/- The exact finite set of retained first-Poisson pairs `(m₁, ℓ)`.
The product map on this set is the source variable `s = m₁ℓ` used to
avoid paying separately for every `m₁`. -/
noncomputable def gmAffineFirstPoissonPairs
    (M₁ M₃ : ℕ) (Q xi : ℝ) : Finset (ℤ × ℤ) :=
  (gmAffineSignedShell M₁).biUnion fun m₁ =>
    (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).image
      fun ell => (m₁, ell)

theorem mem_gmAffineFirstPoissonPairs
    {M₁ M₃ : ℕ} {Q xi : ℝ} {p : ℤ × ℤ} :
    p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi ↔
      p.1 ∈ gmAffineSignedShell M₁ ∧
        p.2 ∈ gmAffinePoissonNearSet M₃ (xi / (p.1 : ℝ)) Q := by
  classical
  simp only [gmAffineFirstPoissonPairs, Finset.mem_biUnion,
    Finset.mem_image]
  constructor
  · rintro ⟨m₁, hm₁, ell, hell, hp⟩
    rw [← hp]
    exact ⟨hm₁, hell⟩
  · rintro ⟨hp₁, hp₂⟩
    exact ⟨p.1, hp₁, p.2, hp₂, Prod.ext rfl rfl⟩

/- The finite product image of the retained first-Poisson pairs. -/
noncomputable def gmAffineFirstPoissonProducts
    (M₁ M₃ : ℕ) (Q xi : ℝ) : Finset ℤ :=
  (gmAffineFirstPoissonPairs M₁ M₃ Q xi).image
    fun p => p.1 * p.2

/- A nonzero product fiber injects into the signed divisor
antidiagonal.  This is the exact finite form of the divisor-bound step
in the proof of Lemma 9.2. -/
theorem card_gmAffineFirstPoissonPair_fiber_le_divisorsAntidiag
    (M₁ M₃ : ℕ) (Q xi : ℝ) {s : ℤ} (hs : s ≠ 0) :
    ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).filter
        fun p => p.1 * p.2 = s).card ≤ s.divisorsAntidiag.card := by
  classical
  apply Finset.card_le_card
  intro p hp
  rw [Int.mem_divisorsAntidiag]
  exact ⟨(Finset.mem_filter.mp hp).2, hs⟩

/- The signed divisor antidiagonal has exactly twice the ordinary
positive-divisor cardinality. -/
theorem card_int_divisorsAntidiag_eq_two_mul_natAbs_divisors
    (s : ℤ) :
    s.divisorsAntidiag.card = 2 * s.natAbs.divisors.card := by
  cases s with
  | ofNat n =>
      change ((n : ℤ).divisorsAntidiag).card = 2 * n.divisors.card
      rw [Int.divisorsAntidiag_natCast, Finset.card_disjUnion]
      simp only [Finset.card_map]
      rw [show n.divisorsAntidiagonal.card = n.divisors.card by
        rw [← Nat.map_div_right_divisors]
        simp]
      omega
  | negSucc n =>
      change ((-((n + 1 : ℕ) : ℤ)).divisorsAntidiag).card =
        2 * (n + 1).divisors.card
      rw [Int.divisorsAntidiag_neg_natCast, Finset.card_disjUnion]
      simp only [Finset.card_map]
      rw [show (n + 1).divisorsAntidiagonal.card = (n + 1).divisors.card by
        rw [← Nat.map_div_right_divisors]
        simp]
      omega

/- Fiberwise divisor estimate for the complete retained pair set.  The
nonzero-product hypothesis will be discharged from the lower boundary
of the middle-frequency region. -/
theorem card_gmAffineFirstPoissonPairs_le_sum_divisors
    (M₁ M₃ : ℕ) (Q xi : ℝ)
    (hnonzero : ∀ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
      p.1 * p.2 ≠ 0) :
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi).card ≤
      ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
        2 * s.natAbs.divisors.card := by
  classical
  rw [Finset.card_eq_sum_card_image
    (fun p : ℤ × ℤ => p.1 * p.2)
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi)]
  unfold gmAffineFirstPoissonProducts
  apply Finset.sum_le_sum
  intro s hs
  rw [← card_int_divisorsAntidiag_eq_two_mul_natAbs_divisors]
  apply card_gmAffineFirstPoissonPair_fiber_le_divisorsAntidiag
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  exact hnonzero p hp

/- The exact product-window radius following from the retained
first-Poisson cutoff. -/
noncomputable def gmAffineFirstPoissonRadius
    (M₁ M₃ : ℕ) (Q : ℝ) : ℝ :=
  Q * (2 * M₁ : ℝ) / (8 * M₃ : ℝ)

/- Every retained product lies in the narrow real window centered at
`-xi`.  This is the algebraic content of the passage from `(m₁,ℓ)`
to `s = m₁ℓ`. -/
theorem abs_add_product_lt_gmAffineFirstPoissonRadius
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) {p : ℤ × ℤ}
    (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    |xi + ((p.1 * p.2 : ℤ) : ℝ)| <
      gmAffineFirstPoissonRadius M₁ M₃ Q := by
  obtain ⟨hm₁, hell⟩ := mem_gmAffineFirstPoissonPairs.mp hp
  have hm₁neZ : p.1 ≠ 0 := gmAffineSignedShell_ne_zero hM₁ hm₁
  have hm₁neR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hm₁neZ
  have hnear : |(8 * M₃ : ℝ) *
      (xi / (p.1 : ℝ) + (p.2 : ℝ))| < Q := by
    unfold gmAffinePoissonNearSet at hell
    exact (Finset.mem_filter.mp hell).2
  have hrewrite : xi / (p.1 : ℝ) + (p.2 : ℝ) =
      (xi + (p.1 : ℝ) * (p.2 : ℝ)) / (p.1 : ℝ) := by
    field_simp [hm₁neR]
  rw [hrewrite, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 8 * M₃), abs_div] at hnear
  have hmabs : 0 < |(p.1 : ℝ)| := abs_pos.mpr hm₁neR
  have hscale : (0 : ℝ) < 8 * M₃ := by positivity
  have hdiv : |xi + (p.1 : ℝ) * (p.2 : ℝ)| / |(p.1 : ℝ)| <
      Q / (8 * M₃ : ℝ) := by
    rw [lt_div_iff₀ hscale]
    simpa only [mul_comm] using hnear
  have hmul : |xi + (p.1 : ℝ) * (p.2 : ℝ)| <
      (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := by
    rw [div_lt_iff₀ hmabs] at hdiv
    exact hdiv
  calc
    |xi + ((p.1 * p.2 : ℤ) : ℝ)| =
        |xi + (p.1 : ℝ) * (p.2 : ℝ)| := by push_cast; rfl
    _ < (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := hmul
    _ ≤ (Q / (8 * M₃ : ℝ)) * (2 * M₁ : ℝ) := by
      gcongr
      exact abs_gmAffineSignedShell_le_scale hm₁
    _ = gmAffineFirstPoissonRadius M₁ M₃ Q := by
      unfold gmAffineFirstPoissonRadius
      ring

/- The lower boundary of Region II excludes the zero product. -/
theorem gmAffineFirstPoissonPair_product_ne_zero
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q)
    (hxi : gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi|)
    {p : ℤ × ℤ} (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    p.1 * p.2 ≠ 0 := by
  intro hz
  have hdev := abs_add_product_lt_gmAffineFirstPoissonRadius
    hM₁ hM₃ hQ hp
  rw [hz, Int.cast_zero, add_zero] at hdev
  exact (not_lt_of_ge hxi) hdev

/- Integer interval containing the product image of all retained
first-Poisson pairs. -/
noncomputable def gmAffineFirstPoissonProductRange
    (M₁ M₃ : ℕ) (Q xi : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-xi - gmAffineFirstPoissonRadius M₁ M₃ Q⌋
    ⌈-xi + gmAffineFirstPoissonRadius M₁ M₃ Q⌉

theorem gmAffineFirstPoissonProducts_subset_range
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    gmAffineFirstPoissonProducts M₁ M₃ Q xi ⊆
      gmAffineFirstPoissonProductRange M₁ M₃ Q xi := by
  intro s hs
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  have hdev := abs_add_product_lt_gmAffineFirstPoissonRadius
    hM₁ hM₃ hQ hp
  rw [abs_lt] at hdev
  rw [gmAffineFirstPoissonProductRange, Finset.mem_Icc]
  constructor
  · have hfloor := Int.floor_mono
      (show -xi - gmAffineFirstPoissonRadius M₁ M₃ Q ≤
        ((p.1 * p.2 : ℤ) : ℝ) by linarith [hdev.1])
    rw [Int.floor_intCast] at hfloor
    simpa using hfloor
  · have hceil := Int.ceil_mono
      (show ((p.1 * p.2 : ℤ) : ℝ) ≤
        -xi + gmAffineFirstPoissonRadius M₁ M₃ Q by linarith [hdev.2])
    rw [Int.ceil_intCast] at hceil
    simpa using hceil

/- The containing integer interval has the source-size bound
`2 * radius + 3`, including both endpoint roundings. -/
theorem card_gmAffineFirstPoissonProductRange_real_le
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    ((gmAffineFirstPoissonProductRange M₁ M₃ Q xi).card : ℝ) ≤
      2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3 := by
  let R := gmAffineFirstPoissonRadius M₁ M₃ Q
  let a : ℤ := ⌊-xi - R⌋
  let b : ℤ := ⌈-xi + R⌉
  have hR : 0 ≤ R := by
    unfold R gmAffineFirstPoissonRadius
    positivity
  have haReal : (a : ℝ) ≤ -xi - R := Int.floor_le (-xi - R)
  have hbReal : -xi + R ≤ (b : ℝ) := Int.le_ceil (-xi + R)
  have habReal : (a : ℝ) ≤ (b : ℝ) := by linarith
  have hab : a ≤ b := by exact_mod_cast habReal
  have hdiff : 0 ≤ b + 1 - a := by omega
  have htoNat : (((b + 1 - a).toNat : ℕ) : ℤ) = b + 1 - a :=
    Int.toNat_of_nonneg hdiff
  have hcast : (((b + 1 - a).toNat : ℕ) : ℝ) =
      (b : ℝ) + 1 - (a : ℝ) := by
    exact_mod_cast htoNat
  have haClose := Int.lt_floor_add_one (-xi - R)
  have hbClose := Int.ceil_lt_add_one (-xi + R)
  rw [gmAffineFirstPoissonProductRange, Int.card_Icc]
  change (((b + 1 - a).toNat : ℕ) : ℝ) ≤ _
  rw [hcast]
  dsimp only [R] at haClose hbClose ⊢
  linarith

/- Consequently the number of distinct product values has the same
source-size bound. -/
theorem card_gmAffineFirstPoissonProducts_real_le
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    ((gmAffineFirstPoissonProducts M₁ M₃ Q xi).card : ℝ) ≤
      2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3 := by
  have hcard := Finset.card_le_card
    (gmAffineFirstPoissonProducts_subset_range hM₁ hM₃ (xi := xi) hQ)
  have hcardReal :
      ((gmAffineFirstPoissonProducts M₁ M₃ Q xi).card : ℝ) ≤
        ((gmAffineFirstPoissonProductRange M₁ M₃ Q xi).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardReal.trans
    (card_gmAffineFirstPoissonProductRange_real_le hM₁ hM₃ hQ)

/- Uniform form of the retained-pair divisor estimate.  Unlike the
existential wrapper above, the divisor constant is supplied once and
therefore remains independent of the Fourier variable `xi`. -/
theorem card_gmAffineFirstPoissonPairs_real_le_of_divisor
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hdiv : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ epsilon)
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi B : ℝ} (hQ : 0 < Q)
    (hxi : gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi|)
    (hB : 0 ≤ B)
    (hprod : ∀ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
      (s.natAbs : ℝ) ≤ B) :
    ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
      (2 * C) * B ^ epsilon *
        (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
  have hnonzero : ∀ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
      p.1 * p.2 ≠ 0 := by
    intro p hp
    exact gmAffineFirstPoissonPair_product_ne_zero hM₁ hM₃ hQ hxi hp
  have hnat := card_gmAffineFirstPoissonPairs_le_sum_divisors
    M₁ M₃ Q xi hnonzero
  have hreal : ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
      ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
        2 * (s.natAbs.divisors.card : ℝ) := by
    exact_mod_cast hnat
  calc
    ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
          2 * (s.natAbs.divisors.card : ℝ) := hreal
    _ ≤ ∑ _s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
          2 * (C * B ^ epsilon) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs₀ : s ≠ 0 := by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
        exact hnonzero p hp
      have hdivs := hdiv s.natAbs (Int.natAbs_pos.mpr hs₀)
      have hpow : (s.natAbs : ℝ) ^ epsilon ≤ B ^ epsilon :=
        Real.rpow_le_rpow (by positivity) (hprod s hs) hepsilon.le
      nlinarith [mul_le_mul_of_nonneg_left hpow hC.le]
    _ = (2 * C * B ^ epsilon) *
          ((gmAffineFirstPoissonProducts M₁ M₃ Q xi).card : ℝ) := by
      simp
      ring
    _ ≤ (2 * C) * B ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
      have hcard := card_gmAffineFirstPoissonProducts_real_le
        hM₁ hM₃ (xi := xi) hQ
      have hcoef : 0 ≤ 2 * C * B ^ epsilon := by positivity
      nlinarith

/- Absolute size of every product in the first-Poisson image. -/
theorem natAbs_le_abs_add_gmAffineFirstPoissonRadius
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q)
    {s : ℤ} (hs : s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi) :
    (s.natAbs : ℝ) ≤ |xi| + gmAffineFirstPoissonRadius M₁ M₃ Q := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  have hdev := abs_add_product_lt_gmAffineFirstPoissonRadius
    hM₁ hM₃ hQ hp
  rw [Nat.cast_natAbs, Int.cast_abs]
  grind

/- One divisor constant controls every point of the complete middle
frequency region.  This is the quantifier order needed before integrating
the pointwise Cauchy--Schwarz estimate in Guth--Maynard Lemma 9.2. -/
theorem exists_global_card_gmAffineFirstPoissonPairs_middle_real_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M₁ M₃ : ℕ}, 0 < M₁ → 0 < M₃ →
      ∀ {Q Y : ℝ}, 0 < Q → 0 ≤ Y → ∀ xi : ℝ,
      gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi| → |xi| ≤ Y →
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        C * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
  obtain ⟨D, hD, hdiv⟩ := divisorCountBound_native epsilon hepsilon
  refine ⟨2 * D, by positivity, ?_⟩
  intro M₁ M₃ hM₁ hM₃ Q Y hQ hY xi hxiLower hxiUpper
  apply card_gmAffineFirstPoissonPairs_real_le_of_divisor hepsilon hD hdiv
    hM₁ hM₃ hQ hxiLower
  · have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
      unfold gmAffineFirstPoissonRadius
      positivity
    linarith
  · intro s hs
    exact (natAbs_le_abs_add_gmAffineFirstPoissonRadius hM₁ hM₃ hQ hs).trans
      (by linarith)

/- Scale-specialized consequence of the single global divisor constant. -/
theorem exists_uniform_card_gmAffineFirstPoissonPairs_middle_real_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q Y : ℝ} (hQ : 0 < Q) (hY : 0 ≤ Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ xi : ℝ,
      gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi| → |xi| ≤ Y →
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        C * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_global_card_gmAffineFirstPoissonPairs_middle_real_le hepsilon
  exact ⟨C, hC, hbound hM₁ hM₃ hQ hY⟩

/- Exact finite reindexing of the nested first-Poisson sum by retained
`(m₁, ℓ)` pairs.  This is the sum-level companion to the cardinality
identity above and carries the actual Fourier summands into the divisor
counting argument. -/
theorem sum_gmAffineFirstPoissonPairs
    {A : Type*} [AddCommMonoid A]
    (M₁ M₃ : ℕ) (Q xi : ℝ) (F : ℤ × ℤ → A) :
    ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi, F p =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
          F (m₁, ell) := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(gmAffineSignedShell M₁))
      (fun m₁ : ℤ =>
        (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).image
          fun ell => (m₁, ell)) := by
    intro a ha b hb hab
    change Disjoint
      ((gmAffinePoissonNearSet M₃ (xi / (a : ℝ)) Q).image
        fun ell => (a, ell))
      ((gmAffinePoissonNearSet M₃ (xi / (b : ℝ)) Q).image
        fun ell => (b, ell))
    rw [Finset.disjoint_left]
    intro p hpa hpb
    grind
  unfold gmAffineFirstPoissonPairs
  rw [Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact congrArg Prod.snd hab

/- The complete `m₂` Fourier block attached to a retained first-Poisson
frequency.  It is kept intact when `(m₁, ℓ)` is reindexed by the product
`m₁ℓ`. -/
noncomputable def gmAffineM₂FourierBlock
    (f : SchwartzMap ℝ ℝ) (M₂ : ℕ) (m₁ : ℤ) (xi : ℝ) : ℂ :=
  ∑ m₂ ∈ gmAffinePositiveShell M₂,
    (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
      fourier (gmAffineComplexify f)
        (((m₂ : ℝ) / (m₁ : ℝ)) * xi))

/- A single retained `(m₁, ℓ)` summand of the first-Poisson main term. -/
noncomputable def gmAffineFirstPoissonPairTerm
    (f : SchwartzMap ℝ ℝ) (M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (xi : ℝ) (p : ℤ × ℤ) : ℂ :=
  gmAffineM₂FourierBlock f M₂ p.1 xi *
    gmAffineCentralPoissonKernel M₃ hM₃
      (xi / (p.1 : ℝ) + p.2)

/- The retained main term in equation (9.3), reindexed by the exact
finite pair set used in the divisor-counting argument. -/
theorem gmAffinePoissonMainFourier_eq_sum_pairs
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (Q xi : ℝ) :
    gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi =
      ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
        gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p := by
  rw [sum_gmAffineFirstPoissonPairs]
  unfold gmAffinePoissonMainFourier gmAffineFirstPoissonPairTerm
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  unfold gmAffineM₂FourierBlock
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/- Pointwise Cauchy--Schwarz after the source-faithful pair reindexing.
The outer factor is now exactly the pair count controlled by the divisor
bound, rather than the much larger product of the two shell sizes. -/
theorem norm_gmAffinePoissonMainFourier_sq_le_pairs
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (Q xi : ℝ) :
    ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2 ≤
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) *
        ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
          ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2 := by
  rw [gmAffinePoissonMainFourier_eq_sum_pairs]
  exact norm_sum_sq_le_card_mul_sum_norm_sq
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi)
    (gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi)

/- Exact ordered-pair expansion of the squared norm of a finite complex
sum.  The ordering agrees with the conjugated/unconjugated Fourier factors
used in equation (9.7). -/
theorem ofReal_norm_finset_sum_sq_expand
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) :
    ((‖∑ i ∈ s, a i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, star (a i) * a j := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/- Source-normalized integral formula for the Fourier transform of a
real Schwartz function.  The displayed sign and `2π` normalization are
the ones used in the phases `Z₁` and `Z₂` of equation (9.7). -/
theorem fourier_gmAffineComplexify_eq_integral
    (f : SchwartzMap ℝ ℝ) (xi : ℝ) :
    fourier (gmAffineComplexify f) xi =
      ∫ u : ℝ, Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) *
        (f u : ℂ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  rw [gmAffineComplexify_apply]
  simp only [Real.inner_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

/- Conjugated form of the source-normalized Fourier integral. -/
theorem conj_fourier_gmAffineComplexify_eq_integral
    (f : SchwartzMap ℝ ℝ) (xi : ℝ) :
    (starRingEnd ℂ) (fourier (gmAffineComplexify f) xi) =
      ∫ u : ℝ, Complex.exp ((((2 * Real.pi * u * xi) : ℝ) : ℂ) * I) *
        (f u : ℂ) := by
  rw [fourier_gmAffineComplexify_eq_integral]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  have hexp :
      (starRingEnd ℂ)
          (Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I)) =
        Complex.exp ((((2 * Real.pi * u * xi) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    simp
  simp_all

/-! ### Exact equation (9.7) source objects -/

/- The inner `m₂`-sum in the source definition of `Σ_II`. -/
noncomputable def gmAffineMiddleFourierBlock
    (f : SchwartzMap ℝ ℝ) (A : ℝ) (M₂ : ℕ) (ell : ℤ) (tau : ℝ) : ℂ :=
  ∑ m₂ ∈ gmAffinePositiveShell M₂,
    (m₂ : ℂ) * fourier (gmAffineComplexify f)
      ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau)

/- The exact first-to-second Poisson change of variables from the proof
of Lemma 9.2.  The physical variable
`tau = 8 M₃ (xi / m₁ + ell)` gives denominator `8 M₃`, not `M₁`.
This records the normalization before any cutoff is enlarged or any
rapidly decaying frequency is discarded. -/
noncomputable def gmAffineFirstPoissonTau
    (M₃ : ℕ) (m₁ ell : ℤ) (xi : ℝ) : ℝ :=
  (8 * M₃ : ℝ) * (xi / (m₁ : ℝ) + (ell : ℝ))

theorem gmAffineM₂FourierBlock_eq_middleBlock
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {m₁ ell : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁) (xi : ℝ) :
    gmAffineM₂FourierBlock f M₂ m₁ xi =
      ((1 / |(m₁ : ℝ)| : ℝ) : ℂ) *
        gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell)
          (gmAffineFirstPoissonTau M₃ m₁ ell xi) := by
  have hm₁neZ : m₁ ≠ 0 := gmAffineSignedShell_ne_zero hM₁ hm₁
  have hm₁neR : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁neZ
  have hdenom : (8 * M₃ : ℝ) ≠ 0 := by positivity
  unfold gmAffineM₂FourierBlock gmAffineMiddleFourierBlock
    gmAffineFirstPoissonTau
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  have hm₂posZ : (0 : ℤ) < m₂ := by
    have hm₂lower := (mem_gmAffinePositiveShell.mp hm₂).1
    exact lt_of_lt_of_le (by exact_mod_cast hM₂) hm₂lower
  have hm₂nonnegR : (0 : ℝ) ≤ m₂ := by exact_mod_cast hm₂posZ.le
  have hcoeff : |(m₂ : ℝ) / (m₁ : ℝ)| =
      (1 / |(m₁ : ℝ)|) * (m₂ : ℝ) := by
    rw [abs_div, abs_of_nonneg hm₂nonnegR]
    field_simp [abs_ne_zero.mpr hm₁neR]
  have harg : ((m₂ : ℝ) / (m₁ : ℝ)) * xi =
      ((-ell : ℤ) : ℝ) * (m₂ : ℝ) +
        ((m₂ : ℝ) / (8 * M₃ : ℕ)) *
          ((8 * M₃ : ℝ) * (xi / (m₁ : ℝ) + (ell : ℝ))) := by
    push_cast
    field_simp [hm₁neR, hdenom]
    ring
  rw [hcoeff, harg]
  push_cast
  ring

theorem mem_gmAffinePoissonNearSet_iff_firstPoissonTau
    {M₃ : ℕ} (hM₃ : 0 < M₃) {m₁ ell : ℤ} {Q xi : ℝ} :
    ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q ↔
      |gmAffineFirstPoissonTau M₃ m₁ ell xi| < Q := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact mem_gmAffinePoissonNearSet_of_lt hM₃ h

theorem gmAffineCentralPoissonKernel_eq_tau
    {M₃ : ℕ} (hM₃ : 0 < M₃) (m₁ ell : ℤ) (xi : ℝ) :
    gmAffineCentralPoissonKernel M₃ hM₃
        (xi / (m₁ : ℝ) + (ell : ℝ)) =
      ((8 * M₃ : ℝ) : ℂ) *
        gmAffineLocalBumpDual (gmAffineFirstPoissonTau M₃ m₁ ell xi) := by
  rw [gmAffineCentralPoissonKernel_eq_scaled]
  rfl

/- Exact retained summand after the source change of variables.  In
particular, the denominator in the middle Fourier block is `8 M₃` and
the retained cutoff is the physical condition `|tau| < Q`. -/
theorem gmAffineFirstPoissonPairTerm_eq_middleBlock
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q xi : ℝ} {p : ℤ × ℤ}
    (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p =
      (((1 / |(p.1 : ℝ)|) * (8 * M₃ : ℝ) : ℝ) : ℂ) *
        gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-p.2)
          (gmAffineFirstPoissonTau M₃ p.1 p.2 xi) *
        gmAffineLocalBumpDual
          (gmAffineFirstPoissonTau M₃ p.1 p.2 xi) := by
  obtain ⟨hp₁, hp₂⟩ := mem_gmAffineFirstPoissonPairs.mp hp
  unfold gmAffineFirstPoissonPairTerm
  rw [gmAffineM₂FourierBlock_eq_middleBlock f hM₁ hM₂ hM₃ hp₁,
    gmAffineCentralPoissonKernel_eq_tau hM₃]
  push_cast
  ring

theorem norm_gmAffineFirstPoissonPairTerm_sq_eq
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q xi : ℝ} {p : ℤ × ℤ}
    (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2 =
      (((8 * M₃ : ℝ) / |(p.1 : ℝ)|) ^ 2) *
        ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-p.2)
          (gmAffineFirstPoissonTau M₃ p.1 p.2 xi)‖ ^ 2 *
        ‖gmAffineLocalBumpDual
          (gmAffineFirstPoissonTau M₃ p.1 p.2 xi)‖ ^ 2 := by
  rw [gmAffineFirstPoissonPairTerm_eq_middleBlock f hM₁ hM₂ hM₃ hp]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  grind

/- The scaled compact majorant required by the actual retained window
`|tau| < Q`.  Keeping `Q` in the definition prevents the fixed-width
surrogate from being confused with the source middle-frequency term. -/
noncomputable def gmAffineMiddleTauWeight (Q tau : ℝ) : ℝ :=
  gmCubicLocalBump (tau / Q)

theorem gmAffineMiddleTauWeight_nonneg (Q tau : ℝ) :
    0 ≤ gmAffineMiddleTauWeight Q tau :=
  gmCubicLocalBump_nonneg _

theorem gmAffineMiddleTauWeight_le_one (Q tau : ℝ) :
    gmAffineMiddleTauWeight Q tau ≤ 1 :=
  gmCubicLocalBump_le_one _

theorem gmAffineMiddleTauWeight_eq_zero_of_not_mem
    {Q : ℝ} (hQ : 0 < Q) {tau : ℝ}
    (htau : tau ∉ Set.Icc (-2 * Q) (2 * Q)) :
    gmAffineMiddleTauWeight Q tau = 0 := by
  unfold gmAffineMiddleTauWeight
  apply gmCubicLocalBump_eq_zero_of_two_le_abs
  rw [abs_div, abs_of_pos hQ, le_div_iff₀ hQ]
  grind

theorem continuous_gmAffineMiddleTauWeight (Q : ℝ) :
    Continuous (gmAffineMiddleTauWeight Q) := by
  have hbcont : Continuous gmCubicLocalBump := by
    exact dfiUnitRedundantBump.continuous.comp (continuous_id.div_const 2)
  unfold gmAffineMiddleTauWeight
  exact hbcont.comp (by fun_prop)

theorem hasCompactSupport_gmAffineMiddleTauWeight
    {Q : ℝ} (hQ : 0 < Q) :
    HasCompactSupport (gmAffineMiddleTauWeight Q) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-2 * Q) (2 * Q)))
  intro tau htau
  have hout : tau < -2 * Q ∨ 2 * Q < tau := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using htau
  apply gmCubicLocalBump_eq_zero_of_two_le_abs
  rw [abs_div, abs_of_pos hQ, le_div_iff₀ hQ]
  rcases hout with hleft | hright
  · rw [abs_of_neg (by linarith : tau < 0)]
    linarith
  · rw [abs_of_pos (by linarith : 0 < tau)]
    linarith

theorem gmAffineMiddleTauWeight_one_of_abs_lt
    {Q tau : ℝ} (hQ : 0 < Q) (htau : |tau| < Q) :
    gmAffineMiddleTauWeight Q tau = 1 := by
  unfold gmAffineMiddleTauWeight
  apply gmCubicLocalBump_one
  rw [abs_div, abs_of_pos hQ]
  exact (div_le_one hQ).mpr htau.le

theorem continuous_gmAffineMiddleFourierBlock
    (f : SchwartzMap ℝ ℝ) (A M₂ : ℕ) (ell : ℤ) :
    Continuous (gmAffineMiddleFourierBlock f A M₂ ell) := by
  unfold gmAffineMiddleFourierBlock
  fun_prop

theorem integrable_gmAffineMiddleTauWeightedBlockSq
    {Q : ℝ} (hQ : 0 < Q) (f : SchwartzMap ℝ ℝ)
    (A M₂ : ℕ) (ell : ℤ) :
    Integrable (fun tau : ℝ =>
      gmAffineMiddleTauWeight Q tau *
        ‖gmAffineMiddleFourierBlock f A M₂ ell tau‖ ^ 2) := by
  have hcont : Continuous (fun tau : ℝ =>
      gmAffineMiddleTauWeight Q tau *
        ‖gmAffineMiddleFourierBlock f A M₂ ell tau‖ ^ 2) :=
    (continuous_gmAffineMiddleTauWeight Q).mul
      ((continuous_gmAffineMiddleFourierBlock f A M₂ ell).norm.pow 2)
  have hcomp : HasCompactSupport (fun tau : ℝ =>
      gmAffineMiddleTauWeight Q tau *
        ‖gmAffineMiddleFourierBlock f A M₂ ell tau‖ ^ 2) := by
    change HasCompactSupport
      (gmAffineMiddleTauWeight Q * fun tau : ℝ =>
        ‖gmAffineMiddleFourierBlock f A M₂ ell tau‖ ^ 2)
    exact (hasCompactSupport_gmAffineMiddleTauWeight hQ).mul_right
  exact hcont.integrable_of_hasCompactSupport hcomp

/- A finite-frequency version of the `Z₂` factor in equation (9.7).
The full source cutoff is recovered once its compact integer support is
identified. -/
noncomputable def gmAffineMiddleZ₂Finite
    (L : Finset ℤ) (T : ℝ) (M₂ : ℕ)
    (m₂ m₂' : ℤ) (u u' : ℝ) : ℂ :=
  ∑ ell ∈ L,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
        gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)

/- The finite-frequency form of `Σ_II` before expanding the Fourier
square. -/
noncomputable def gmAffineSigmaIIFinite
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T M₁ : ℝ) (M₂ : ℕ) : ℂ :=
  ∑ ell ∈ L,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
        ((‖gmAffineMiddleFourierBlock f M₁ M₂ ell tau‖ ^ 2 : ℝ) : ℂ)

/- Exact ordered-pair expansion of the Fourier block in `Σ_II`; no
frequency, coefficient, or conjugation is discarded. -/
theorem ofReal_norm_gmAffineMiddleFourierBlock_sq_expand
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (M₂ : ℕ) (ell : ℤ) (tau : ℝ) :
    ((‖gmAffineMiddleFourierBlock f M₁ M₂ ell tau‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          star ((m₂' : ℂ) * fourier (gmAffineComplexify f)
            ((ell : ℝ) * (m₂' : ℝ) + ((m₂' : ℝ) / M₁) * tau)) *
          ((m₂ : ℂ) * fourier (gmAffineComplexify f)
            ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau)) := by
  unfold gmAffineMiddleFourierBlock
  exact ofReal_norm_finset_sum_sq_expand
    (gmAffinePositiveShell M₂)
    (fun m₂ => (m₂ : ℂ) * fourier (gmAffineComplexify f)
      ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau))

/- Exact two-variable integral expansion of one conjugated Fourier pair.
This is the Fubini kernel from which the phases `Z₁` and `Z₂` in (9.7)
are obtained. -/
theorem gmAffineFourierPair_eq_iteratedIntegral
    (f : SchwartzMap ℝ ℝ) (m₂ m₂' : ℤ) (xi xi' : ℝ) :
    (starRingEnd ℂ) ((m₂' : ℂ) * fourier (gmAffineComplexify f) xi') *
        ((m₂ : ℂ) * fourier (gmAffineComplexify f) xi) =
      ∫ u' : ℝ, ∫ u : ℝ,
        (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
          Complex.exp ((((2 * Real.pi * (u' * xi' - u * xi)) : ℝ) : ℂ) * I) := by
  rw [map_mul, conj_fourier_gmAffineComplexify_eq_integral,
    fourier_gmAffineComplexify_eq_integral]
  simp only [map_intCast]
  let A : ℝ → ℂ := fun u' =>
    Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) * (f u' : ℂ)
  let B : ℝ → ℂ := fun u =>
    Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) * (f u : ℂ)
  change ((m₂' : ℂ) * ∫ u', A u') * ((m₂ : ℂ) * ∫ u, B u) = _
  calc
    ((m₂' : ℂ) * ∫ u', A u') * ((m₂ : ℂ) * ∫ u, B u) =
        (∫ u', A u') * (((m₂' * m₂ : ℤ) : ℂ) * ∫ u, B u) := by
      push_cast
      ring
    _ = ∫ u' : ℝ, A u' * (((m₂' * m₂ : ℤ) : ℂ) * ∫ u, B u) := by
      rw [integral_mul_const]
    _ = ∫ u' : ℝ, ∫ u : ℝ, A u' * (((m₂' * m₂ : ℤ) : ℂ) * B u) := by
      apply integral_congr_ae
      filter_upwards with u'
      rw [integral_const_mul]
      rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u'
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [A, B]
      calc
        Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) * (f u' : ℂ) *
            (((m₂' * m₂ : ℤ) : ℂ) *
              (Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) * (f u : ℂ))) =
            (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
              (Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) *
                Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring

/- First exact expansion of finite `Σ_II`: the Fourier square is replaced
by its ordered `(m₂',m₂)` double sum and each Fourier pair by the literal
two-variable integral.  This is equation (9.7) before commuting the finite
sums and compact `τ` integral. -/
theorem gmAffineSigmaIIFinite_eq_expandedFourierPairs
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T M₁ : ℝ) (M₂ : ℕ) :
    gmAffineSigmaIIFinite L f T M₁ M₂ =
      ∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                ∫ u' : ℝ, ∫ u : ℝ,
                  (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
                    Complex.exp ((((2 * Real.pi *
                      (u' * ((ell : ℝ) * (m₂' : ℝ) +
                          ((m₂' : ℝ) / M₁) * tau) -
                        u * ((ell : ℝ) * (m₂ : ℝ) +
                          ((m₂ : ℝ) / M₁) * tau))) : ℝ) : ℂ) * I) := by
  unfold gmAffineSigmaIIFinite
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  apply integral_congr_ae
  filter_upwards with tau
  congr 1
  rw [ofReal_norm_gmAffineMiddleFourierBlock_sq_expand]
  apply Finset.sum_congr rfl
  intro m₂' hm₂'
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  exact gmAffineFourierPair_eq_iteratedIntegral f m₂ m₂'
    ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau)
    ((ell : ℝ) * (m₂' : ℝ) + ((m₂' : ℝ) / M₁) * tau)

/- The expanded Fourier-pair phase splits exactly into the compact
`τ` phase `Z₁` and the integer-frequency phase `Z₂` from equation (9.7). -/
theorem gmAffineMiddlePairPhase_exp_eq_Z₁_mul_Z₂
    (M₁ : ℝ) (ell m₂ m₂' : ℤ) (u u' tau : ℝ) :
    Complex.exp ((((2 * Real.pi *
        (u' * ((ell : ℝ) * (m₂' : ℝ) + ((m₂' : ℝ) / M₁) * tau) -
          u * ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau))) : ℝ) : ℂ) * I) =
      Complex.exp ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
        Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
          gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]
  congr 1
  unfold gmAffineMiddleTauPhase gmAffineMiddleDisplacement
  push_cast
  ring

/- Equation (9.7) with the phase already separated into its `Z₁` and
`Z₂` factors, still in the original finite-sum/integral order. -/
theorem gmAffineSigmaIIFinite_eq_expanded_Z₁_Z₂_integrands
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T M₁ : ℝ) (M₂ : ℕ) :
    gmAffineSigmaIIFinite L f T M₁ M₂ =
      ∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                ∫ u' : ℝ, ∫ u : ℝ,
                  (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
                    (Complex.exp
                      ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                    Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                      gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)) := by
  rw [gmAffineSigmaIIFinite_eq_expandedFourierPairs]
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  apply integral_congr_ae
  filter_upwards with tau
  congr 1
  apply Finset.sum_congr rfl
  intro m₂' hm₂'
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  apply integral_congr_ae
  filter_upwards with u'
  apply integral_congr_ae
  filter_upwards with u
  rw [gmAffineMiddlePairPhase_exp_eq_Z₁_mul_Z₂]

/- The full `(τ,(u',u))` kernel after splitting the equation-(9.7)
phase. -/
noncomputable def gmAffineMiddleTripleKernel
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (ell m₂ m₂' : ℤ)
    (z : ℝ × (ℝ × ℝ)) : ℂ :=
  (gmCubicLocalBump z.1 : ℂ) *
    ((((m₂' * m₂ : ℤ) : ℂ) * (f z.2.1 : ℂ) * (f z.2.2 : ℂ)) *
      (Complex.exp
          ((gmAffineMiddleTauPhase M₁ m₂ m₂' z.2.2 z.2.1 z.1 : ℂ) * I) *
        Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
          gmAffineMiddleDisplacement m₂ m₂' z.2.2 z.2.1) : ℝ) : ℂ) * I)))

/- Absolute integrability of the complete equation-(9.7) triple kernel. -/
theorem integrable_gmAffineMiddleTripleKernel
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (ell m₂ m₂' : ℤ) :
    Integrable (gmAffineMiddleTripleKernel f M₁ ell m₂ m₂')
      (volume.prod (volume.prod volume)) := by
  have hb : Integrable (fun tau : ℝ => ‖(gmCubicLocalBump tau : ℂ)‖) := by
    simpa only [gmAffineLocalBumpSchwartz_apply] using
      gmAffineLocalBumpSchwartz.integrable.norm
  have hf : Integrable (fun u : ℝ => ‖gmAffineComplexify f u‖) :=
    (gmAffineComplexify f).integrable.norm
  have hpair : Integrable (fun q : ℝ × ℝ =>
      ‖gmAffineComplexify f q.1‖ * ‖gmAffineComplexify f q.2‖)
      (volume.prod volume) := hf.mul_prod hf
  have hprod : Integrable (fun z : ℝ × (ℝ × ℝ) =>
      ‖(gmCubicLocalBump z.1 : ℂ)‖ *
        (‖gmAffineComplexify f z.2.1‖ * ‖gmAffineComplexify f z.2.2‖))
      (volume.prod (volume.prod volume)) := hb.mul_prod hpair
  have hmajor : Integrable (fun z : ℝ × (ℝ × ℝ) =>
      ‖((m₂' * m₂ : ℤ) : ℂ)‖ *
        (‖(gmCubicLocalBump z.1 : ℂ)‖ *
          (‖gmAffineComplexify f z.2.1‖ * ‖gmAffineComplexify f z.2.2‖)))
      (volume.prod (volume.prod volume)) := hprod.const_mul _
  apply hmajor.mono'
  · unfold gmAffineMiddleTripleKernel
    change AEStronglyMeasurable (fun z : ℝ × (ℝ × ℝ) =>
      gmAffineLocalBumpSchwartz z.1 *
        ((((m₂' * m₂ : ℤ) : ℂ) * gmAffineComplexify f z.2.1 *
            gmAffineComplexify f z.2.2) *
          (Complex.exp
              ((gmAffineMiddleTauPhase M₁ m₂ m₂' z.2.2 z.2.1 z.1 : ℂ) * I) *
            Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
              gmAffineMiddleDisplacement m₂ m₂' z.2.2 z.2.1) : ℝ) : ℂ) * I))))
    apply Continuous.aestronglyMeasurable
    have hbcont : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        gmAffineLocalBumpSchwartz z.1) :=
      gmAffineLocalBumpSchwartz.continuous.comp continuous_fst
    have hfcont₁ : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        gmAffineComplexify f z.2.1) :=
      (gmAffineComplexify f).continuous.comp (continuous_fst.comp continuous_snd)
    have hfcont₂ : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        gmAffineComplexify f z.2.2) :=
      (gmAffineComplexify f).continuous.comp (continuous_snd.comp continuous_snd)
    have hphase : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        Complex.exp
            ((gmAffineMiddleTauPhase M₁ m₂ m₂' z.2.2 z.2.1 z.1 : ℂ) * I) *
          Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
            gmAffineMiddleDisplacement m₂ m₂' z.2.2 z.2.1) : ℝ) : ℂ) * I)) := by
      unfold gmAffineMiddleTauPhase gmAffineMiddleDisplacement
      fun_prop
    exact hbcont.mul
      (((continuous_const.mul hfcont₁).mul hfcont₂).mul hphase)
  · filter_upwards with z
    unfold gmAffineMiddleTripleKernel
    simp only [norm_mul, Complex.norm_exp, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, Real.exp_zero]
    simp only [gmAffineComplexify_apply, norm_real]
    ring_nf
    exact le_rfl

/- Exact Fubini interchange from the source order `(τ,u',u)` to the
equation-(9.7) order `(u',u,τ)`. -/
theorem integral_tau_u'_u_gmAffineMiddleTripleKernel_eq_u'_u_tau
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (ell m₂ m₂' : ℤ) :
    (∫ tau : ℝ, ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      ∫ u' : ℝ, ∫ u : ℝ, ∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u)) := by
  let F : ℝ × (ℝ × ℝ) → ℂ :=
    gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  have hF : Integrable F (volume.prod (volume.prod volume)) :=
    integrable_gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  calc
    (∫ tau : ℝ, ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      ∫ tau : ℝ, ∫ q : ℝ × ℝ, F (tau, q) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hF.prod_right_ae] with tau htau
        exact (MeasureTheory.integral_prod _ htau).symm
    _ = ∫ z : ℝ × (ℝ × ℝ), F z ∂(volume.prod (volume.prod volume)) :=
      (MeasureTheory.integral_prod _ hF).symm
    _ = ∫ q : ℝ × ℝ, ∫ tau : ℝ, F (tau, q) :=
      MeasureTheory.integral_prod_symm _ hF
    _ = ∫ u' : ℝ, ∫ u : ℝ, ∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u)) := by
      simpa [F, Measure.volume_eq_prod] using MeasureTheory.integral_prod
        (fun q : ℝ × ℝ => ∫ tau : ℝ, F (tau, q)) hF.integral_prod_right

/- The inner `τ`-integral of the full kernel is exactly the compact
factor `Z₁`, with the integer-frequency phase retained. -/
theorem integral_gmAffineMiddleTripleKernel_eq_Z₁
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (ell m₂ m₂' : ℤ) (u u' : ℝ) :
    (∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
        gmAffineMiddleZ₁ M₁ m₂ m₂' u u' *
        Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
          gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I) := by
  let A : ℂ := ((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)
  let E : ℂ := Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
    gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)
  calc
    (∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      ∫ tau : ℝ, A *
          ((gmCubicLocalBump tau : ℂ) *
            Complex.exp
              ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I)) * E := by
        apply integral_congr_ae
        filter_upwards with tau
        unfold gmAffineMiddleTripleKernel
        ring
    _ = A * (∫ tau : ℝ,
          (gmCubicLocalBump tau : ℂ) *
            Complex.exp
              ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I)) * E := by
      rw [integral_mul_const, integral_const_mul]
    _ = _ := by
      rfl

/- Moving the compact `τ` cutoff through the two Fourier variables gives
the literal triple kernel. -/
theorem gmCubicLocalBump_mul_fourierPairIntegral_eq_tripleKernel
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (ell m₂ m₂' : ℤ) (tau : ℝ) :
    (gmCubicLocalBump tau : ℂ) *
        (∫ u' : ℝ, ∫ u : ℝ,
          (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
            (Complex.exp
                ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
              Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u'
  rw [← integral_const_mul]
  rfl

/- One fixed `(ell,m₂',m₂)` contribution in the source order is exactly
its equation-(9.7) `Z₁` contribution in the Fourier-analysis order. -/
theorem gmAffineMiddleWeightedComponent_eq_Z₁
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ)
    (ell m₂ m₂' : ℤ) :
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
        (∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
          ∫ u' : ℝ, ∫ u : ℝ,
            (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
              (Complex.exp
                  ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                  gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      ∫ u' : ℝ, ∫ u : ℝ,
        (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
          gmAffineMiddleZ₁ M₁ m₂ m₂' u u' *
          ((gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
            Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
              gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)) := by
  let c : ℂ :=
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ)
  calc
    c * (∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
          ∫ u' : ℝ, ∫ u : ℝ,
            (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
              (Complex.exp
                  ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                  gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      c * (∫ tau : ℝ, ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with tau
          exact gmCubicLocalBump_mul_fourierPairIntegral_eq_tripleKernel
            f M₁ ell m₂ m₂' tau
    _ = c * (∫ u' : ℝ, ∫ u : ℝ, ∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) := by
          rw [integral_tau_u'_u_gmAffineMiddleTripleKernel_eq_u'_u_tau]
    _ = ∫ u' : ℝ, ∫ u : ℝ, c *
        (∫ tau : ℝ,
          gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with u'
          rw [← integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u'
      apply integral_congr_ae
      filter_upwards with u
      rw [integral_gmAffineMiddleTripleKernel_eq_Z₁]
      ring

/- The source-order contribution of one fixed middle frequency pair. -/
noncomputable def gmAffineMiddleSourceTerm
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (ell m₂ m₂' : ℤ) (tau : ℝ) : ℂ :=
  (gmCubicLocalBump tau : ℂ) *
    ∫ u' : ℝ, ∫ u : ℝ,
      (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
        (Complex.exp
            ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
          Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
            gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))

/- The equation-(9.7) contribution of one fixed integer frequency and
one fixed middle-shell pair. -/
noncomputable def gmAffineMiddleEquation97Term
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ)
    (ell m₂ m₂' : ℤ) (q : ℝ × ℝ) : ℂ :=
  (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
    gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
    ((gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
        gmAffineMiddleDisplacement m₂ m₂' q.2 q.1) : ℝ) : ℂ) * I))

theorem integrable_gmAffineMiddleSourceTerm
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (ell m₂ m₂' : ℤ) :
    Integrable (gmAffineMiddleSourceTerm f M₁ ell m₂ m₂') := by
  let F : ℝ × (ℝ × ℝ) → ℂ :=
    gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  have hF : Integrable F (volume.prod (volume.prod volume)) :=
    integrable_gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  refine hF.integral_prod_left.congr ?_
  filter_upwards [hF.prod_right_ae] with tau htau
  unfold gmAffineMiddleSourceTerm
  rw [gmCubicLocalBump_mul_fourierPairIntegral_eq_tripleKernel]
  exact MeasureTheory.integral_prod _ htau

theorem integrable_gmAffineMiddleEquation97Term
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ)
    (ell m₂ m₂' : ℤ) :
    Integrable (gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂')
      (volume.prod volume) := by
  let F : ℝ × (ℝ × ℝ) → ℂ :=
    gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  let c : ℂ :=
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ)
  have hF : Integrable F (volume.prod (volume.prod volume)) :=
    integrable_gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  have hc : Integrable (fun q : ℝ × ℝ =>
      c * ∫ tau : ℝ, F (tau, q)) (volume.prod volume) :=
    hF.integral_prod_right.const_mul c
  refine hc.congr ?_
  filter_upwards with q
  rw [integral_gmAffineMiddleTripleKernel_eq_Z₁]
  unfold gmAffineMiddleEquation97Term
  ring

/- Exact equation-(9.7) rearrangement for one fixed integer frequency,
including both ordered middle-shell sums. -/
theorem gmAffineMiddleEllSource_eq_equation97
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ) (ell : ℤ) :
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
        (∫ tau : ℝ,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) =
      ∫ q : ℝ × ℝ,
        ∑ m₂' ∈ gmAffinePositiveShell M₂,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
  let c : ℂ :=
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ)
  calc
    c * (∫ tau : ℝ,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) =
      c * (∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∫ tau : ℝ, gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) := by
        congr 1
        rw [MeasureTheory.integral_finsetSum _ (fun m₂' _ =>
          integrable_finsetSum _ (fun m₂ _ =>
            integrable_gmAffineMiddleSourceTerm f M₁ ell m₂ m₂'))]
        apply Finset.sum_congr rfl
        intro m₂' hm₂'
        rw [MeasureTheory.integral_finsetSum _ (fun m₂ _ =>
          integrable_gmAffineMiddleSourceTerm f M₁ ell m₂ m₂')]
    _ = ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          c * (∫ tau : ℝ,
            gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) := by
      simp only [Finset.mul_sum]
    _ = ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∫ u' : ℝ, ∫ u : ℝ,
            gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' (u', u) := by
      apply Finset.sum_congr rfl
      intro m₂' hm₂'
      apply Finset.sum_congr rfl
      intro m₂ hm₂
      unfold gmAffineMiddleSourceTerm gmAffineMiddleEquation97Term
      exact gmAffineMiddleWeightedComponent_eq_Z₁ f T M₁ M₂ ell m₂ m₂'
    _ = ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∫ q : ℝ × ℝ,
            gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
      apply Finset.sum_congr rfl
      intro m₂' hm₂'
      apply Finset.sum_congr rfl
      intro m₂ hm₂
      exact (MeasureTheory.integral_prod _
        (integrable_gmAffineMiddleEquation97Term
          f T M₁ M₂ ell m₂ m₂')).symm
    _ = _ := by
      calc
        (∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              ∫ q : ℝ × ℝ,
                gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q) =
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∫ q : ℝ × ℝ,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
            apply Finset.sum_congr rfl
            intro m₂' hm₂'
            exact (MeasureTheory.integral_finsetSum _ (fun m₂ _ =>
              integrable_gmAffineMiddleEquation97Term
                f T M₁ M₂ ell m₂ m₂')).symm
        _ = _ := (MeasureTheory.integral_finsetSum _ (fun m₂' _ =>
          integrable_finsetSum _ (fun m₂ _ =>
            integrable_gmAffineMiddleEquation97Term
              f T M₁ M₂ ell m₂ m₂'))).symm

/- Summing the fixed-frequency equation-(9.7) terms produces exactly the
finite `Z₂` factor. -/
theorem sum_gmAffineMiddleEquation97Term_eq_Z₂Finite
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ)
    (m₂ m₂' : ℤ) (q : ℝ × ℝ) :
    (∑ ell ∈ L,
        gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q) =
      (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
        gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
        gmAffineMiddleZ₂Finite L T M₂ m₂ m₂' q.2 q.1 := by
  unfold gmAffineMiddleEquation97Term gmAffineMiddleZ₂Finite
  simp only [Finset.mul_sum]

/- The finite-frequency right side of Guth--Maynard equation (9.7). -/
noncomputable def gmAffineSigmaIIEquation97Finite
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T M₁ : ℝ) (M₂ : ℕ) : ℂ :=
  ∫ q : ℝ × ℝ,
    ∑ m₂' ∈ gmAffinePositiveShell M₂,
      ∑ m₂ ∈ gmAffinePositiveShell M₂,
        (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
          gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
          gmAffineMiddleZ₂Finite L T M₂ m₂ m₂' q.2 q.1

/- Exact finite-frequency form of Guth--Maynard equation (9.7), with all
three finite sums, both real integrals, and the `Z₁ Z₂` factors retained. -/
theorem gmAffineSigmaIIFinite_eq_equation97
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T M₁ : ℝ) (M₂ : ℕ) :
    gmAffineSigmaIIFinite L f T M₁ M₂ =
      gmAffineSigmaIIEquation97Finite L f T M₁ M₂ := by
  rw [gmAffineSigmaIIFinite_eq_expanded_Z₁_Z₂_integrands]
  unfold gmAffineSigmaIIEquation97Finite
  calc
    (∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                ∫ u' : ℝ, ∫ u : ℝ,
                  (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
                    (Complex.exp
                      ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                    Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                      gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      ∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ,
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau := by
          apply Finset.sum_congr rfl
          intro ell hell
          congr 1
          apply integral_congr_ae
          filter_upwards with tau
          unfold gmAffineMiddleSourceTerm
          simp only [Finset.mul_sum]
    _ = ∑ ell ∈ L,
        ∫ q : ℝ × ℝ,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
          apply Finset.sum_congr rfl
          intro ell hell
          exact gmAffineMiddleEllSource_eq_equation97 f T M₁ M₂ ell
    _ = ∫ q : ℝ × ℝ,
        ∑ ell ∈ L,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
          exact (MeasureTheory.integral_finsetSum L (fun ell _ =>
            integrable_finsetSum _ (fun m₂' _ =>
              integrable_finsetSum _ (fun m₂ _ =>
                integrable_gmAffineMiddleEquation97Term
                  f T M₁ M₂ ell m₂ m₂')))).symm
    _ = ∫ q : ℝ × ℝ,
        ∑ m₂' ∈ gmAffinePositiveShell M₂,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
              gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
              gmAffineMiddleZ₂Finite L T M₂ m₂ m₂' q.2 q.1 := by
          apply integral_congr_ae
          filter_upwards with q
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro m₂' hm₂'
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro m₂ hm₂
          exact sum_gmAffineMiddleEquation97Term_eq_Z₂Finite
            L f T M₁ M₂ m₂ m₂' q

/- A symmetric integer window containing the complete support of the
source cutoff `ψ₂(M₂ ell / T)`.  The extra unit makes the endpoint
comparison strict and avoids any convention at `|x| = 2`. -/
noncomputable def gmAffineMiddleFrequencySupport (T : ℝ) (M₂ : ℕ) : Finset ℤ :=
  let B : ℕ := ⌈2 * T / (M₂ : ℝ)⌉₊ + 1
  Finset.Icc (-(B : ℤ)) (B : ℤ)

theorem gmCubicLocalBump_middleFrequency_eq_zero_of_not_mem
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    {ell : ℤ} (hell : ell ∉ gmAffineMiddleFrequencySupport T M₂) :
    gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) = 0 := by
  let B : ℕ := ⌈2 * T / (M₂ : ℝ)⌉₊ + 1
  have hceil : 2 * T / (M₂ : ℝ) ≤
      (⌈2 * T / (M₂ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hB : 2 * T / (M₂ : ℝ) < (B : ℝ) := by
    dsimp only [B]
    push_cast
    linarith
  have hell' : ell < -(B : ℤ) ∨ (B : ℤ) < ell := by
    simpa only [gmAffineMiddleFrequencySupport, B, Finset.mem_Icc,
      not_and_or, not_le] using hell
  have hellAbs : (B : ℝ) < |(ell : ℝ)| := by
    rcases hell' with hleft | hright
    · have hleft' : (ell : ℝ) < -(B : ℝ) := by exact_mod_cast hleft
      rw [abs_of_neg (by linarith)]
      linarith
    · have hright' : (B : ℝ) < (ell : ℝ) := by exact_mod_cast hright
      rw [abs_of_pos (by linarith)]
      exact hright'
  apply gmCubicLocalBump_eq_zero_of_two_le_abs
  rw [abs_div, abs_mul, abs_of_pos hT, abs_of_pos (by positivity : (0 : ℝ) < M₂)]
  apply (le_div_iff₀ hT).2
  have hscale : 2 * T < (M₂ : ℝ) * |(ell : ℝ)| := by
    have hM₂real : (0 : ℝ) < M₂ := by positivity
    have := mul_lt_mul_of_pos_left (lt_trans hB hellAbs) hM₂real
    calc
      2 * T = (M₂ : ℝ) * (2 * T / (M₂ : ℝ)) := by field_simp
      _ < (M₂ : ℝ) * |(ell : ℝ)| := this
  linarith

/- The finite source-support sum is exactly the complete integer lattice
sum `Z₂`; no tail is being discarded before Poisson summation. -/
theorem gmAffineMiddleZ₂Finite_support_eq_Z₂
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (m₂ m₂' : ℤ) (u u' : ℝ) :
    gmAffineMiddleZ₂Finite (gmAffineMiddleFrequencySupport T M₂)
        T M₂ m₂ m₂' u u' =
      gmAffineMiddleZ₂ T M₂ m₂ m₂' u u' := by
  unfold gmAffineMiddleZ₂Finite gmAffineMiddleZ₂
  rw [tsum_eq_sum (s := gmAffineMiddleFrequencySupport T M₂)]
  intro ell hell
  rw [gmCubicLocalBump_middleFrequency_eq_zero_of_not_mem hT hM₂ hell]
  simp

/- Guth--Maynard's complete middle-frequency quantity `Σ_II`, written as
the source integer lattice sum rather than a preselected finite window. -/
noncomputable def gmAffineSigmaII
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ) : ℂ :=
  ∑' ell : ℤ,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
        ((‖gmAffineMiddleFourierBlock f M₁ M₂ ell tau‖ ^ 2 : ℝ) : ℂ)

theorem gmAffineSigmaII_eq_finiteSupport
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) :
    gmAffineSigmaII f T M₁ M₂ =
      gmAffineSigmaIIFinite (gmAffineMiddleFrequencySupport T M₂)
        f T M₁ M₂ := by
  unfold gmAffineSigmaII gmAffineSigmaIIFinite
  rw [tsum_eq_sum (s := gmAffineMiddleFrequencySupport T M₂)]
  intro ell hell
  rw [gmCubicLocalBump_middleFrequency_eq_zero_of_not_mem hT hM₂ hell]
  simp

/- The complete, source-faithful right side of equation (9.7). -/
noncomputable def gmAffineSigmaIIEquation97
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ) : ℂ :=
  ∫ q : ℝ × ℝ,
    ∑ m₂' ∈ gmAffinePositiveShell M₂,
      ∑ m₂ ∈ gmAffinePositiveShell M₂,
        (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
          gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
          gmAffineMiddleZ₂ T M₂ m₂ m₂' q.2 q.1

/- Exact Guth--Maynard equation (9.7) for the complete integer-frequency
sum.  Compact support, both Fubini steps, and both shell sums are proved in
the theorem chain above. -/
theorem gmAffineSigmaII_eq_equation97
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) :
    gmAffineSigmaII f T M₁ M₂ =
      gmAffineSigmaIIEquation97 f T M₁ M₂ := by
  rw [gmAffineSigmaII_eq_finiteSupport hT hM₂,
    gmAffineSigmaIIFinite_eq_equation97]
  unfold gmAffineSigmaIIEquation97Finite gmAffineSigmaIIEquation97
  apply integral_congr_ae
  filter_upwards with q
  apply Finset.sum_congr rfl
  intro m₂' hm₂'
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  rw [gmAffineMiddleZ₂Finite_support_eq_Z₂ hT hM₂]

/- Zeroth-order uniform bound for one second-Poisson kernel value. -/
theorem norm_gmAffineScaledBumpDual_le
    {S : ℝ} (hS : 0 < S) (y : ℝ) :
    ‖gmAffineScaledBumpDual S hS y‖ ≤
      S * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual := by
  simpa using gmAffineScaledBumpDual_polynomial_decay 0 hS y

/- The affine center associated with the Poisson integer `j`.  The sign
is chosen so that replacing `j` by `-j` gives the source affine shift. -/
noncomputable def gmAffineMiddleCenter (m₂ m₂' j : ℤ) (u : ℝ) : ℝ :=
  ((m₂ : ℝ) * u - (j : ℝ)) / (m₂' : ℝ)

/- Membership in the retained second-Poisson window forces `u'` into the
physical interval of radius `Q/T` about the corresponding affine center. -/
theorem mem_gmAffineUnitInterval_div_of_mem_scaledNear
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {m₂ m₂' j : ℤ}
    (hm₂' : m₂' ∈ gmAffinePositiveShell M₂) {u u' : ℝ}
    (hj : j ∈ gmAffineScaledNearSet (T / M₂)
      (-gmAffineMiddleDisplacement m₂ m₂' u u') Q) :
    u' ∈ gmAffineUnitInterval (T / Q)
      (gmAffineMiddleCenter m₂ m₂' j u) := by
  have hnear := (Finset.mem_filter.mp hj).2
  have hm₂'Bounds := mem_gmAffinePositiveShell.mp hm₂'
  have hM₂Int : (0 : ℤ) < (M₂ : ℤ) := by exact_mod_cast hM₂
  have hm₂'PosInt : (0 : ℤ) < m₂' :=
    lt_of_lt_of_le hM₂Int hm₂'Bounds.1
  have hm₂'Pos : (0 : ℝ) < m₂' := by
    exact_mod_cast hm₂'PosInt
  have hS : 0 < T / (M₂ : ℝ) := by positivity
  have hM₂real : (0 : ℝ) < M₂ := by positivity
  have hraw :
      |u' - gmAffineMiddleCenter m₂ m₂' j u| < Q / T := by
    have hfactor :
        (T / (M₂ : ℝ)) *
            ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u') =
          ((T * (m₂' : ℝ)) / (M₂ : ℝ)) *
            (u' - gmAffineMiddleCenter m₂ m₂' j u) := by
      unfold gmAffineMiddleDisplacement gmAffineMiddleCenter
      field_simp [show (m₂' : ℝ) ≠ 0 by positivity,
        show (M₂ : ℝ) ≠ 0 by positivity]
      ring
    rw [show -gmAffineMiddleDisplacement m₂ m₂' u u' + (j : ℝ) =
        (j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u' by ring,
      hfactor, abs_mul, abs_of_pos (by positivity :
      (0 : ℝ) < (T * (m₂' : ℝ)) / (M₂ : ℝ))] at hnear
    have hscale : T ≤ (T * (m₂' : ℝ)) / (M₂ : ℝ) := by
      rw [le_div_iff₀ hM₂real]
      nlinarith [show (M₂ : ℝ) ≤ m₂' by exact_mod_cast hm₂'Bounds.1]
    have hTmul : T * |u' - gmAffineMiddleCenter m₂ m₂' j u| < Q :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hscale (abs_nonneg _)) hnear
    exact (lt_div_iff₀ hT).mpr (by simpa [mul_comm] using hTmul)
  rw [gmAffineUnitInterval, Set.mem_Icc]
  have hHQ : 0 < T / Q := by positivity
  have hradius : 1 / (T / Q) = Q / T := by field_simp
  rw [hradius]
  rw [abs_lt] at hraw
  constructor <;> linarith

/- On the fixed iteration support and for `Q ≤ T`, every retained Poisson integer
maps (after the sign change in (9.5)) into the actual finite affine-shift
shell used by `J`. -/
theorem neg_mem_gmAffineCentralShell_of_mem_scaledNear
    {T Q : ℝ} (hT : 0 < T) (hQT : Q ≤ T)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {m₂ m₂' j : ℤ}
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂)
    (hm₂' : m₂' ∈ gmAffinePositiveShell M₂)
    {u u' : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 3)
    (hu' : u' ∈ Set.Icc (0 : ℝ) 3)
    (hj : j ∈ gmAffineScaledNearSet (T / M₂)
      (-gmAffineMiddleDisplacement m₂ m₂' u u') Q) :
    -j ∈ gmAffineCentralShell M₂ := by
  have hm₂Bounds := mem_gmAffinePositiveShell.mp hm₂
  have hm₂'Bounds := mem_gmAffinePositiveShell.mp hm₂'
  have hM₂real : (0 : ℝ) < M₂ := by positivity
  have hm₂Lower : (M₂ : ℝ) ≤ m₂ := by exact_mod_cast hm₂Bounds.1
  have hm₂Upper : (m₂ : ℝ) ≤ 2 * M₂ := by exact_mod_cast hm₂Bounds.2
  have hm₂'Lower : (M₂ : ℝ) ≤ m₂' := by exact_mod_cast hm₂'Bounds.1
  have hm₂'Upper : (m₂' : ℝ) ≤ 2 * M₂ := by exact_mod_cast hm₂'Bounds.2
  have hm₂Nonneg : (0 : ℝ) ≤ m₂ := hM₂real.le.trans hm₂Lower
  have hm₂'Nonneg : (0 : ℝ) ≤ m₂' := hM₂real.le.trans hm₂'Lower
  have hmuLower : (0 : ℝ) ≤ (m₂ : ℝ) * u :=
    mul_nonneg hm₂Nonneg hu.1
  have hmuUpper : (m₂ : ℝ) * u ≤ 6 * M₂ := by
    calc
      (m₂ : ℝ) * u ≤ (2 * M₂ : ℝ) * 3 :=
        mul_le_mul hm₂Upper hu.2 (by linarith [hu.1]) (by positivity)
      _ = 6 * M₂ := by ring
  have hm'u'Lower : (0 : ℝ) ≤ (m₂' : ℝ) * u' :=
    mul_nonneg hm₂'Nonneg hu'.1
  have hm'u'Upper : (m₂' : ℝ) * u' ≤ 6 * M₂ := by
    calc
      (m₂' : ℝ) * u' ≤ (2 * M₂ : ℝ) * 3 :=
        mul_le_mul hm₂'Upper hu'.2 (by linarith [hu'.1]) (by positivity)
      _ = 6 * M₂ := by ring
  have hnear := (Finset.mem_filter.mp hj).2
  have hS : 0 < T / (M₂ : ℝ) := by positivity
  rw [abs_mul, abs_of_pos hS] at hnear
  have herrScaled : (T / (M₂ : ℝ)) *
      |(j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u'| < T := by
    simpa [sub_eq_add_neg, add_comm] using hnear.trans_le hQT
  have herr :
      |(j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u'| < M₂ := by
    have hmul : T *
        |(j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u'| <
          T * M₂ := by
      apply (div_lt_iff₀ hM₂real).mp
      simpa [div_mul_eq_mul_div] using herrScaled
    nlinarith
  rw [abs_lt] at herr
  unfold gmAffineMiddleDisplacement at herr
  have hjLower : (-(8 * M₂ : ℝ)) ≤ -(j : ℝ) := by
    linarith
  have hjUpper : -(j : ℝ) ≤ (8 * M₂ : ℝ) := by
    linarith
  rw [mem_gmAffineCentralShell]
  constructor
  · have hcast : ((-(8 * (M₂ : ℤ)) : ℤ) : ℝ) ≤ ((-j : ℤ) : ℝ) := by
      push_cast
      simpa using hjLower
    exact_mod_cast hcast
  · have hcast : ((-j : ℤ) : ℝ) ≤ (((8 * M₂ : ℕ) : ℤ) : ℝ) := by
      push_cast
      simpa using hjUpper
    exact_mod_cast hcast

/- The absolute retained second-Poisson weight for one shell pair. -/
noncomputable def gmAffineMiddleNearKernelNormSum
    (T : ℝ) (hT : 0 < T) (M₂ : ℕ) (hM₂ : 0 < M₂)
    (Q : ℝ) (m₂ m₂' : ℤ) (u u' : ℝ) : ℝ :=
  ∑ j ∈ gmAffineScaledNearSet (T / M₂)
      (-gmAffineMiddleDisplacement m₂ m₂' u u') Q,
    ‖gmAffineScaledBumpDual (T / M₂) (by positivity)
      ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u')‖

/- Fixed-central-shell physical majorant for the retained dual modes. -/
noncomputable def gmAffineMiddlePhysicalWindowWeight
    (T Q : ℝ) (M₂ : ℕ) (m₂ m₂' : ℤ) (u u' : ℝ) : ℝ :=
  ∑ k ∈ gmAffineCentralShell M₂,
    Set.indicator
      (gmAffineUnitInterval (T / Q)
        (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
      (fun _ => (T / M₂) *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) u'

/- The dynamically selected near-frequency sum injects into the fixed
central affine shell, with each kernel bounded by its zeroth Schwartz
seminorm. -/
theorem gmAffineMiddleNearKernelNormSum_le_physical
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hQT : Q ≤ T)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {m₂ m₂' : ℤ}
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂)
    (hm₂' : m₂' ∈ gmAffinePositiveShell M₂)
    {u u' : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 3)
    (hu' : u' ∈ Set.Icc (0 : ℝ) 3) :
    gmAffineMiddleNearKernelNormSum T hT M₂ hM₂ Q m₂ m₂' u u' ≤
      gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u' := by
  let A := gmAffineScaledNearSet (T / M₂)
    (-gmAffineMiddleDisplacement m₂ m₂' u u') Q
  let B := A.image fun j : ℤ => -j
  let C : ℝ :=
    (T / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual
  have hS : 0 < T / (M₂ : ℝ) := by positivity
  have hAB : B ⊆ gmAffineCentralShell M₂ := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact neg_mem_gmAffineCentralShell_of_mem_scaledNear
      hT hQT hM₂ hm₂ hm₂' hu hu' hj
  have hNearInterval : ∀ j ∈ A,
      u' ∈ gmAffineUnitInterval (T / Q)
        (((m₂ : ℝ) * u + ((-j : ℤ) : ℝ)) / (m₂' : ℝ)) := by
    intro j hj
    have hmem := mem_gmAffineUnitInterval_div_of_mem_scaledNear
      hT hQ hM₂ hm₂' hj
    simpa only [gmAffineMiddleCenter, Int.cast_neg, sub_eq_add_neg] using hmem
  have hkernel : ∀ j ∈ A,
      ‖gmAffineScaledBumpDual (T / M₂) hS
          ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u')‖ ≤ C := by
    intro j hj
    exact norm_gmAffineScaledBumpDual_le hS _
  calc
    gmAffineMiddleNearKernelNormSum T hT M₂ hM₂ Q m₂ m₂' u u' ≤
        ∑ j ∈ A, C := by
      unfold gmAffineMiddleNearKernelNormSum
      dsimp only [A, C]
      apply Finset.sum_le_sum
      assumption
    _ = ∑ k ∈ B, C := by
      apply Finset.sum_bij (fun j _ => -j)
      · intro j hj
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · intro j₁ hj₁ j₂ hj₂ hEq
        omega
      · intro k hk
        obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
        exact ⟨j, hj, hjk⟩
      · intro j hj
        rfl
    _ = ∑ k ∈ B,
        Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u' := by
      apply Finset.sum_congr rfl
      intro k hkB
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hkB
      subst k
      rw [Set.indicator_of_mem (hNearInterval j hj)]
    _ ≤ ∑ k ∈ gmAffineCentralShell M₂,
        Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u' := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hAB
      intro k hkC hkB
      by_cases hk : u' ∈ gmAffineUnitInterval (T / Q)
          (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ))
      · rw [Set.indicator_of_mem hk]
        positivity
      · rw [Set.indicator_of_notMem hk]
    _ = gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u' := by
      rfl

/- Exact conversion of one physical-window indicator into the normalized
`T/Q` neighborhood integral used by the source smoother. -/
theorem integral_mul_middleWindowIndicator
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ) (C x : ℝ) :
    (∫ u' : ℝ, f u' *
        Set.indicator (gmAffineUnitInterval (T / Q) x) (fun _ => C) u') =
      (C / (T / Q)) *
        ∫ u' in gmAffineUnitInterval (T / Q) x, (T / Q) * f u' := by
  have hH : 0 < T / Q := by positivity
  calc
    (∫ u' : ℝ, f u' *
        Set.indicator (gmAffineUnitInterval (T / Q) x) (fun _ => C) u') =
      ∫ u' : ℝ, Set.indicator (gmAffineUnitInterval (T / Q) x)
        (fun y => C * f y) u' := by
          apply integral_congr_ae
          filter_upwards with u'
          by_cases hu' : u' ∈ gmAffineUnitInterval (T / Q) x
          · rw [Set.indicator_of_mem hu', Set.indicator_of_mem hu']
            ring
          · rw [Set.indicator_of_notMem hu', Set.indicator_of_notMem hu']
            ring
    _ = ∫ u' in gmAffineUnitInterval (T / Q) x, C * f u' := by
      unfold gmAffineUnitInterval
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = C * ∫ u' in gmAffineUnitInterval (T / Q) x, f u' := by
      rw [integral_const_mul]
    _ = (C / (T / Q)) *
        ∫ u' in gmAffineUnitInterval (T / Q) x, (T / Q) * f u' := by
      rw [integral_const_mul]
      field_simp [hH.ne']

/- Integrating the fixed-shell physical weight is exactly a scalar
multiple of the retained affine-neighborhood sum for one `(m₂,m₂')`. -/
theorem integral_mul_gmAffineMiddlePhysicalWindowWeight
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (m₂ m₂' : ℤ) (u : ℝ) :
    (∫ u' : ℝ, f u' *
        gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u') =
      (Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual *
        ∑ k ∈ gmAffineCentralShell M₂,
          ∫ u' in gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)),
              (T / Q) * f u' := by
  let C : ℝ :=
    (T / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual
  have hterm : ∀ k ∈ gmAffineCentralShell M₂,
      Integrable (fun u' : ℝ => f u' *
        Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u') := by
    intro k hk
    apply (f.integrable.norm.const_mul |C|).mono'
    · apply AEStronglyMeasurable.mul f.continuous.aestronglyMeasurable
      exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
    · filter_upwards with u'
      by_cases hu' : u' ∈ gmAffineUnitInterval (T / Q)
          (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ))
      · rw [Set.indicator_of_mem hu']
        simp only [Real.norm_eq_abs, abs_mul]
        ring_nf
        exact le_rfl
      · rw [Set.indicator_of_notMem hu']
        simpa only [norm_mul, norm_zero, mul_zero, Real.norm_eq_abs] using
          mul_nonneg (abs_nonneg C) (abs_nonneg (f u'))
  unfold gmAffineMiddlePhysicalWindowWeight
  change (∫ u' : ℝ, f u' *
      ∑ k ∈ gmAffineCentralShell M₂,
        Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u') = _
  calc
    (∫ u' : ℝ, f u' *
        ∑ k ∈ gmAffineCentralShell M₂,
          Set.indicator
            (gmAffineUnitInterval (T / Q)
              (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
            (fun _ => C) u') =
      ∫ u' : ℝ,
        ∑ k ∈ gmAffineCentralShell M₂,
          f u' * Set.indicator
            (gmAffineUnitInterval (T / Q)
              (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
            (fun _ => C) u' := by
          apply integral_congr_ae
          filter_upwards with u'
          simp only [Finset.mul_sum]
    _ = ∑ k ∈ gmAffineCentralShell M₂,
        ∫ u' : ℝ, f u' * Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u' :=
      MeasureTheory.integral_finsetSum _ hterm
    _ = ∑ k ∈ gmAffineCentralShell M₂,
        (Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual *
          ∫ u' in gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)),
              (T / Q) * f u' := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_mul_middleWindowIndicator hT hQ]
      dsimp only [C]
      congr 1
      field_simp [hT.ne', hQ.ne', show (M₂ : ℝ) ≠ 0 by positivity]
    _ = _ := by
      rw [Finset.mul_sum]

/- Integrability counterpart of
`integral_mul_gmAffineMiddlePhysicalWindowWeight`. -/
theorem integrable_mul_gmAffineMiddlePhysicalWindowWeight
    {T Q : ℝ} (f : SchwartzMap ℝ ℝ) {M₂ : ℕ}
    (m₂ m₂' : ℤ) (u : ℝ) :
    Integrable (fun u' : ℝ => f u' *
      gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u') := by
  let C : ℝ :=
    (T / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual
  have hterm : ∀ k ∈ gmAffineCentralShell M₂,
      Integrable (fun u' : ℝ => f u' *
        Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u') := by
    intro k hk
    apply (f.integrable.norm.const_mul |C|).mono'
    · apply AEStronglyMeasurable.mul f.continuous.aestronglyMeasurable
      exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
    · filter_upwards with u'
      by_cases hu' : u' ∈ gmAffineUnitInterval (T / Q)
          (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ))
      · rw [Set.indicator_of_mem hu']
        simp only [Real.norm_eq_abs, abs_mul]
        ring_nf
        exact le_rfl
      · rw [Set.indicator_of_notMem hu']
        simpa only [norm_mul, norm_zero, mul_zero, Real.norm_eq_abs] using
          mul_nonneg (abs_nonneg C) (abs_nonneg (f u'))
  unfold gmAffineMiddlePhysicalWindowWeight
  rw [show (fun u' : ℝ => f u' *
      ∑ k ∈ gmAffineCentralShell M₂,
        Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u') =
      (fun u' : ℝ => ∑ k ∈ gmAffineCentralShell M₂,
        f u' * Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) u') by
    funext u'
    rw [Finset.mul_sum]]
  exact integrable_finsetSum _ hterm

/- Nonnegative envelope for the retained part of the exact `Z₂` split. -/
noncomputable def gmAffineSigmaIINearEnvelope
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (Q : ℝ)
    (M₂ : ℕ) (hM₂ : 0 < M₂) (q : ℝ × ℝ) : ℝ :=
  ∑ m₂' ∈ gmAffinePositiveShell M₂,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * |f q.1| * |f q.2| * 4 *
        gmAffineMiddleNearKernelNormSum
          T hT M₂ hM₂ Q m₂ m₂' q.2 q.1

/- Fixed-shell physical majorant for the near part, with the exact
`16 M₂²` coefficient coming from `|m₂m₂'|` and `|Z₁| ≤ 4`. -/
noncomputable def gmAffineSigmaIIPhysicalEnvelope
    (f : ℝ → ℝ) (T Q : ℝ) (M₂ : ℕ) (q : ℝ × ℝ) : ℝ :=
  ∑ m₂' ∈ gmAffinePositiveShell M₂,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      16 * (M₂ : ℝ) ^ 2 * f q.1 * f q.2 *
        gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' q.2 q.1

theorem gmAffineSigmaIINearEnvelope_le_physical
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hQT : Q ≤ T)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f)
    {M₂ : ℕ} (hM₂ : 0 < M₂) (q : ℝ × ℝ) :
    gmAffineSigmaIINearEnvelope f T hT Q M₂ hM₂ q ≤
      gmAffineSigmaIIPhysicalEnvelope f T Q M₂ q := by
  by_cases hq₁ : q.1 ∈ Set.Icc (0 : ℝ) 3
  · by_cases hq₂ : q.2 ∈ Set.Icc (0 : ℝ) 3
    · unfold gmAffineSigmaIINearEnvelope gmAffineSigmaIIPhysicalEnvelope
      apply Finset.sum_le_sum
      intro m₂' hm₂'
      apply Finset.sum_le_sum
      intro m₂ hm₂
      have hm₂Bounds := mem_gmAffinePositiveShell.mp hm₂
      have hm₂'Bounds := mem_gmAffinePositiveShell.mp hm₂'
      have hm₂Nonneg : (0 : ℝ) ≤ m₂ := by
        exact_mod_cast (show (0 : ℤ) ≤ m₂ by omega)
      have hm₂'Nonneg : (0 : ℝ) ≤ m₂' := by
        exact_mod_cast (show (0 : ℤ) ≤ m₂' by omega)
      have hm₂Upper : (m₂ : ℝ) ≤ 2 * M₂ := by exact_mod_cast hm₂Bounds.2
      have hm₂'Upper : (m₂' : ℝ) ≤ 2 * M₂ := by exact_mod_cast hm₂'Bounds.2
      have hcoeff : ‖(((m₂' * m₂ : ℤ) : ℂ))‖ ≤ 4 * (M₂ : ℝ) ^ 2 := by
        rw [Complex.norm_intCast, Int.cast_mul, abs_mul,
          abs_of_nonneg hm₂Nonneg, abs_of_nonneg hm₂'Nonneg]
        nlinarith [mul_le_mul hm₂'Upper hm₂Upper hm₂Nonneg
          (by positivity : (0 : ℝ) ≤ 2 * M₂)]
      have hnear := gmAffineMiddleNearKernelNormSum_le_physical
        hT hQ hQT hM₂ hm₂ hm₂' hq₂ hq₁
      have hf₁ : 0 ≤ f q.1 := hf q.1
      have hf₂ : 0 ≤ f q.2 := hf q.2
      have hNearNonneg :
          0 ≤ gmAffineMiddleNearKernelNormSum
            T hT M₂ hM₂ Q m₂ m₂' q.2 q.1 := by
        unfold gmAffineMiddleNearKernelNormSum
        positivity
      rw [abs_of_nonneg (hf q.1), abs_of_nonneg (hf q.2)]
      change ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * f q.1 * f q.2 * 4 *
          gmAffineMiddleNearKernelNormSum
            T hT M₂ hM₂ Q m₂ m₂' q.2 q.1 ≤
        16 * (M₂ : ℝ) ^ 2 * f q.1 * f q.2 *
          gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' q.2 q.1
      calc
        ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * f q.1 * f q.2 * 4 *
            gmAffineMiddleNearKernelNormSum
              T hT M₂ hM₂ Q m₂ m₂' q.2 q.1 =
          ‖(((m₂' * m₂ : ℤ) : ℂ))‖ *
            (f q.1 * f q.2 * 4 *
              gmAffineMiddleNearKernelNormSum
                T hT M₂ hM₂ Q m₂ m₂' q.2 q.1) := by ring
        _ ≤ (4 * (M₂ : ℝ) ^ 2) *
            (f q.1 * f q.2 * 4 *
              gmAffineMiddleNearKernelNormSum
                T hT M₂ hM₂ Q m₂ m₂' q.2 q.1) := by
          exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ = ((4 * (M₂ : ℝ) ^ 2) * f q.1 * f q.2 * 4) *
            gmAffineMiddleNearKernelNormSum
              T hT M₂ hM₂ Q m₂ m₂' q.2 q.1 := by ring
        _ ≤ ((4 * (M₂ : ℝ) ^ 2) * f q.1 * f q.2 * 4) *
            gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' q.2 q.1 := by
          exact mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = 16 * (M₂ : ℝ) ^ 2 * f q.1 * f q.2 *
            gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' q.2 q.1 := by ring
    · have hz : f q.2 = 0 := hsupp q.2 hq₂
      simp [gmAffineSigmaIINearEnvelope, gmAffineSigmaIIPhysicalEnvelope, hz]
  · have hz : f q.1 = 0 := hsupp q.1 hq₁
    simp [gmAffineSigmaIINearEnvelope, gmAffineSigmaIIPhysicalEnvelope, hz]

/- The fixed-shell physical envelope is integrable on the `(u',u)` plane.
This is the analytic domination needed before applying Fubini to (9.8). -/
theorem integrable_gmAffineSigmaIIPhysicalEnvelope
    {T Q : ℝ} (f : SchwartzMap ℝ ℝ) (M₂ : ℕ) :
    Integrable (gmAffineSigmaIIPhysicalEnvelope f T Q M₂) := by
  have hbase : Integrable (fun q : ℝ × ℝ => f q.1 * f q.2) :=
    f.integrable.mul_prod f.integrable
  unfold gmAffineSigmaIIPhysicalEnvelope gmAffineMiddlePhysicalWindowWeight
  apply integrable_finsetSum
  intro m₂' hm₂'
  apply integrable_finsetSum
  intro m₂ hm₂
  rw [show (fun q : ℝ × ℝ =>
      16 * (M₂ : ℝ) ^ 2 * f q.1 * f q.2 *
        ∑ k ∈ gmAffineCentralShell M₂,
          Set.indicator
            (gmAffineUnitInterval (T / Q)
              (((m₂ : ℝ) * q.2 + (k : ℝ)) / (m₂' : ℝ)))
            (fun _ => (T / M₂) *
              SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) q.1) =
      (fun q : ℝ × ℝ =>
        ∑ k ∈ gmAffineCentralShell M₂,
          16 * (M₂ : ℝ) ^ 2 * f q.1 * f q.2 *
            Set.indicator
              (gmAffineUnitInterval (T / Q)
                (((m₂ : ℝ) * q.2 + (k : ℝ)) / (m₂' : ℝ)))
              (fun _ => (T / M₂) *
                SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) q.1) by
      funext q
      rw [Finset.mul_sum]]
  apply integrable_finsetSum
  intro k hk
  let C : ℝ := (T / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual
  let S : Set (ℝ × ℝ) := {q | q.1 ∈
    gmAffineUnitInterval (T / Q)
      (((m₂ : ℝ) * q.2 + (k : ℝ)) / (m₂' : ℝ))}
  have hS : MeasurableSet S := by
    dsimp only [S, gmAffineUnitInterval]
    measurability
  have hind : AEStronglyMeasurable (fun q : ℝ × ℝ =>
      Set.indicator S (fun _ => C) q) :=
    (measurable_const.indicator hS).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ =>
      16 * (M₂ : ℝ) ^ 2 * f q.1 * f q.2 *
        Set.indicator
          (gmAffineUnitInterval (T / Q)
            (((m₂ : ℝ) * q.2 + (k : ℝ)) / (m₂' : ℝ)))
          (fun _ => C) q.1) := by
    have hprod : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        16 * (M₂ : ℝ) ^ 2 * (f q.1 * f q.2) *
          Set.indicator S (fun _ => C) q) :=
      ((hbase.aestronglyMeasurable.const_mul
        (16 * (M₂ : ℝ) ^ 2)).mul hind)
    apply hprod.congr
    filter_upwards with q
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      rw [Set.indicator_of_mem]
      · ring
      · exact hq
    · rw [Set.indicator_of_notMem hq]
      rw [Set.indicator_of_notMem]
      · ring
      · exact hq
  refine (hbase.norm.const_mul
      |16 * (M₂ : ℝ) ^ 2 * C|).mono' hmeas ?_
  filter_upwards with q
  by_cases hq : q ∈ S
  · have hq' : q.1 ∈ gmAffineUnitInterval (T / Q)
        (((m₂ : ℝ) * q.2 + (k : ℝ)) / (m₂' : ℝ)) := hq
    rw [Set.indicator_of_mem hq']
    simp only [Real.norm_eq_abs, abs_mul]
    dsimp only [C]
    rw [abs_mul]
    ring_nf
    rfl
  · have hq' : q.1 ∉ gmAffineUnitInterval (T / Q)
        (((m₂ : ℝ) * q.2 + (k : ℝ)) / (m₂' : ℝ)) := hq
    rw [Set.indicator_of_notMem hq']
    simp only [mul_zero, norm_zero, Real.norm_eq_abs]
    positivity

/- Exact integrated form of the physical majorant.  This is equation (9.8)
before the final Cauchy--Schwarz estimate against `J`. -/
theorem integral_gmAffineSigmaIIPhysicalEnvelope_eq
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ) {M₂ : ℕ} (hM₂ : 0 < M₂) :
    (∫ q : ℝ × ℝ, gmAffineSigmaIIPhysicalEnvelope f T Q M₂ q) =
      16 * (M₂ : ℝ) ^ 2 *
        ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
          ∫ u : ℝ, f u *
            gmAffineRetainedNeighborhoodSum f (T / Q) M₂ u := by
  have hEnvelopeInt := integrable_gmAffineSigmaIIPhysicalEnvelope
    (T := T) (Q := Q) f M₂
  have hinner : ∀ u : ℝ,
      (∫ u' : ℝ, gmAffineSigmaIIPhysicalEnvelope f T Q M₂ (u', u)) =
        16 * (M₂ : ℝ) ^ 2 *
          ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
            (f u * gmAffineRetainedNeighborhoodSum f (T / Q) M₂ u) := by
    intro u
    have hpairInt : ∀ m₂' ∈ gmAffinePositiveShell M₂,
        ∀ m₂ ∈ gmAffinePositiveShell M₂,
        Integrable (fun u' : ℝ =>
          16 * (M₂ : ℝ) ^ 2 * f u' * f u *
            gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u') := by
      intro m₂' hm₂' m₂ hm₂
      have hbase := integrable_mul_gmAffineMiddlePhysicalWindowWeight
        (T := T) (Q := Q) (M₂ := M₂) f m₂ m₂' u
      have hscaled := hbase.const_mul (16 * (M₂ : ℝ) ^ 2 * f u)
      apply hscaled.congr
      filter_upwards with u'
      ring
    have hpairEq : ∀ m₂' ∈ gmAffinePositiveShell M₂,
        ∀ m₂ ∈ gmAffinePositiveShell M₂,
        (∫ u' : ℝ,
          16 * (M₂ : ℝ) ^ 2 * f u' * f u *
            gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u') =
          (16 * (M₂ : ℝ) ^ 2 * f u) *
            ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual *
              ∑ k ∈ gmAffineCentralShell M₂,
                ∫ u' in gmAffineUnitInterval (T / Q)
                  (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)),
                    (T / Q) * f u') := by
      intro m₂' hm₂' m₂ hm₂
      calc
        (∫ u' : ℝ,
            16 * (M₂ : ℝ) ^ 2 * f u' * f u *
              gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u') =
          ∫ u' : ℝ, (16 * (M₂ : ℝ) ^ 2 * f u) *
            (f u' * gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u') := by
              apply integral_congr_ae
              filter_upwards with u'
              ring
        _ = (16 * (M₂ : ℝ) ^ 2 * f u) *
            ∫ u' : ℝ, f u' *
              gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u' := by
          rw [integral_const_mul]
        _ = _ := by
          rw [integral_mul_gmAffineMiddlePhysicalWindowWeight hT hQ f hM₂]
    unfold gmAffineSigmaIIPhysicalEnvelope
    calc
      (∫ u' : ℝ,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              16 * (M₂ : ℝ) ^ 2 * f u' * f u *
                gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u') =
        ∑ m₂' ∈ gmAffinePositiveShell M₂,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            ∫ u' : ℝ,
              16 * (M₂ : ℝ) ^ 2 * f u' * f u *
                gmAffineMiddlePhysicalWindowWeight T Q M₂ m₂ m₂' u u' := by
          rw [MeasureTheory.integral_finsetSum _ (fun m₂' hm₂' =>
            integrable_finsetSum _ (hpairInt m₂' hm₂'))]
          apply Finset.sum_congr rfl
          intro m₂' hm₂'
          rw [MeasureTheory.integral_finsetSum _ (hpairInt m₂' hm₂')]
      _ = ∑ m₂' ∈ gmAffinePositiveShell M₂,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            (16 * (M₂ : ℝ) ^ 2 * f u) *
              ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual *
                ∑ k ∈ gmAffineCentralShell M₂,
                  ∫ u' in gmAffineUnitInterval (T / Q)
                    (((m₂ : ℝ) * u + (k : ℝ)) / (m₂' : ℝ)),
                      (T / Q) * f u') := by
          apply Finset.sum_congr rfl
          intro m₂' hm₂'
          apply Finset.sum_congr rfl
          intro m₂ hm₂
          exact hpairEq m₂' hm₂' m₂ hm₂
      _ = 16 * (M₂ : ℝ) ^ 2 *
          ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
            (f u * gmAffineRetainedNeighborhoodSum f (T / Q) M₂ u) := by
        unfold gmAffineRetainedNeighborhoodSum
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        ring
  calc
    (∫ q : ℝ × ℝ, gmAffineSigmaIIPhysicalEnvelope f T Q M₂ q) =
        ∫ u : ℝ, ∫ u' : ℝ,
          gmAffineSigmaIIPhysicalEnvelope f T Q M₂ (u', u) :=
      MeasureTheory.integral_prod_symm _ hEnvelopeInt
    _ = ∫ u : ℝ,
        16 * (M₂ : ℝ) ^ 2 *
          ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
            (f u * gmAffineRetainedNeighborhoodSum f (T / Q) M₂ u) := by
      apply integral_congr_ae
      filter_upwards with u
      exact hinner u
    _ = _ := by
      rw [integral_const_mul]

/- The retained physical contribution in (9.8), bounded by the square
root of the affine energy at smoothing scale `T/Q`. -/
theorem integral_gmAffineSigmaIIPhysicalEnvelope_le
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M₂ : ℕ} (hM₂ : 0 < M₂) :
    (∫ q : ℝ × ℝ, gmAffineSigmaIIPhysicalEnvelope f T Q M₂ q) ≤
      16 * (M₂ : ℝ) ^ 2 *
        ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz (T / Q) (by positivity) f) M₂)) := by
  rw [integral_gmAffineSigmaIIPhysicalEnvelope_eq hT hQ f hM₂]
  apply mul_le_mul_of_nonneg_left
  · exact integral_mul_gmAffineRetainedNeighborhoodSum_le
      (show 0 < T / Q by positivity) f hf hM₂
  · positivity

/- The complete source-facing integrand on the right side of (9.7). -/
noncomputable def gmAffineSigmaIIEquation97Integrand
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ) (q : ℝ × ℝ) : ℂ :=
  ∑ m₂' ∈ gmAffinePositiveShell M₂,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
        gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
        gmAffineMiddleZ₂ T M₂ m₂ m₂' q.2 q.1

theorem gmAffineSigmaIIEquation97_eq_integral_integrand
    (f : SchwartzMap ℝ ℝ) (T M₁ : ℝ) (M₂ : ℕ) :
    gmAffineSigmaIIEquation97 f T M₁ M₂ =
      ∫ q : ℝ × ℝ, gmAffineSigmaIIEquation97Integrand f T M₁ M₂ q := by
  rfl

/- Uniform omitted-frequency constant after the second Poisson split. -/
noncomputable def gmAffineMiddleFarBound
    (n : ℕ) (T Q : ℝ) (M₂ : ℕ) : ℝ :=
  (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
      ((T / M₂) * Q ^ n)) *
      (∑' k : ℤ, gmIntDecayProfile 2 k) +
    2 * ((T / M₂) *
      SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ (n + 2))

/- Nonnegative envelope for the complete omitted integer-frequency series. -/
noncomputable def gmAffineSigmaIIFarEnvelope
    (n : ℕ) (f : ℝ → ℝ) (T Q : ℝ) (M₂ : ℕ) (q : ℝ × ℝ) : ℝ :=
  ∑ m₂' ∈ gmAffinePositiveShell M₂,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * |f q.1| * |f q.2| * 4 *
        gmAffineMiddleFarBound n T Q M₂

theorem gmAffineMiddleFarBound_nonneg
    (n : ℕ) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) :
    0 ≤ gmAffineMiddleFarBound n T Q M₂ := by
  unfold gmAffineMiddleFarBound
  have hsum : 0 ≤ (∑' k : ℤ, gmIntDecayProfile 2 k) :=
    tsum_nonneg fun k => by
      unfold gmIntDecayProfile
      positivity
  positivity

/- Pointwise near/far domination of the complete equation-(9.7)
integrand.  Both Poisson pieces are the exact pieces of the source sum. -/
theorem norm_gmAffineSigmaIIEquation97Integrand_le_near_add_far
    (n : ℕ) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) (q : ℝ × ℝ) :
    ‖gmAffineSigmaIIEquation97Integrand f T M₁ M₂ q‖ ≤
      gmAffineSigmaIINearEnvelope f T hT Q M₂ hM₂ q +
        gmAffineSigmaIIFarEnvelope n f T Q M₂ q := by
  unfold gmAffineSigmaIIEquation97Integrand
    gmAffineSigmaIINearEnvelope gmAffineSigmaIIFarEnvelope
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m₂' hm₂'
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m₂ hm₂
  rw [gmAffineMiddleZ₂_eq_near_add_far n hT hM₂ hQ]
  let A : ℂ :=
    (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
      gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1
  let N : ℂ :=
    ∑ j ∈ gmAffineScaledNearSet (T / M₂)
        (-gmAffineMiddleDisplacement m₂ m₂' q.2 q.1) Q,
      gmAffineScaledBumpDual (T / M₂) (by positivity)
        ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' q.2 q.1)
  let F : ℂ := gmAffineScaledFarSeries (T / M₂) (by positivity)
    (-gmAffineMiddleDisplacement m₂ m₂' q.2 q.1) Q
  have hN : ‖N‖ ≤ gmAffineMiddleNearKernelNormSum
      T hT M₂ hM₂ Q m₂ m₂' q.2 q.1 := by
    dsimp only [N, gmAffineMiddleNearKernelNormSum]
    exact norm_sum_le _ _
  have hF : ‖F‖ ≤ gmAffineMiddleFarBound n T Q M₂ := by
    dsimp only [F]
    exact norm_gmAffineMiddleZ₂_farSeries_le
      n hT hM₂ hQ m₂ m₂' q.2 q.1
  have hZ₁ := norm_gmAffineMiddleZ₁_le_four M₁ m₂ m₂' q.2 q.1
  have hA : ‖A‖ ≤
      ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * |f q.1| * |f q.2| * 4 := by
    dsimp only [A]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  change ‖A * (N + F)‖ ≤
    ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * |f q.1| * |f q.2| * 4 *
        gmAffineMiddleNearKernelNormSum
          T hT M₂ hM₂ Q m₂ m₂' q.2 q.1 +
      ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * |f q.1| * |f q.2| * 4 *
        gmAffineMiddleFarBound n T Q M₂
  calc
    ‖A * (N + F)‖ = ‖A‖ * ‖N + F‖ := norm_mul _ _
    _ ≤ ‖A‖ * (‖N‖ + ‖F‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le N F) (norm_nonneg A)
    _ ≤ (‖(((m₂' * m₂ : ℤ) : ℂ))‖ * |f q.1| * |f q.2| * 4) *
        (gmAffineMiddleNearKernelNormSum
            T hT M₂ hM₂ Q m₂ m₂' q.2 q.1 +
          gmAffineMiddleFarBound n T Q M₂) := by
      gcongr
    _ = _ := by ring

theorem integrable_gmAffineSigmaIIFarEnvelope
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (T Q : ℝ) (M₂ : ℕ) :
    Integrable (gmAffineSigmaIIFarEnvelope n f T Q M₂) := by
  have hbase : Integrable (fun q : ℝ × ℝ => |f q.1| * |f q.2|) :=
    f.integrable.norm.mul_prod f.integrable.norm
  unfold gmAffineSigmaIIFarEnvelope
  apply integrable_finsetSum
  intro m₂' hm₂'
  apply integrable_finsetSum
  intro m₂ hm₂
  have hscaled := hbase.const_mul
    (‖(((m₂' * m₂ : ℤ) : ℂ))‖ * 4 * gmAffineMiddleFarBound n T Q M₂)
  apply hscaled.congr
  filter_upwards with q
  ring

theorem integrable_gmAffineSigmaIIEquation97Integrand
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (M₁ : ℝ) :
    Integrable (gmAffineSigmaIIEquation97Integrand f T M₁ M₂)
      (volume.prod volume) := by
  let L := gmAffineMiddleFrequencySupport T M₂
  have hfinite : Integrable (fun q : ℝ × ℝ =>
      ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∑ ell ∈ L,
            gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q)
      (volume.prod volume) :=
    integrable_finsetSum _ (fun m₂' _ =>
      integrable_finsetSum _ (fun m₂ _ =>
        integrable_finsetSum _ (fun ell _ =>
          integrable_gmAffineMiddleEquation97Term
            f T M₁ M₂ ell m₂ m₂')))
  refine hfinite.congr ?_
  filter_upwards with q
  unfold gmAffineSigmaIIEquation97Integrand
  apply Finset.sum_congr rfl
  intro m₂' hm₂'
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  rw [sum_gmAffineMiddleEquation97Term_eq_Z₂Finite]
  rw [gmAffineMiddleZ₂Finite_support_eq_Z₂ hT hM₂]

/- Absolute equation-(9.7) bound after the exact near/far split. -/
theorem norm_gmAffineSigmaII_le_physical_add_far
    (n : ℕ) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hQT : Q ≤ T)
    {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f) (M₁ : ℝ) :
    ‖gmAffineSigmaII f T M₁ M₂‖ ≤
      (∫ q : ℝ × ℝ, gmAffineSigmaIIPhysicalEnvelope f T Q M₂ q) +
        ∫ q : ℝ × ℝ, gmAffineSigmaIIFarEnvelope n f T Q M₂ q := by
  rw [gmAffineSigmaII_eq_equation97 hT hM₂,
    gmAffineSigmaIIEquation97_eq_integral_integrand]
  have hI := integrable_gmAffineSigmaIIEquation97Integrand hT hM₂ f M₁
  have hP := integrable_gmAffineSigmaIIPhysicalEnvelope
    (T := T) (Q := Q) f M₂
  have hF := integrable_gmAffineSigmaIIFarEnvelope n f T Q M₂
  calc
    ‖∫ q : ℝ × ℝ, gmAffineSigmaIIEquation97Integrand f T M₁ M₂ q‖ ≤
        ∫ q : ℝ × ℝ, ‖gmAffineSigmaIIEquation97Integrand f T M₁ M₂ q‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ q : ℝ × ℝ,
        gmAffineSigmaIIPhysicalEnvelope f T Q M₂ q +
          gmAffineSigmaIIFarEnvelope n f T Q M₂ q := by
      apply integral_mono hI.norm (hP.add hF)
      intro q
      exact (norm_gmAffineSigmaIIEquation97Integrand_le_near_add_far
        n hT hQ hM₂ f M₁ q).trans
          (add_le_add
            (gmAffineSigmaIINearEnvelope_le_physical
              hT hQ hQT f hf hsupp hM₂ q)
            le_rfl)
    _ = _ := integral_add hP hF

/- The `gmAffineSigmaIIFarCoefficient` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineSigmaIIFarCoefficient
    (n : ℕ) (T Q : ℝ) (M₂ : ℕ) : ℝ :=
  ∑ m₂' ∈ gmAffinePositiveShell M₂,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * 4 *
        gmAffineMiddleFarBound n T Q M₂

theorem gmAffineSigmaIIFarEnvelope_eq_coefficient_mul
    (n : ℕ) (f : ℝ → ℝ) (T Q : ℝ) (M₂ : ℕ) (q : ℝ × ℝ) :
    gmAffineSigmaIIFarEnvelope n f T Q M₂ q =
      gmAffineSigmaIIFarCoefficient n T Q M₂ * (|f q.1| * |f q.2|) := by
  unfold gmAffineSigmaIIFarEnvelope gmAffineSigmaIIFarCoefficient
  simp_rw [← Finset.sum_mul]
  ring

theorem integral_gmAffineSigmaIIFarEnvelope_eq
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (T Q : ℝ) (M₂ : ℕ) :
    (∫ q : ℝ × ℝ, gmAffineSigmaIIFarEnvelope n f T Q M₂ q) =
      gmAffineSigmaIIFarCoefficient n T Q M₂ *
        (∫ u : ℝ, |f u|) ^ 2 := by
  have hbase : Integrable (fun q : ℝ × ℝ => |f q.1| * |f q.2|) :=
    f.integrable.norm.mul_prod f.integrable.norm
  calc
    (∫ q : ℝ × ℝ, gmAffineSigmaIIFarEnvelope n f T Q M₂ q) =
        ∫ q : ℝ × ℝ, gmAffineSigmaIIFarCoefficient n T Q M₂ *
          (|f q.1| * |f q.2|) := by
      apply integral_congr_ae
      filter_upwards with q
      exact gmAffineSigmaIIFarEnvelope_eq_coefficient_mul n f T Q M₂ q
    _ = gmAffineSigmaIIFarCoefficient n T Q M₂ *
        ∫ q : ℝ × ℝ, |f q.1| * |f q.2| := by
      rw [integral_const_mul]
    _ = gmAffineSigmaIIFarCoefficient n T Q M₂ *
        ∫ x : ℝ, ∫ y : ℝ, |f x| * |f y| := by
      congr 1
      simpa only [Measure.volume_eq_prod] using (MeasureTheory.integral_prod
        (fun q : ℝ × ℝ => |f q.1| * |f q.2|) hbase)
    _ = _ := by
      simp_rw [integral_const_mul]
      rw [integral_mul_const]
      ring

theorem gmAffineSigmaIIFarCoefficient_le
    (n : ℕ) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) :
    gmAffineSigmaIIFarCoefficient n T Q M₂ ≤
      16 * (M₂ : ℝ) ^ 2 *
        ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
          gmAffineMiddleFarBound n T Q M₂ := by
  have hB := gmAffineMiddleFarBound_nonneg n hT hQ hM₂
  unfold gmAffineSigmaIIFarCoefficient
  calc
    (∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ‖(((m₂' * m₂ : ℤ) : ℂ))‖ * 4 *
            gmAffineMiddleFarBound n T Q M₂) ≤
      ∑ _m₂' ∈ gmAffinePositiveShell M₂,
        ∑ _m₂ ∈ gmAffinePositiveShell M₂,
          (4 * (M₂ : ℝ) ^ 2) * 4 *
            gmAffineMiddleFarBound n T Q M₂ := by
      apply Finset.sum_le_sum
      intro m₂' hm₂'
      apply Finset.sum_le_sum
      intro m₂ hm₂
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Complex.norm_intCast, Int.cast_mul, abs_mul]
      have hm₂Le := abs_gmAffinePositiveShell_le_scale hm₂
      have hm₂'Le := abs_gmAffinePositiveShell_le_scale hm₂'
      nlinarith [mul_le_mul hm₂'Le hm₂Le (abs_nonneg (m₂ : ℝ))
        (by positivity : (0 : ℝ) ≤ 2 * M₂)]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem integral_gmAffineSigmaIIFarEnvelope_le
    (n : ℕ) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ) {M₂ : ℕ} (hM₂ : 0 < M₂) :
    (∫ q : ℝ × ℝ, gmAffineSigmaIIFarEnvelope n f T Q M₂ q) ≤
      16 * (M₂ : ℝ) ^ 2 *
        ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
          gmAffineMiddleFarBound n T Q M₂ *
            (∫ u : ℝ, |f u|) ^ 2 := by
  rw [integral_gmAffineSigmaIIFarEnvelope_eq]
  exact mul_le_mul_of_nonneg_right
    (gmAffineSigmaIIFarCoefficient_le n hT hQ hM₂) (sq_nonneg _)

/- Complete quantitative bound for the exact `Sigma_II` of equation
(9.7), with the retained affine-energy term and the full omitted lattice
shown separately. -/
theorem norm_gmAffineSigmaII_le_J_add_far
    (n : ℕ) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hQT : Q ≤ T)
    {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f) (M₁ : ℝ) :
    ‖gmAffineSigmaII f T M₁ M₂‖ ≤
      16 * (M₂ : ℝ) ^ 2 *
        ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz (T / Q) (by positivity) f) M₂)) +
      16 * (M₂ : ℝ) ^ 2 *
        ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
          gmAffineMiddleFarBound n T Q M₂ *
            (∫ u : ℝ, |f u|) ^ 2 := by
  exact (norm_gmAffineSigmaII_le_physical_add_far
    n hT hQ hQT hM₂ f hf hsupp M₁).trans
      (add_le_add
        (integral_gmAffineSigmaIIPhysicalEnvelope_le hT hQ f hf hM₂)
        (integral_gmAffineSigmaIIFarEnvelope_le n hT hQ f hM₂))

/-! ### Corrected physical-width middle-frequency consumer -/

/- The retained pair square, extended by zero outside its exact
first-Poisson window. -/
noncomputable def gmAffineRetainedFirstPoissonPairSquare
    (f : SchwartzMap ℝ ℝ) (Q : ℝ) (M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (p : ℤ × ℤ) (xi : ℝ) : ℝ :=
  if |gmAffineFirstPoissonTau M₃ p.1 p.2 xi| < Q then
    ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2
  else 0

/- The finite retained-pair square from the first Poisson formula is
exactly the complete integer lattice sum after every omitted pair has
been extended by zero.  This is the source entry needed before the
middle-frequency `ell` sum is split into its genuine core and rapidly
decaying tail. -/
theorem sum_gmAffineFirstPoissonPairTerm_sq_eq_tsum_retained
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ} (hM₃ : 0 < M₃)
    (Q xi : ℝ) :
    ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
        ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2 =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑' ell : ℤ,
          gmAffineRetainedFirstPoissonPairSquare
            f Q M₂ M₃ hM₃ (m₁, ell) xi := by
  rw [sum_gmAffineFirstPoissonPairs]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [tsum_eq_sum (s :=
    gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q)]
  · apply Finset.sum_congr rfl
    intro ell hell
    unfold gmAffineRetainedFirstPoissonPairSquare
    rw [ite_eq_left ((mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mp hell)]
  · intro ell hell
    unfold gmAffineRetainedFirstPoissonPairSquare
    rw [ite_eq_right]
    intro htau
    exact hell ((mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mpr htau)

/- A uniform integer-frequency radius for every retained first-Poisson
pair while the physical frequency lies in `[-Y,Y]`.  This radius is
derived from the actual near-stationary inequality rather than imposed as
an independent compact cutoff. -/
noncomputable def gmAffineFirstPoissonEllRadius
    (M₁ M₃ : ℕ) (Q Y : ℝ) : ℝ :=
  Y / M₁ + Q / (8 * M₃ : ℝ)

/- The fixed finite frequency range containing all first-Poisson pairs
over `|xi| ≤ Y`. -/
noncomputable def gmAffineFirstPoissonEllRange
    (M₁ M₃ : ℕ) (Q Y : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈gmAffineFirstPoissonEllRadius M₁ M₃ Q Y⌉)
    ⌈gmAffineFirstPoissonEllRadius M₁ M₃ Q Y⌉

/- Explicit cardinality of the fixed first-Poisson frequency range.
This is the polynomial factor used when its omitted tail is absorbed in
the `T^-100` error. -/
theorem card_gmAffineFirstPoissonEllRange_real_le
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q Y : ℝ} (hQ : 0 ≤ Q) (hY : 0 ≤ Y) :
    ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) ≤
      2 * gmAffineFirstPoissonEllRadius M₁ M₃ Q Y + 3 := by
  let R : ℝ := gmAffineFirstPoissonEllRadius M₁ M₃ Q Y
  let c : ℤ := ⌈R⌉
  have hR : 0 ≤ R := by
    dsimp only [R]
    unfold gmAffineFirstPoissonEllRadius
    positivity
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact Int.ceil_nonneg hR
  have hdiff : 0 ≤ c + 1 - (-c) := by omega
  have htoNat : (((c + 1 - (-c)).toNat : ℕ) : ℤ) = c + 1 - (-c) :=
    Int.toNat_of_nonneg hdiff
  have hcast : (((c + 1 - (-c)).toNat : ℕ) : ℝ) =
      2 * (c : ℝ) + 1 := by
    calc
      (((c + 1 - (-c)).toNat : ℕ) : ℝ) =
          ((c + 1 - (-c) : ℤ) : ℝ) := by exact_mod_cast htoNat
      _ = 2 * (c : ℝ) + 1 := by push_cast; ring
  have hcClose : (c : ℝ) < R + 1 := by
    dsimp only [c]
    exact Int.ceil_lt_add_one R
  rw [gmAffineFirstPoissonEllRange, Int.card_Icc]
  change (((c + 1 - (-c)).toNat : ℕ) : ℝ) ≤ _
  rw [hcast]
  dsimp only [R] at hcClose ⊢
  linarith

/- Every genuinely retained first-Poisson pair lies in the uniform
finite `ell` range on a bounded physical-frequency interval. -/
theorem mem_gmAffineFirstPoissonEllRange_of_pair
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q Y xi : ℝ} (hY : 0 ≤ Y) (hxi : |xi| ≤ Y)
    {p : ℤ × ℤ} (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    p.2 ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y := by
  have htau : |gmAffineFirstPoissonTau M₃ p.1 p.2 xi| < Q :=
    (mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mp
      (mem_gmAffineFirstPoissonPairs.mp hp).2
  have hp₁ := (mem_gmAffineFirstPoissonPairs.mp hp).1
  have hp₁ne : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast gmAffineSignedShell_ne_zero hM₁ hp₁
  have hp₁lower : (M₁ : ℝ) ≤ |(p.1 : ℝ)| :=
    gmAffineSignedShell_scale_le_abs hp₁
  have hA : (0 : ℝ) < 8 * M₃ := by positivity
  have hnear : |xi / (p.1 : ℝ) + (p.2 : ℝ)| < Q / (8 * M₃ : ℝ) := by
    unfold gmAffineFirstPoissonTau at htau
    rw [abs_mul, abs_of_pos hA] at htau
    apply (lt_div_iff₀ hA).2
    simpa [mul_comm] using htau
  have hxiDiv : |xi / (p.1 : ℝ)| ≤ Y / M₁ := by
    rw [abs_div]
    gcongr
  have hellBound : |(p.2 : ℝ)| <
      gmAffineFirstPoissonEllRadius M₁ M₃ Q Y := by
    have htri : |(p.2 : ℝ)| ≤
        |xi / (p.1 : ℝ) + (p.2 : ℝ)| + |xi / (p.1 : ℝ)| := by
      calc
        |(p.2 : ℝ)| =
            |(xi / (p.1 : ℝ) + (p.2 : ℝ)) - xi / (p.1 : ℝ)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    unfold gmAffineFirstPoissonEllRadius
    linarith
  have hceil : |(p.2 : ℝ)| ≤
      (⌈gmAffineFirstPoissonEllRadius M₁ M₃ Q Y⌉ : ℝ) :=
    hellBound.le.trans (Int.le_ceil _)
  rw [gmAffineFirstPoissonEllRange, Finset.mem_Icc]
  constructor
  · have hreal :
        (-⌈gmAffineFirstPoissonEllRadius M₁ M₃ Q Y⌉ : ℤ) ≤ p.2 := by
      exact_mod_cast
        ((neg_le_neg hceil).trans (neg_abs_le (p.2 : ℝ)))
    exact hreal
  · have hreal : p.2 ≤
        (⌈gmAffineFirstPoissonEllRadius M₁ M₃ Q Y⌉ : ℤ) := by
      exact_mod_cast ((le_abs_self (p.2 : ℝ)).trans hceil)
    exact hreal

/- On `|xi| ≤ Y`, the exact retained-pair square is a fixed finite
double sum.  This is the form in which finite-sum integration and the
middle/core versus far-frequency split can be carried out without any
hidden interchange of an `xi`-dependent support. -/
theorem sum_gmAffineFirstPoissonPairTerm_sq_eq_sum_retained_range
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q Y xi : ℝ} (hY : 0 ≤ Y) (hxi : |xi| ≤ Y) :
    ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
        ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2 =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
          gmAffineRetainedFirstPoissonPairSquare
            f Q M₂ M₃ hM₃ (m₁, ell) xi := by
  rw [sum_gmAffineFirstPoissonPairTerm_sq_eq_tsum_retained]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [tsum_eq_sum (s := gmAffineFirstPoissonEllRange M₁ M₃ Q Y)]
  intro ell hell
  unfold gmAffineRetainedFirstPoissonPairSquare
  rw [ite_eq_right]
  intro htau
  apply hell
  apply mem_gmAffineFirstPoissonEllRange_of_pair
    (Q := Q) (p := (m₁, ell)) hM₁ hM₃ hY hxi
  exact mem_gmAffineFirstPoissonPairs.mpr
    ⟨hm₁, (mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mpr htau⟩

/- The corresponding physical `tau` profile after the exact affine
change of variables. -/
noncomputable def gmAffineRetainedMiddleProfile
    (f : SchwartzMap ℝ ℝ) (Q : ℝ) (M₂ M₃ : ℕ) (ell : ℤ) (tau : ℝ) : ℝ :=
  if |tau| < Q then
    ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 *
      ‖gmAffineLocalBumpDual tau‖ ^ 2
  else 0

theorem integrable_gmAffineRetainedMiddleProfile
    (f : SchwartzMap ℝ ℝ) (Q : ℝ)
    (M₂ M₃ : ℕ) (ell : ℤ) :
    Integrable (gmAffineRetainedMiddleProfile f Q M₂ M₃ ell) := by
  let H : ℝ → ℝ := fun tau =>
    ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 *
      ‖gmAffineLocalBumpDual tau‖ ^ 2
  have hblock : Continuous (fun tau : ℝ =>
      gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau) := by
    unfold gmAffineMiddleFourierBlock
    apply continuous_finsetSum
    fun_prop
  have hHcont : Continuous H := by fun_prop
  have hlocal : IntegrableOn H (Set.Ioo (-Q) Q) :=
    (hHcont.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hind : Integrable (Set.indicator (Set.Ioo (-Q) Q) H) :=
    (integrable_indicator_iff measurableSet_Ioo).2 hlocal
  apply hind.congr
  filter_upwards with tau
  unfold gmAffineRetainedMiddleProfile
  by_cases htau : |tau| < Q
  · rw [ite_eq_left htau, Set.indicator_of_mem]
    exact abs_lt.mp htau
  · rw [ite_eq_right htau, Set.indicator_of_notMem]
    intro hmem
    exact htau (abs_lt.mpr hmem)

/- Pointwise affine rescaling of one retained first-Poisson pair into
its physical `tau` profile. -/
theorem gmAffineRetainedFirstPoissonPairSquare_eq_scaled_profile
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {m₁ ell : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
    (Q xi : ℝ) :
    gmAffineRetainedFirstPoissonPairSquare f Q M₂ M₃ hM₃ (m₁, ell) xi =
      ((8 * M₃ : ℝ) / |(m₁ : ℝ)|) ^ 2 *
        gmAffineRetainedMiddleProfile f Q M₂ M₃ ell
          (gmAffineFirstPoissonTau M₃ m₁ ell xi) := by
  unfold gmAffineRetainedFirstPoissonPairSquare
    gmAffineRetainedMiddleProfile
  split_ifs with hwindow
  · have hp : (m₁, ell) ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi :=
      mem_gmAffineFirstPoissonPairs.mpr
        ⟨hm₁, (mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mpr
          hwindow⟩
    rw [norm_gmAffineFirstPoissonPairTerm_sq_eq f hM₁ hM₂ hM₃ hp]
    ring
  · simp

theorem integrable_gmAffineRetainedFirstPoissonPairSquare
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {m₁ ell : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
    (Q : ℝ) :
    Integrable (gmAffineRetainedFirstPoissonPairSquare
      f Q M₂ M₃ hM₃ (m₁, ell)) := by
  have hm₁neR : (m₁ : ℝ) ≠ 0 := by
    exact_mod_cast gmAffineSignedShell_ne_zero hM₁ hm₁
  let a : ℝ := (8 * M₃ : ℝ) / (m₁ : ℝ)
  let b : ℝ := (8 * M₃ : ℝ) * (ell : ℝ)
  let H : ℝ → ℝ := gmAffineRetainedMiddleProfile f Q M₂ M₃ ell
  have ha : a ≠ 0 := div_ne_zero (by positivity) hm₁neR
  have hbase : Integrable (fun xi : ℝ => H (a * xi + b)) :=
    ((integrable_gmAffineRetainedMiddleProfile f Q M₂ M₃ ell).comp_add_right b).comp_mul_left' ha
  have hscaled := hbase.const_mul (((8 * M₃ : ℝ) / |(m₁ : ℝ)|) ^ 2)
  apply hscaled.congr
  filter_upwards with xi
  rw [gmAffineRetainedFirstPoissonPairSquare_eq_scaled_profile
    f hM₁ hM₂ hM₃ hm₁ Q xi]
  congr 2
  dsimp only [H, a, b]
  unfold gmAffineFirstPoissonTau
  field_simp [hm₁neR]

theorem integral_gmAffineRetainedFirstPoissonPairSquare_eq
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {m₁ ell : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁) (Q : ℝ) :
    (∫ xi : ℝ,
      gmAffineRetainedFirstPoissonPairSquare f Q M₂ M₃ hM₃ (m₁, ell) xi) =
      ((8 * M₃ : ℝ) / |(m₁ : ℝ)|) *
        ∫ tau : ℝ, gmAffineRetainedMiddleProfile f Q M₂ M₃ ell tau := by
  have hm₁neZ : m₁ ≠ 0 := gmAffineSignedShell_ne_zero hM₁ hm₁
  have hm₁neR : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁neZ
  let a : ℝ := (8 * M₃ : ℝ) / (m₁ : ℝ)
  let b : ℝ := (8 * M₃ : ℝ) * (ell : ℝ)
  let H : ℝ → ℝ := fun tau => gmAffineRetainedMiddleProfile f Q M₂ M₃ ell tau
  have ha : a ≠ 0 := div_ne_zero (by positivity) hm₁neR
  have htau (xi : ℝ) : gmAffineFirstPoissonTau M₃ m₁ ell xi = a * xi + b := by
    dsimp only [a, b]
    unfold gmAffineFirstPoissonTau
    field_simp [hm₁neR]
  have hpoint (xi : ℝ) :
      gmAffineRetainedFirstPoissonPairSquare f Q M₂ M₃ hM₃ (m₁, ell) xi =
        ((8 * M₃ : ℝ) / |(m₁ : ℝ)|) ^ 2 * H (a * xi + b) := by
    unfold gmAffineRetainedFirstPoissonPairSquare
    dsimp only [H]
    unfold gmAffineRetainedMiddleProfile
    rw [htau]
    split_ifs with hwindow
    · have hp : (m₁, ell) ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi :=
        mem_gmAffineFirstPoissonPairs.mpr
          ⟨hm₁, (mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mpr
            (by simpa only [htau] using hwindow)⟩
      rw [norm_gmAffineFirstPoissonPairTerm_sq_eq f hM₁ hM₂ hM₃ hp]
      simp only [htau]
      ring
    · simp
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hchange : (∫ xi : ℝ, H (a * xi + b)) = |a⁻¹| * ∫ tau : ℝ, H tau := by
    calc
      (∫ xi : ℝ, H (a * xi + b)) =
          |a⁻¹| * ∫ y : ℝ, H (y + b) := by
        simpa only [Function.comp_apply, smul_eq_mul] using
          (MeasureTheory.Measure.integral_comp_mul_left
            (fun y : ℝ => H (y + b)) a)
      _ = |a⁻¹| * ∫ tau : ℝ, H tau := by rw [integral_add_right_eq_self]
  rw [hchange]
  have habs : |a⁻¹| = |(m₁ : ℝ)| / (8 * M₃ : ℝ) := by
    dsimp only [a]
    rw [inv_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * M₃)]
  rw [habs]
  have hm₁abs : |(m₁ : ℝ)| ≠ 0 := abs_ne_zero.mpr hm₁neR
  field_simp <;> ring

theorem integral_gmAffineRetainedMiddleProfile_le
    (f : SchwartzMap ℝ ℝ) {Q : ℝ} (hQ : 0 < Q)
    (M₂ M₃ : ℕ) (ell : ℤ) :
    (∫ tau : ℝ, gmAffineRetainedMiddleProfile f Q M₂ M₃ ell tau) ≤
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
          ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 := by
  let G : ℝ → ℝ := fun tau =>
    gmAffineMiddleTauWeight Q tau *
      ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2
  have hGint : Integrable G := by
    have hcast : (8 * (M₃ : ℝ)) = ((8 * M₃ : ℕ) : ℝ) := by
      push_cast
      rfl
    dsimp only [G]
    rw [hcast]
    simpa only using
      integrable_gmAffineMiddleTauWeightedBlockSq hQ f (8 * M₃) M₂ (-ell)
  have hright : Integrable (fun tau : ℝ =>
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 * G tau) :=
    hGint.const_mul _
  have hpoint (tau : ℝ) :
      gmAffineRetainedMiddleProfile f Q M₂ M₃ ell tau ≤
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 * G tau := by
    unfold gmAffineRetainedMiddleProfile
    split_ifs with htau
    · dsimp only [G]
      rw [show gmAffineMiddleTauWeight Q tau = 1 from
        gmAffineMiddleTauWeight_one_of_abs_lt hQ htau]
      have hdual := SchwartzMap.norm_le_seminorm ℝ gmAffineLocalBumpDual tau
      have hdualSq : ‖gmAffineLocalBumpDual tau‖ ^ 2 ≤
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hdual
      have hblock : 0 ≤ ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 :=
        sq_nonneg _
      nlinarith
    · dsimp only [G]
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (gmAffineMiddleTauWeight_nonneg Q tau) (sq_nonneg _))
  calc
    (∫ tau : ℝ, gmAffineRetainedMiddleProfile f Q M₂ M₃ ell tau) ≤
        ∫ tau : ℝ,
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 * G tau := by
      apply integral_mono_of_nonneg
      · filter_upwards with tau
        unfold gmAffineRetainedMiddleProfile
        split_ifs <;> positivity
      · exact hright
      · exact Eventually.of_forall hpoint
    _ = SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
          ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 := by
      rw [integral_const_mul]

theorem integral_gmAffineRetainedFirstPoissonPairSquare_le
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {m₁ ell : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
    {Q : ℝ} (hQ : 0 < Q) :
    (∫ xi : ℝ,
      gmAffineRetainedFirstPoissonPairSquare f Q M₂ M₃ hM₃ (m₁, ell) xi) ≤
      ((8 * M₃ : ℝ) / |(m₁ : ℝ)|) *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
          ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
            ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 := by
  rw [integral_gmAffineRetainedFirstPoissonPairSquare_eq
    f hM₁ hM₂ hM₃ hm₁ Q]
  have hcoef : 0 ≤ (8 * M₃ : ℝ) / |(m₁ : ℝ)| := by positivity
  exact (mul_le_mul_of_nonneg_left
    (integral_gmAffineRetainedMiddleProfile_le f hQ M₂ M₃ ell) hcoef).trans_eq
      (by ring)

/- Summing the retained-pair integrals costs only the signed-shell
cardinality and the reciprocal lower shell endpoint.  Their product is
bounded by the absolute factor `32 M₃`, leaving precisely the middle
Fourier-block square sum that enters `Sigma_II`. -/
theorem sum_integral_gmAffineRetainedFirstPoissonPairSquare_le
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y : ℝ} (hQ : 0 < Q) :
    (∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi) ≤
      (32 * M₃ : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
          ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
            ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 := by
  let A : ℝ := SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  let I : ℤ → ℝ := fun ell =>
    ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
      ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hI (ell : ℤ) : 0 ≤ I ell := by
    dsimp only [I]
    apply integral_nonneg
    intro tau
    exact mul_nonneg (gmAffineMiddleTauWeight_nonneg Q tau) (sq_nonneg _)
  have hcoef {m₁ : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁) :
      (8 * M₃ : ℝ) / |(m₁ : ℝ)| ≤ (8 * M₃ : ℝ) / M₁ := by
    exact div_le_div_of_nonneg_left (by positivity) hM₁r
      (gmAffineSignedShell_scale_le_abs hm₁)
  calc
    (∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi) ≤
        ∑ _m₁ ∈ gmAffineSignedShell M₁,
          ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
            ((8 * M₃ : ℝ) / M₁) * A * I ell := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      apply Finset.sum_le_sum
      intro ell hell
      refine (integral_gmAffineRetainedFirstPoissonPairSquare_le
        f hM₁ hM₂ hM₃ hm₁ hQ).trans ?_
      dsimp only [A, I]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcoef hm₁) (by positivity)) (hI ell)
    _ = ((gmAffineSignedShell M₁).card : ℝ) *
          (((8 * M₃ : ℝ) / M₁) * A *
            ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell) := by
      simp_rw [← Finset.mul_sum]
      simp
      ring
    _ ≤ (32 * M₃ : ℝ) * A *
          ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell := by
      have hcardNat := card_gmAffineSignedShell_le M₁
      have hcard : ((gmAffineSignedShell M₁).card : ℝ) ≤ 4 * M₁ := by
        exact_mod_cast (hcardNat.trans (by omega : 2 * (M₁ + 1) ≤ 4 * M₁))
      have hsum : 0 ≤ ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell := by
        apply Finset.sum_nonneg
        intro ell hell
        exact hI ell
      have hA : 0 ≤ A := by positivity
      calc
        ((gmAffineSignedShell M₁).card : ℝ) *
            (((8 * M₃ : ℝ) / M₁) * A *
              ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell) ≤
            (4 * M₁ : ℝ) * (((8 * M₃ : ℝ) / M₁) * A *
              ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell) := by
          gcongr
        _ = (32 * M₃ : ℝ) * A *
              ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell := by
          field_simp [hM₁r.ne']
          ring
    _ = _ := by rfl

/-! ### Real-denominator form of the middle Fourier block -/

/- The source middle Fourier block with its denominator represented by the
actual positive real scale.  The paper's first Poisson cutoff and this
denominator are independent quantities; keeping them separate prevents a
fixed-width surrogate from replacing the retained `T^eta` window. -/
noncomputable def gmAffineMiddleFourierBlockReal
    (f : SchwartzMap ℝ ℝ) (A : ℝ) (M₂ : ℕ) (ell : ℤ) (tau : ℝ) : ℂ :=
  ∑ m₂ ∈ gmAffinePositiveShell M₂,
    (m₂ : ℂ) * fourier (gmAffineComplexify f)
      ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau)

/- Away from the central first-frequency window, every Fourier argument
in the middle block has size at least `M₂ |ell| / 2`.  This is the exact
reverse-triangle estimate needed to invoke the source rapid-decay
hypothesis uniformly in `m₂` and `tau`. -/
theorem gmAffineMiddleFourierArgument_abs_lower
    {A Q : ℝ} (hA : 0 < A)
    {M₂ : ℕ} {m₂ ell : ℤ}
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂) {tau : ℝ}
    (htau : |tau| ≤ Q) (hell : 2 * Q / A ≤ |(ell : ℝ)|) :
    (M₂ : ℝ) * |(ell : ℝ)| / 2 ≤
      |(ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau| := by
  have hm₂lower : (M₂ : ℝ) ≤ |(m₂ : ℝ)| :=
    gmAffinePositiveShell_scale_le_abs hm₂
  have htauDiv : |tau / A| ≤ Q / A := by
    rw [abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right htau hA.le
  have hrewrite : 2 * Q / A = 2 * (Q / A) := by ring
  rw [hrewrite] at hell
  have hhalf : Q / A ≤ |(ell : ℝ)| / 2 := by linarith
  have hinner : |(ell : ℝ)| / 2 ≤ |(ell : ℝ) + tau / A| := by
    have htri : |(ell : ℝ)| ≤ |(ell : ℝ) + tau / A| + |tau / A| := by
      calc
        |(ell : ℝ)| = |((ell : ℝ) + tau / A) - tau / A| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith
  calc
    (M₂ : ℝ) * |(ell : ℝ)| / 2 = (M₂ : ℝ) * (|(ell : ℝ)| / 2) := by ring
    _ ≤ |(m₂ : ℝ)| * |(ell : ℝ) + tau / A| := by gcongr
    _ = |(ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau| := by
      rw [← abs_mul]
      congr 1
      field_simp [hA.ne']

/- Uniform control of a middle Fourier block once every Fourier argument
lies beyond a prescribed threshold.  This packages the finite `m₂` sum
without weakening the source decay estimate. -/
theorem norm_gmAffineMiddleFourierBlockReal_le_of_fourier_le
    (f : SchwartzMap ℝ ℝ) {A Q B F : ℝ} (hA : 0 < A)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {ell : ℤ} {tau : ℝ}
    (htau : |tau| ≤ Q) (hell : 2 * Q / A ≤ |(ell : ℝ)|)
    (hB : B ≤ (M₂ : ℝ) * |(ell : ℝ)| / 2)
    (hfourier : ∀ x : ℝ, B ≤ |x| →
      ‖fourier (gmAffineComplexify f) x‖ ≤ F) :
    ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ≤
      ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * F := by
  unfold gmAffineMiddleFourierBlockReal
  calc
    ‖∑ m₂ ∈ gmAffinePositiveShell M₂,
        (m₂ : ℂ) * fourier (gmAffineComplexify f)
          ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau)‖ ≤
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ‖(m₂ : ℂ) * fourier (gmAffineComplexify f)
            ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m₂ ∈ gmAffinePositiveShell M₂, (2 * M₂ : ℝ) * F := by
      apply Finset.sum_le_sum
      intro m₂ hm₂
      rw [norm_mul, norm_intCast]
      have harg := gmAffineMiddleFourierArgument_abs_lower
        hA hm₂ htau hell
      have hfour := hfourier _ (hB.trans harg)
      exact mul_le_mul (abs_gmAffinePositiveShell_le_scale hm₂) hfour
        (norm_nonneg _) (by positivity)
    _ = ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * F := by
      simp
      ring

/- The source Proposition 9.1 decay hypothesis applied to one complete
middle block.  Unlike the bare Schwartz estimate above, its numerator is
the physical Fourier scale `T`, and its constant is uniform in `ell`,
`tau`, and the dyadic scale. -/
theorem norm_gmAffineMiddleFourierBlockReal_le_source_decay_of_constant
    {T epsilon C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (n : ℕ)
    (f : SchwartzMap ℝ ℝ)
    (hCdecay : ∀ xi : ℝ, xi ≠ 0 →
      ‖fourier (gmAffineComplexify f) xi‖ ≤
        C * T ^ epsilon * (T / |xi|) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))
    {A Q : ℝ} (hA : 0 < A) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {ell : ℤ} {tau : ℝ}
    (htau : |tau| ≤ Q) (hell : 2 * Q / A ≤ |(ell : ℝ)|) :
    ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ≤
      ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
        (C * T ^ epsilon *
          (2 * T / ((M₂ : ℝ) * |(ell : ℝ)|)) ^ n *
            SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) := by
  have hellpos : 0 < |(ell : ℝ)| := by
    have hleft : 0 < 2 * Q / A := by positivity
    exact hleft.trans_le hell
  let B : ℝ := (M₂ : ℝ) * |(ell : ℝ)| / 2
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  apply norm_gmAffineMiddleFourierBlockReal_le_of_fourier_le
    f hA hM₂ htau hell (B := B)
  · exact le_rfl
  · intro x hx
    have hxpos : 0 < |x| := hBpos.trans_le hx
    have hxne : x ≠ 0 := abs_pos.mp hxpos
    have hratio : T / |x| ≤ 2 * T / ((M₂ : ℝ) * |(ell : ℝ)|) := by
      calc
        T / |x| ≤ T / B := div_le_div_of_nonneg_left hT.le hBpos hx
        _ = 2 * T / ((M₂ : ℝ) * |(ell : ℝ)|) := by
          dsimp only [B]
          field_simp
    exact (hCdecay x hxne).trans (by
      gcongr)



theorem gmAffineMiddleFourierBlockReal_scale_tau
    (f : SchwartzMap ℝ ℝ) {A Q : ℝ} (hA : A ≠ 0)
    (M₂ : ℕ) (ell : ℤ) (tau : ℝ) :
    gmAffineMiddleFourierBlockReal f A M₂ ell (Q * tau) =
      gmAffineMiddleFourierBlockReal f (A / Q) M₂ ell tau := by
  unfold gmAffineMiddleFourierBlockReal
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  congr 2
  field_simp [hA]

/- The corrected `Sigma_II` with an arbitrary positive real Fourier
denominator and an independent physical `tau` width. -/
noncomputable def gmAffineSigmaIIReal
    (f : SchwartzMap ℝ ℝ) (T Q A : ℝ) (M₂ : ℕ) : ℂ :=
  ∑' ell : ℤ,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      ∫ tau : ℝ, (gmAffineMiddleTauWeight Q tau : ℂ) *
        ((‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 : ℝ) : ℂ)

theorem integrable_gmAffineMiddleTauWeightedBlockRealSq_real
    {Q : ℝ} (hQ : 0 < Q) (f : SchwartzMap ℝ ℝ)
    (A : ℝ) (M₂ : ℕ) (ell : ℤ) :
    Integrable (fun tau : ℝ =>
      gmAffineMiddleTauWeight Q tau *
        ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) := by
  have hcontBlock : Continuous (gmAffineMiddleFourierBlockReal f A M₂ ell) := by
    unfold gmAffineMiddleFourierBlockReal
    fun_prop
  have hcont : Continuous (fun tau : ℝ =>
      gmAffineMiddleTauWeight Q tau *
        ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) := by
    exact (continuous_gmAffineMiddleTauWeight Q).mul (hcontBlock.norm.pow 2)
  have hcomp : HasCompactSupport (fun tau : ℝ =>
      gmAffineMiddleTauWeight Q tau *
        ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) :=
    (hasCompactSupport_gmAffineMiddleTauWeight hQ).mul_right
  exact hcont.integrable_of_hasCompactSupport hcomp

/- The nonnegative physical middle-block mass attached to one integer
frequency. -/
noncomputable def gmAffineMiddleBlockMass
    (f : SchwartzMap ℝ ℝ) (Q A : ℝ) (M₂ : ℕ) (ell : ℤ) : ℝ :=
  ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
    ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2

theorem gmAffineMiddleBlockMass_nonneg
    (f : SchwartzMap ℝ ℝ) (Q A : ℝ) (M₂ : ℕ) (ell : ℤ) :
    0 ≤ gmAffineMiddleBlockMass f Q A M₂ ell := by
  unfold gmAffineMiddleBlockMass
  apply integral_nonneg
  intro tau
  exact mul_nonneg (gmAffineMiddleTauWeight_nonneg Q tau) (sq_nonneg _)

/- The natural-denominator middle integral produced by the first
Poisson calculation is literally the corrected real-denominator block
mass. -/


theorem integral_gmAffineMiddleTauWeightedBlockRealSq_eq_ofReal_mass
    (Q : ℝ) (f : SchwartzMap ℝ ℝ)
    (A : ℝ) (M₂ : ℕ) (ell : ℤ) :
    (∫ tau : ℝ, (gmAffineMiddleTauWeight Q tau : ℂ) *
      ((‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 : ℝ) : ℂ)) =
        (gmAffineMiddleBlockMass f Q A M₂ ell : ℂ) := by
  calc
    (∫ tau : ℝ, (gmAffineMiddleTauWeight Q tau : ℂ) *
      ((‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 : ℝ) : ℂ)) =
        ∫ tau : ℝ, Complex.ofReal (gmAffineMiddleTauWeight Q tau *
          ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards with tau
      norm_num
    _ = Complex.ofReal (∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
          ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) :=
      integral_ofReal
    _ = _ := by rfl

/- Frequencies on which the outer cutoff at scale `B` is identically
one.  The finite ambient range is retained explicitly because it comes
from the first Poisson summation, not from the second cutoff. -/
noncomputable def gmAffineMiddleCore
    (L : Finset ℤ) (B : ℝ) (M₂ : ℕ) : Finset ℤ :=
  L.filter fun ell => (M₂ : ℝ) * |(ell : ℝ)| ≤ B

/- The `gmAffineMiddleTail` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineMiddleTail
    (L : Finset ℤ) (B : ℝ) (M₂ : ℕ) : Finset ℤ :=
  L.filter fun ell => ¬(M₂ : ℝ) * |(ell : ℝ)| ≤ B

theorem mem_gmAffineMiddleTail
    {L : Finset ℤ} {B : ℝ} {M₂ : ℕ} {ell : ℤ} :
    ell ∈ gmAffineMiddleTail L B M₂ ↔
      ell ∈ L ∧ B < (M₂ : ℝ) * |(ell : ℝ)| := by
  simp only [gmAffineMiddleTail, Finset.mem_filter, not_le]

theorem gmCubicLocalBump_eq_one_of_mem_gmAffineMiddleCore
    {L : Finset ℤ} {B : ℝ} (hB : 0 < B)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {ell : ℤ}
    (hell : ell ∈ gmAffineMiddleCore L B M₂) :
    gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / B) = 1 := by
  apply gmCubicLocalBump_one
  rw [abs_div, abs_mul, abs_of_pos hB, abs_of_pos (by positivity : (0 : ℝ) < M₂)]
  exact (div_le_one hB).mpr (Finset.mem_filter.mp hell).2

theorem gmAffineMiddleCore_subset_frequencySupport
    {L : Finset ℤ} {B : ℝ} (hB : 0 < B)
    {M₂ : ℕ} (hM₂ : 0 < M₂) :
    gmAffineMiddleCore L B M₂ ⊆ gmAffineMiddleFrequencySupport B M₂ := by
  intro ell hell
  let K : ℕ := ⌈2 * B / (M₂ : ℝ)⌉₊ + 1
  have hscale := (Finset.mem_filter.mp hell).2
  have hM₂real : (0 : ℝ) < M₂ := by positivity
  have hellAbs : |(ell : ℝ)| ≤ B / (M₂ : ℝ) := by
    exact (le_div_iff₀ hM₂real).mpr (by simpa only [mul_comm] using hscale)
  have hceil : 2 * B / (M₂ : ℝ) ≤
      (⌈2 * B / (M₂ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hK : |(ell : ℝ)| ≤ (K : ℝ) := by
    dsimp only [K]
    push_cast
    have hhalf : B / (M₂ : ℝ) ≤ 2 * B / (M₂ : ℝ) := by
      exact div_le_div_of_nonneg_right (by linarith) hM₂real.le
    linarith
  have hellBounds := (abs_le.mp hK)
  change ell ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast hellBounds.1
  · exact_mod_cast hellBounds.2

/- A uniform pointwise block estimate on the physical retained window
integrates with the exact interval length `4Q`. -/
theorem integral_gmAffineMiddleTauWeightedBlockRealSq_le_of_norm_le
    {Q F : ℝ} (hQ : 0 < Q) (hF : 0 ≤ F)
    (f : SchwartzMap ℝ ℝ) (A : ℝ) (M₂ : ℕ) (ell : ℤ)
    (hblock : ∀ tau : ℝ, |tau| ≤ 2 * Q →
      ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ≤ F) :
    (∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
      ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) ≤
        4 * Q * F ^ 2 := by
  let I : Set ℝ := Set.Icc (-2 * Q) (2 * Q)
  let g : ℝ → ℝ := fun tau => gmAffineMiddleTauWeight Q tau *
    ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2
  have hg : Integrable g := by
    dsimp only [g]
    exact integrable_gmAffineMiddleTauWeightedBlockRealSq_real
      hQ f A M₂ ell
  have hgSupport : g = I.indicator g := by
    funext tau
    by_cases htau : tau ∈ I
    · simp only [Set.indicator, htau, ite_eq_left]
    · simp only [Set.indicator, htau]
      have hzero : gmAffineMiddleTauWeight Q tau = 0 := by
        apply gmAffineMiddleTauWeight_eq_zero_of_not_mem hQ
        simpa only [I] using htau
      simp [g, hzero]
  have hpoint : ∀ tau ∈ I, g tau ≤ F ^ 2 := by
    intro tau htau
    have habs : |tau| ≤ 2 * Q := by grind
    have hsq : ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 ≤ F ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hF).mpr (hblock tau habs)
    dsimp only [g]
    calc
      gmAffineMiddleTauWeight Q tau *
          ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 ≤
          1 * ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 := by
        gcongr
        exact gmAffineMiddleTauWeight_le_one Q tau
      _ ≤ F ^ 2 := by simpa using hsq
  calc
    (∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
      ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) =
        ∫ tau in I, g tau := by
      change (∫ tau : ℝ, g tau) = _
      calc
        (∫ tau : ℝ, g tau) = ∫ tau : ℝ, I.indicator g tau := by
          apply integral_congr_ae
          filter_upwards with tau
          exact congrFun hgSupport tau
        _ = ∫ tau in I, g tau := by
          rw [integral_indicator (by simpa only [I] using measurableSet_Icc)]
    _ ≤ ∫ _tau in I, F ^ 2 := by
      apply MeasureTheory.setIntegral_mono_on hg.integrableOn
        (integrableOn_const (C := F ^ 2)
          (ne_of_lt isCompact_Icc.measure_lt_top))
        (by simpa only [I] using measurableSet_Icc) hpoint
    _ = 4 * Q * F ^ 2 := by
      rw [MeasureTheory.setIntegral_const]
      change volume.real (Set.Icc (-2 * Q) (2 * Q)) * F ^ 2 = _
      rw [Real.volume_real_Icc_of_le (by linarith : -2 * Q ≤ 2 * Q)]
      ring

/- Integrated first-frequency tail bound for one fixed, already uniform
Fourier-decay constant. -/
theorem integral_gmAffineMiddleTauWeightedBlockRealSq_le_source_decay_of_constant
    {T epsilon C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (n : ℕ)
    (f : SchwartzMap ℝ ℝ)
    (hCdecay : ∀ xi : ℝ, xi ≠ 0 →
      ‖fourier (gmAffineComplexify f) xi‖ ≤
        C * T ^ epsilon * (T / |xi|) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))
    {A Q : ℝ} (hA : 0 < A) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {ell : ℤ}
    (hell : 4 * Q / A ≤ |(ell : ℝ)|) :
    (∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
      ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2) ≤
        4 * Q *
          (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
            (C * T ^ epsilon *
              (2 * T / ((M₂ : ℝ) * |(ell : ℝ)|)) ^ n *
                SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2 := by
  let F : ℝ := ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
    (C * T ^ epsilon *
      (2 * T / ((M₂ : ℝ) * |(ell : ℝ)|)) ^ n *
        SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))
  have hF : 0 ≤ F := by
    dsimp only [F]
    positivity
  apply integral_gmAffineMiddleTauWeightedBlockRealSq_le_of_norm_le
    hQ hF f A M₂ ell
  intro tau htau
  apply norm_gmAffineMiddleFourierBlockReal_le_source_decay_of_constant
    hT hC n f hCdecay hA (show 0 < 2 * Q by positivity) hM₂ htau
  calc
    2 * (2 * Q) / A = 4 * Q / A := by ring
    _ ≤ |(ell : ℝ)| := hell

/- The complete omitted first-frequency tail for one fixed uniform decay
the constant.  This is the form used to keep constants outside the physical
height quantifier in Proposition 9.1. -/
theorem sum_gmAffineMiddleTail_mass_le_source_decay_of_constant
    {T epsilon C : ℝ} (hT : 0 < T) (hC : 0 ≤ C) (n : ℕ)
    (f : SchwartzMap ℝ ℝ)
    (hCdecay : ∀ xi : ℝ, xi ≠ 0 →
      ‖fourier (gmAffineComplexify f) xi‖ ≤
        C * T ^ epsilon * (T / |xi|) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))
    (L : Finset ℤ) {A Q B : ℝ} (hA : 0 < A) (hQ : 0 < Q) (hB : 0 < B)
    {M₂ : ℕ} (hM₂ : 0 < M₂)
    (hwidth : 4 * Q * (M₂ : ℝ) / A ≤ B) :
    (∑ ell ∈ gmAffineMiddleTail L B M₂,
      gmAffineMiddleBlockMass f Q A M₂ ell) ≤
      (L.card : ℝ) * 4 * Q *
        (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
          (C * T ^ epsilon * (2 * T / B) ^ n *
            SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2 := by
  let D : ℝ := ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ)
  let S : ℝ := SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)
  let F : ℝ := D * (C * T ^ epsilon * (2 * T / B) ^ n * S)
  have hF : 0 ≤ F := by
    dsimp only [F, D, S]
    positivity
  calc
    (∑ ell ∈ gmAffineMiddleTail L B M₂,
      gmAffineMiddleBlockMass f Q A M₂ ell) ≤
        ∑ _ell ∈ gmAffineMiddleTail L B M₂, 4 * Q * F ^ 2 := by
      apply Finset.sum_le_sum
      intro ell hell
      have hellTail := (mem_gmAffineMiddleTail.mp hell).2
      have hellSource : 4 * Q / A ≤ |(ell : ℝ)| := by
        have hM₂real : (0 : ℝ) < M₂ := by positivity
        have hmul : (4 * Q / A) * (M₂ : ℝ) <
            |(ell : ℝ)| * (M₂ : ℝ) := by
          calc
            (4 * Q / A) * M₂ = 4 * Q * M₂ / A := by ring
            _ ≤ B := hwidth
            _ < (M₂ : ℝ) * |(ell : ℝ)| := hellTail
            _ = |(ell : ℝ)| * M₂ := by ring
        exact le_of_lt (lt_of_mul_lt_mul_right hmul hM₂real.le)
      refine (integral_gmAffineMiddleTauWeightedBlockRealSq_le_source_decay_of_constant
        hT hC n f hCdecay hA hQ hM₂ hellSource).trans ?_
      have hratio : 2 * T / ((M₂ : ℝ) * |(ell : ℝ)|) ≤ 2 * T / B := by
        exact div_le_div_of_nonneg_left (by positivity) hB hellTail.le
      have hpow : (2 * T / ((M₂ : ℝ) * |(ell : ℝ)|)) ^ n ≤
          (2 * T / B) ^ n := by gcongr
      have hinner :
          C * T ^ epsilon *
              (2 * T / ((M₂ : ℝ) * |(ell : ℝ)|)) ^ n * S ≤
            C * T ^ epsilon * (2 * T / B) ^ n * S := by
        gcongr
      have hblockCommon :
          ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
              (C * T ^ epsilon *
                (2 * T / ((M₂ : ℝ) * |(ell : ℝ)|)) ^ n * S) ≤ F := by
        dsimp only [F, D]
        gcongr
      gcongr
    _ = ((gmAffineMiddleTail L B M₂).card : ℝ) * (4 * Q * F ^ 2) := by
      simp
    _ ≤ (L.card : ℝ) * (4 * Q * F ^ 2) := by
      have hcardNat : (gmAffineMiddleTail L B M₂).card ≤ L.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hcard : ((gmAffineMiddleTail L B M₂).card : ℝ) ≤ L.card := by
        exact_mod_cast hcardNat
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (L.card : ℝ) * 4 * Q * F ^ 2 := by ring
    _ = _ := by rfl

/- The complete omitted first-frequency tail is negligible at arbitrary
order once the outer cutoff scale dominates the physical translation
width.  The cardinality of the original finite first-Poisson range is
kept explicit for the later `T^6` comparison. -/
theorem exists_sum_gmAffineMiddleTail_mass_le_source_decay
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (n : ℕ) (f : SchwartzMap ℝ ℝ)
    (hdecay : GMAffineFourierDecayAt T f) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (L : Finset ℤ) {A Q B : ℝ}, 0 < A → 0 < Q → 0 < B →
      ∀ {M₂ : ℕ}, 0 < M₂ →
      4 * Q * (M₂ : ℝ) / A ≤ B →
      (∑ ell ∈ gmAffineMiddleTail L B M₂,
        gmAffineMiddleBlockMass f Q A M₂ ell) ≤
        (L.card : ℝ) * 4 * Q *
          (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
            (C * T ^ epsilon * (2 * T / B) ^ n *
              SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2 := by
  obtain ⟨C, hC, hCdecay⟩ := hdecay epsilon hepsilon n
  refine ⟨C, hC, ?_⟩
  intro L A Q B hA hQ hB M₂ hM₂ hwidth
  exact sum_gmAffineMiddleTail_mass_le_source_decay_of_constant
    hT hC n f hCdecay L hA hQ hB hM₂ hwidth

/- Negation of a finite frequency set.  The first Poisson formula uses
`-ℓ` in the middle Fourier block, whereas the corrected `Sigma_II` is
indexed by its actual Fourier frequency. -/
def gmAffineNegFrequencyImage (L : Finset ℤ) : Finset ℤ :=
  L.image fun ell => -ell

@[simp]
theorem card_gmAffineNegFrequencyImage (L : Finset ℤ) :
    (gmAffineNegFrequencyImage L).card = L.card := by
  unfold gmAffineNegFrequencyImage
  rw [Finset.card_image_iff.mpr]
  simp

theorem sum_gmAffineMiddleBlockMass_neg_eq_image
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ) (Q A : ℝ) (M₂ : ℕ) :
    (∑ ell ∈ L, gmAffineMiddleBlockMass f Q A M₂ (-ell)) =
      ∑ k ∈ gmAffineNegFrequencyImage L,
        gmAffineMiddleBlockMass f Q A M₂ k := by
  classical
  unfold gmAffineNegFrequencyImage
  apply Finset.sum_bij (fun ell _ => -ell)
  · intro ell hell
    exact Finset.mem_image.mpr ⟨ell, hell, rfl⟩
  · intro ell₁ hell₁ ell₂ hell₂ heq
    exact neg_inj.mp heq
  · intro k hk
    obtain ⟨ell, hell, hkEq⟩ := Finset.mem_image.mp hk
    exact ⟨ell, hell, hkEq⟩
  · intro ell hell
    rfl

/- Rescaling the physical retained window to unit width changes the real
Fourier denominator from `A` to `A / Q` and contributes the exact Jacobian
`Q`. -/
theorem integral_gmAffineMiddleTauWeight_blockReal_scale
    (f : SchwartzMap ℝ ℝ) {A Q : ℝ} (hA : 0 < A) (hQ : 0 < Q)
    (M₂ : ℕ) (ell : ℤ) :
    (∫ tau : ℝ, (gmAffineMiddleTauWeight Q tau : ℂ) *
        ((‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 : ℝ) : ℂ)) =
      (Q : ℂ) * ∫ s : ℝ, (gmCubicLocalBump s : ℂ) *
        ((‖gmAffineMiddleFourierBlockReal f (A / Q) M₂ ell s‖ ^ 2 : ℝ) : ℂ) := by
  let H : ℝ → ℂ := fun s =>
    (gmCubicLocalBump s : ℂ) *
      ((‖gmAffineMiddleFourierBlockReal f (A / Q) M₂ ell s‖ ^ 2 : ℝ) : ℂ)
  have hpoint (s : ℝ) :
      (gmAffineMiddleTauWeight Q (Q * s) : ℂ) *
          ((‖gmAffineMiddleFourierBlockReal f A M₂ ell (Q * s)‖ ^ 2 : ℝ) : ℂ) =
        H s := by
    unfold gmAffineMiddleTauWeight
    rw [mul_div_cancel_left₀ s hQ.ne',
      gmAffineMiddleFourierBlockReal_scale_tau f hA.ne']
  have hchange := MeasureTheory.Measure.integral_comp_mul_left
    (fun tau : ℝ =>
      (gmAffineMiddleTauWeight Q tau : ℂ) *
        ((‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 : ℝ) : ℂ)) Q
  rw [abs_inv, abs_of_pos hQ] at hchange
  have hscaled :
      (∫ s : ℝ,
          (gmAffineMiddleTauWeight Q (Q * s) : ℂ) *
            ((‖gmAffineMiddleFourierBlockReal f A M₂ ell (Q * s)‖ ^ 2 : ℝ) : ℂ)) =
        ((Q⁻¹ : ℝ) : ℂ) * ∫ tau : ℝ,
          (gmAffineMiddleTauWeight Q tau : ℂ) *
            ((‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 : ℝ) : ℂ) := by assumption
  simp_rw [hpoint] at hscaled
  have hQcomplex : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hcastInv : ((Q⁻¹ : ℝ) : ℂ) = (Q : ℂ)⁻¹ := by norm_cast
  grind

theorem gmAffineMiddleTauWeight_one (tau : ℝ) :
    gmAffineMiddleTauWeight 1 tau = gmCubicLocalBump tau := by
  unfold gmAffineMiddleTauWeight
  rw [div_one]

theorem gmAffineSigmaIIReal_eq_finiteSupport
    {T Q A : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) :
    gmAffineSigmaIIReal f T Q A M₂ =
      ∑ ell ∈ gmAffineMiddleFrequencySupport T M₂,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ, (gmAffineMiddleTauWeight Q tau : ℂ) *
            ((‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ^ 2 : ℝ) : ℂ) := by
  unfold gmAffineSigmaIIReal
  rw [tsum_eq_sum (s := gmAffineMiddleFrequencySupport T M₂)]
  intro ell hell
  rw [gmCubicLocalBump_middleFrequency_eq_zero_of_not_mem hT hM₂ hell]
  simp

/- The corrected `Sigma_II` is a nonnegative real finite sum.  This
identity permits order comparisons with exact subfamilies of the first
Poisson frequencies instead of using a triangle inequality in the wrong
direction. -/
theorem norm_gmAffineSigmaIIReal_eq_sum_mass
    {T : ℝ} (hT : 0 < T) (Q A : ℝ)
    {M₂ : ℕ} (hM₂ : 0 < M₂) (f : SchwartzMap ℝ ℝ) :
    ‖gmAffineSigmaIIReal f T Q A M₂‖ =
      ∑ ell ∈ gmAffineMiddleFrequencySupport T M₂,
        gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) *
          gmAffineMiddleBlockMass f Q A M₂ ell := by
  rw [gmAffineSigmaIIReal_eq_finiteSupport hT hM₂]
  simp_rw [integral_gmAffineMiddleTauWeightedBlockRealSq_eq_ofReal_mass Q]
  have hcast :
      (∑ ell ∈ gmAffineMiddleFrequencySupport T M₂,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          (gmAffineMiddleBlockMass f Q A M₂ ell : ℂ)) =
        Complex.ofReal (∑ ell ∈ gmAffineMiddleFrequencySupport T M₂,
          gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) *
            gmAffineMiddleBlockMass f Q A M₂ ell) := by
    simp_rw [← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  apply Finset.sum_nonneg
  intro ell hell
  exact mul_nonneg (gmCubicLocalBump_nonneg _)
    (gmAffineMiddleBlockMass_nonneg f Q A M₂ ell)

/- The complete core of any first-Poisson frequency range is bounded by
the corrected equation-(9.7) quantity at cutoff scale `B`. -/
theorem sum_gmAffineMiddleCore_mass_le_norm_sigmaIIReal
    (L : Finset ℤ) {B : ℝ} (hB : 0 < B) (Q A : ℝ)
    {M₂ : ℕ} (hM₂ : 0 < M₂) (f : SchwartzMap ℝ ℝ) :
    (∑ ell ∈ gmAffineMiddleCore L B M₂,
      gmAffineMiddleBlockMass f Q A M₂ ell) ≤
        ‖gmAffineSigmaIIReal f B Q A M₂‖ := by
  rw [norm_gmAffineSigmaIIReal_eq_sum_mass hB Q A hM₂ f]
  calc
    (∑ ell ∈ gmAffineMiddleCore L B M₂,
      gmAffineMiddleBlockMass f Q A M₂ ell) =
        ∑ ell ∈ gmAffineMiddleCore L B M₂,
          gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / B) *
            gmAffineMiddleBlockMass f Q A M₂ ell := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [gmCubicLocalBump_eq_one_of_mem_gmAffineMiddleCore hB hM₂ hell]
      simp
    _ ≤ ∑ ell ∈ gmAffineMiddleFrequencySupport B M₂,
          gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / B) *
            gmAffineMiddleBlockMass f Q A M₂ ell := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (gmAffineMiddleCore_subset_frequencySupport hB hM₂)
      intro ell hellSupport hellCore
      exact mul_nonneg (gmCubicLocalBump_nonneg _)
        (gmAffineMiddleBlockMass_nonneg f Q A M₂ ell)

theorem sum_gmAffineMiddleBlockMass_le_sigmaIIReal_add_tail
    (L : Finset ℤ) {B : ℝ} (hB : 0 < B) (Q A : ℝ)
    {M₂ : ℕ} (hM₂ : 0 < M₂) (f : SchwartzMap ℝ ℝ) :
    (∑ ell ∈ L, gmAffineMiddleBlockMass f Q A M₂ ell) ≤
      ‖gmAffineSigmaIIReal f B Q A M₂‖ +
        ∑ ell ∈ gmAffineMiddleTail L B M₂,
          gmAffineMiddleBlockMass f Q A M₂ ell := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    L (fun ell : ℤ => (M₂ : ℝ) * |(ell : ℝ)| ≤ B)
      (fun ell => gmAffineMiddleBlockMass f Q A M₂ ell)
  change
    (∑ ell ∈ gmAffineMiddleCore L B M₂,
        gmAffineMiddleBlockMass f Q A M₂ ell) +
      (∑ ell ∈ gmAffineMiddleTail L B M₂,
        gmAffineMiddleBlockMass f Q A M₂ ell) =
      ∑ ell ∈ L, gmAffineMiddleBlockMass f Q A M₂ ell at hsplit
  rw [← hsplit]
  gcongr
  exact sum_gmAffineMiddleCore_mass_le_norm_sigmaIIReal
    L hB Q A hM₂ f

/- The complete first-Poisson middle-block mass, including the sign
change in the paper's frequency variable, is controlled by the genuine
`Sigma_II` core plus the explicit rapidly decaying tail. -/
theorem sum_gmAffineMiddleBlockMass_neg_le_sigmaIIReal_add_tail
    (L : Finset ℤ) {B : ℝ} (hB : 0 < B) (Q A : ℝ)
    {M₂ : ℕ} (hM₂ : 0 < M₂) (f : SchwartzMap ℝ ℝ) :
    (∑ ell ∈ L, gmAffineMiddleBlockMass f Q A M₂ (-ell)) ≤
      ‖gmAffineSigmaIIReal f B Q A M₂‖ +
        ∑ k ∈ gmAffineMiddleTail (gmAffineNegFrequencyImage L) B M₂,
          gmAffineMiddleBlockMass f Q A M₂ k := by
  rw [sum_gmAffineMiddleBlockMass_neg_eq_image]
  exact sum_gmAffineMiddleBlockMass_le_sigmaIIReal_add_tail
    (gmAffineNegFrequencyImage L) hB Q A hM₂ f

/- The exact retained first-Poisson pair integrals are controlled by the
corrected middle `Sigma_II` and the complete omitted frequency tail.
This composes the first change of variables, its signed-shell cost, and
the frequency-sign reindexing without discarding a lattice mode. -/
theorem sum_integral_gmAffineRetainedFirstPoissonPairSquare_le_sigmaIIReal_add_tail
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y B : ℝ} (hQ : 0 < Q) (hB : 0 < B) :
    (∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi) ≤
      (32 * M₃ : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        (‖gmAffineSigmaIIReal f B Q (8 * M₃) M₂‖ +
          ∑ k ∈ gmAffineMiddleTail
              (gmAffineNegFrequencyImage
                (gmAffineFirstPoissonEllRange M₁ M₃ Q Y)) B M₂,
            gmAffineMiddleBlockMass f Q (8 * M₃) M₂ k) := by
  let L := gmAffineFirstPoissonEllRange M₁ M₃ Q Y
  let K : ℝ :=
    (32 * M₃ : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  have hsumEq :
      (∑ ell ∈ L,
        ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
          ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2) =
        ∑ ell ∈ L,
          gmAffineMiddleBlockMass f Q (8 * M₃) M₂ (-ell) := by rfl
  have hmiddle := sum_gmAffineMiddleBlockMass_neg_le_sigmaIIReal_add_tail
    L hB Q (8 * M₃ : ℝ) hM₂ f
  calc
    (∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi) ≤
        K * ∑ ell ∈ L,
          ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
            ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 := by
      simpa only [K, L] using
        sum_integral_gmAffineRetainedFirstPoissonPairSquare_le
          f hM₁ hM₂ hM₃ hQ
    _ = K * ∑ ell ∈ L,
          gmAffineMiddleBlockMass f Q (8 * M₃) M₂ (-ell) := by rw [hsumEq]
    _ ≤ K * (‖gmAffineSigmaIIReal f B Q (8 * M₃) M₂‖ +
          ∑ k ∈ gmAffineMiddleTail (gmAffineNegFrequencyImage L) B M₂,
            gmAffineMiddleBlockMass f Q (8 * M₃) M₂ k) := by
      exact mul_le_mul_of_nonneg_left hmiddle (by positivity)
    _ = _ := by rfl

/- Exact retained/omitted square split for the Fourier transform in
equation (9.3).  The factor two is the sole loss from replacing the norm
of the sum by the two square energies. -/
theorem norm_gmAffineSmoothTransformSchwartz_fourier_sq_le_main_add_far
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 0 < Q) (xi : ℝ) :
    ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2 ≤
      2 * ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2 +
      2 * ‖gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2 := by
  rw [gmAffineSmoothTransformSchwartz_fourier_eq_main_add_far
    n f hM₁ hM₂ hM₃ hQ xi]
  have hnorm := norm_add_le
    (gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi)
    (gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  nlinarith [sq_nonneg
    (‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ -
      ‖gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi‖)]

/- Integrated Region-II estimate for the complete Fourier transform.
It keeps the exact retained first-Poisson pair integrals and the complete
omitted Poisson envelope separate, before either is specialized to a
power of `T`. -/
theorem integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_uniform_pairs_add_far
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y D : ℝ} (hQ : 0 < Q) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hcard : ∀ xi : ℝ,
      gmAffineFirstPoissonRadius M₁ M₃ Q < |xi| → |xi| ≤ Y →
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤ D) :
    (∫ xi in gmAffineMiddleFrequencyRegion
        (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
      ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
      2 * D *
        (∑ m₁ ∈ gmAffineSignedShell M₁,
          ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
            ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
              f Q M₂ M₃ hM₃ (m₁, ell) xi) +
      4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 := by
  let X : ℝ := gmAffineFirstPoissonRadius M₁ M₃ Q
  let S : ℝ → ℝ := fun xi =>
    ∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi
  let E : ℝ := gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q
  have hterm (m₁ : ℤ) (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
      (ell : ℤ) (_hell : ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y) :
      Integrable (gmAffineRetainedFirstPoissonPairSquare
        f Q M₂ M₃ hM₃ (m₁, ell)) :=
    integrable_gmAffineRetainedFirstPoissonPairSquare
      f hM₁ hM₂ hM₃ hm₁ Q
  have hSint : Integrable S := by fun_prop
  have hSnonneg (xi : ℝ) : 0 ≤ S xi := by
    dsimp only [S]
    apply Finset.sum_nonneg
    intro m₁ hm₁
    apply Finset.sum_nonneg
    intro ell hell
    unfold gmAffineRetainedFirstPoissonPairSquare
    split_ifs <;> positivity
  have hE : 0 ≤ E := by
    have hfar := norm_gmAffinePoissonFarFourier_le
      n f hM₁ hM₂ hM₃ hQ 0
    exact (norm_nonneg
      (gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q 0)).trans
        (by simpa only [E, gmAffinePoissonFarEnvelope] using hfar)
  have hsubset : gmAffineMiddleFrequencyRegion X Y ⊆ Set.Icc (-Y) Y := by
    intro xi hxi
    rw [gmAffineMiddleFrequencyRegion] at hxi
    exact (abs_le.mp hxi.2)
  have hconstInt : IntegrableOn (fun _xi : ℝ => 2 * E ^ 2) (Set.Icc (-Y) Y) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hright : IntegrableOn (fun xi : ℝ => 2 * D * S xi + 2 * E ^ 2)
      (gmAffineMiddleFrequencyRegion X Y) := by
    apply Integrable.add
    · exact (hSint.const_mul (2 * D)).integrableOn
    · exact hconstInt.mono_set hsubset
  have hpoint : ∀ xi ∈ gmAffineMiddleFrequencyRegion X Y,
      ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2 ≤
        2 * D * S xi + 2 * E ^ 2 := by
    intro xi hxi
    have hxiData := hxi
    rw [gmAffineMiddleFrequencyRegion] at hxiData
    have hsum := sum_gmAffineFirstPoissonPairTerm_sq_eq_sum_retained_range
      (M₂ := M₂) (Q := Q) f hM₁ hM₃ hY hxiData.2
    have hmain := norm_gmAffinePoissonMainFourier_sq_le_pairs
      f M₁ M₂ M₃ hM₃ Q xi
    rw [hsum] at hmain
    have hmainD :
        ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2 ≤
          D * S xi := by
      exact hmain.trans (mul_le_mul (hcard xi hxiData.1 hxiData.2) le_rfl
        (hSnonneg xi) hD)
    have hfarNorm :
        ‖gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi‖ ≤ E := by
      simpa only [E, gmAffinePoissonFarEnvelope] using
        norm_gmAffinePoissonFarFourier_le n f hM₁ hM₂ hM₃ hQ xi
    have hfarSq :
        ‖gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2 ≤ E ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hE).mpr hfarNorm
    exact (norm_gmAffineSmoothTransformSchwartz_fourier_sq_le_main_add_far
      n f hM₁ hM₂ hM₃ hQ xi).trans (by nlinarith)
  calc
    (∫ xi in gmAffineMiddleFrequencyRegion X Y,
      ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
        ∫ xi in gmAffineMiddleFrequencyRegion X Y,
          (2 * D * S xi + 2 * E ^ 2) := by
      apply integral_mono_of_nonneg
      · filter_upwards with xi
        exact sq_nonneg _
      · exact hright
      · filter_upwards [self_mem_ae_restrict
          (measurableSet_gmAffineMiddleFrequencyRegion X Y)] with xi hxi
        exact hpoint xi hxi
    _ = (∫ xi in gmAffineMiddleFrequencyRegion X Y, 2 * D * S xi) +
          ∫ xi in gmAffineMiddleFrequencyRegion X Y, 2 * E ^ 2 := by
      rw [integral_add (hSint.const_mul (2 * D)).integrableOn
        (hconstInt.mono_set hsubset)]
    _ ≤ (∫ xi : ℝ, 2 * D * S xi) +
          ∫ xi in Set.Icc (-Y) Y, 2 * E ^ 2 := by
      apply add_le_add
      · exact setIntegral_le_integral (hSint.const_mul (2 * D))
          (Eventually.of_forall fun xi => mul_nonneg (by positivity) (hSnonneg xi))
      · exact setIntegral_mono_set hconstInt
          (Eventually.of_forall fun _ => by positivity) hsubset.eventuallyLE
    _ = 2 * D *
          (∑ m₁ ∈ gmAffineSignedShell M₁,
            ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
              ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
                f Q M₂ M₃ hM₃ (m₁, ell) xi) +
          4 * Y * E ^ 2 := by
      rw [integral_const_mul]
      dsimp only [S]
      rw [MeasureTheory.integral_finsetSum (gmAffineSignedShell M₁) (by fun_prop)]
      apply congrArg₂ (fun a b : ℝ => a + b)
      · congr 1
        apply Finset.sum_congr rfl
        intro m₁ hm₁
        rw [MeasureTheory.integral_finsetSum
          (gmAffineFirstPoissonEllRange M₁ M₃ Q Y) (hterm m₁ hm₁)]
      · rw [MeasureTheory.setIntegral_const]
        change volume.real (Set.Icc (-Y) Y) * (2 * E ^ 2) = 4 * Y * E ^ 2
        rw [Real.volume_real_Icc_of_le (by linarith)]
        ring
    _ = _ := by rfl

/- Full Region-II Fourier energy after composing the uniform divisor
count with the exact first-Poisson and `Sigma_II` reductions. -/
theorem exists_integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_tails
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (n : ℕ)
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y B : ℝ} (hQ : 0 < Q) (hY : 0 ≤ Y) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      (∫ xi in gmAffineMiddleFrequencyRegion
          (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
        2 *
          (C * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
            (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
          ((32 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
            (‖gmAffineSigmaIIReal f B Q (8 * M₃) M₂‖ +
              ∑ k ∈ gmAffineMiddleTail
                  (gmAffineNegFrequencyImage
                    (gmAffineFirstPoissonEllRange M₁ M₃ Q Y)) B M₂,
                gmAffineMiddleBlockMass f Q (8 * M₃) M₂ k)) +
        4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 := by
  obtain ⟨C, hC, hcard⟩ :=
    exists_uniform_card_gmAffineFirstPoissonPairs_middle_real_le
      hepsilon hM₁ hM₃ hQ hY
  refine ⟨C, hC, ?_⟩
  let D : ℝ := C * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
    (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hfull :=
    integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_uniform_pairs_add_far
      n f hM₁ hM₂ hM₃ hQ hY hD (fun xi hxiLower hxiUpper =>
        hcard xi hxiLower.le hxiUpper)
  have hpairs :=
    sum_integral_gmAffineRetainedFirstPoissonPairSquare_le_sigmaIIReal_add_tail
      (Y := Y) f hM₁ hM₂ hM₃ hQ hB
  refine hfull.trans ?_
  have hcoef : 0 ≤ 2 * D := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left hpairs hcoef) le_rfl

/- Region-II estimate with explicitly supplied divisor and Fourier-decay
constants.  Neither constant is selected after the scale triple or height;
this is the source quantifier order needed by the iterative argument. -/
theorem integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_source_tails_of_constants
    {epsilon T Cdiv Ctail : ℝ} (hT : 0 < T)
    (hCdiv : 0 < Cdiv) (hCtail : 0 ≤ Ctail) (n : ℕ)
    (f : SchwartzMap ℝ ℝ)
    (hCdecay : ∀ xi : ℝ, xi ≠ 0 →
      ‖fourier (gmAffineComplexify f) xi‖ ≤
        Ctail * T ^ epsilon * (T / |xi|) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))
    {M₁ M₂ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y B : ℝ} (hQ : 0 < Q) (hY : 0 ≤ Y) (hB : 0 < B)
    (hcard : ∀ xi : ℝ,
      gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi| → |xi| ≤ Y →
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3))
    (hwidth : 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) ≤ B) :
    (∫ xi in gmAffineMiddleFrequencyRegion
        (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
      ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
      2 *
        (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
        ((32 * M₃ : ℝ) *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
          (‖gmAffineSigmaIIReal f B Q (8 * M₃) M₂‖ +
            ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
              4 * Q *
              (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
                (Ctail * T ^ epsilon * (2 * T / B) ^ n *
                  SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2)) +
      4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 := by
  let D : ℝ := Cdiv *
    (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let K : ℝ := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hfull :=
    integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_uniform_pairs_add_far
      n f hM₁ hM₂ hM₃ hQ hY hD (fun xi hxiLower hxiUpper =>
        hcard xi hxiLower.le hxiUpper)
  have hpairs :=
    sum_integral_gmAffineRetainedFirstPoissonPairSquare_le_sigmaIIReal_add_tail
      (Y := Y) f hM₁ hM₂ hM₃ hQ hB
  have hfull' := hfull.trans
    (add_le_add (mul_le_mul_of_nonneg_left hpairs (by positivity)) le_rfl)
  have htail := sum_gmAffineMiddleTail_mass_le_source_decay_of_constant
    hT hCtail n f hCdecay
      (gmAffineNegFrequencyImage
        (gmAffineFirstPoissonEllRange M₁ M₃ Q Y))
      (show 0 < (8 * M₃ : ℝ) by positivity) hQ hB hM₂ hwidth
  rw [card_gmAffineNegFrequencyImage] at htail
  refine hfull'.trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · exact add_le_add le_rfl htail
      · exact hK
    · positivity
  · exact le_rfl

/- Region-II estimate with the complete first-frequency tail replaced
by its arbitrary-order source Fourier-decay bound.  The two constants
have the correct quantifier order: both are chosen before the scale
triple and Fourier variable. -/
theorem exists_integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_source_tails
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (n : ℕ)
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hdecay : GMAffineFourierDecayAt T f)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y B : ℝ} (hQ : 0 < Q) (hY : 0 ≤ Y) (hB : 0 < B)
    (hwidth : 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) ≤ B) :
    ∃ Cdiv Ctail : ℝ, 0 < Cdiv ∧ 0 ≤ Ctail ∧
      (∫ xi in gmAffineMiddleFrequencyRegion
          (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
        2 *
          (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
            (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
          ((32 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
            (‖gmAffineSigmaIIReal f B Q (8 * M₃) M₂‖ +
              ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
                4 * Q *
                (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
                  (Ctail * T ^ epsilon * (2 * T / B) ^ n *
                    SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2)) +
        4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 := by
  obtain ⟨Cdiv, hCdiv, hfull⟩ :=
    exists_integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_tails
      hepsilon n f hM₁ hM₂ hM₃ hQ hY hB
  obtain ⟨Ctail, hCtail, htail⟩ :=
    exists_sum_gmAffineMiddleTail_mass_le_source_decay
      hT hepsilon n f hdecay
  refine ⟨Cdiv, Ctail, hCdiv, hCtail, hfull.trans ?_⟩
  let D : ℝ := Cdiv *
    (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let K : ℝ := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have htail' := htail
    (gmAffineNegFrequencyImage
      (gmAffineFirstPoissonEllRange M₁ M₃ Q Y))
    (show 0 < (8 * M₃ : ℝ) by positivity) hQ hB hM₂ hwidth
  rw [card_gmAffineNegFrequencyImage] at htail'
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · exact add_le_add le_rfl htail'
      · exact hK
    · positivity
  · exact le_rfl

/- Exact unit-window normalization of the corrected middle-frequency
quantity.  This is the faithful bridge from the first Poisson width `Q` to
the unit-width equation-(9.7) analysis. -/
theorem gmAffineSigmaIIReal_scale_window
    (f : SchwartzMap ℝ ℝ) {T Q A : ℝ}
    (hT : 0 < T) (hQ : 0 < Q) (hA : 0 < A)
    {M₂ : ℕ} (hM₂ : 0 < M₂) :
    gmAffineSigmaIIReal f T Q A M₂ =
      (Q : ℂ) * gmAffineSigmaIIReal f T 1 (A / Q) M₂ := by
  rw [gmAffineSigmaIIReal_eq_finiteSupport hT hM₂,
    gmAffineSigmaIIReal_eq_finiteSupport hT hM₂]
  simp_rw [integral_gmAffineMiddleTauWeight_blockReal_scale
    f hA hQ M₂, gmAffineMiddleTauWeight_one]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  ring

/- At unit physical width the corrected real-denominator quantity is
definitionally the equation-(9.7) quantity.  Thus all Fubini, second-Poisson,
near/far, and affine-energy estimates above apply without rounding the
Fourier denominator. -/
theorem gmAffineSigmaIIReal_one_eq_sigmaII
    (f : SchwartzMap ℝ ℝ) (T A : ℝ) (M₂ : ℕ) :
    gmAffineSigmaIIReal f T 1 A M₂ = gmAffineSigmaII f T A M₂ := by
  unfold gmAffineSigmaIIReal gmAffineSigmaII
  apply tsum_congr
  intro ell
  congr 1
  apply integral_congr_ae
  filter_upwards with tau
  rw [gmAffineMiddleTauWeight_one]
  rfl

/- Complete source-faithful middle-frequency estimate with independent
physical width `Q` and real Fourier denominator `A`.  The exact rescaling
contributes one factor `Q`; the equation-(9.7) estimate is then applied at
the genuine denominator `A / Q`. -/
theorem norm_gmAffineSigmaIIReal_le_J_add_far
    (n : ℕ) {T Q A : ℝ}
    (hT : 0 < T) (hQ : 0 < Q) (hA : 0 < A) (hQT : Q ≤ T)
    {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f) :
    ‖gmAffineSigmaIIReal f T Q A M₂‖ ≤
      Q * (16 * (M₂ : ℝ) ^ 2 *
        ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz (T / Q) (by positivity) f) M₂)) +
        16 * (M₂ : ℝ) ^ 2 *
          ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
            gmAffineMiddleFarBound n T Q M₂ *
              (∫ u : ℝ, |f u|) ^ 2) := by
  rw [gmAffineSigmaIIReal_scale_window f hT hQ hA hM₂,
    gmAffineSigmaIIReal_one_eq_sigmaII, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hQ]
  exact mul_le_mul_of_nonneg_left
    (norm_gmAffineSigmaII_le_J_add_far
      n hT hQ hQT hM₂ f hf hsupp (A / Q)) hQ.le

/- Source-faithful Region-II estimate without the spurious restriction
`M₂ ≤ T`.  The second-Poisson cutoff `B` is allowed to cover both the
ambient Fourier scale and the translated physical `tau` window.  Its
smoothing scale is therefore the exact `B / Q`; in the source-normalized
application below we take `B = T Q + 4 Q M₂ / (8 M₃)`, so `B / Q ≥ T`
and the finite support margin only improves. -/
theorem exists_integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_J_at_cutoff
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (n : ℕ)
    {T Q B : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hB : 0 < B)
    (hQB : Q ≤ B)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f)
    (hdecay : GMAffineFourierDecayAt T f)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hwidth : 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) ≤ B) :
    ∃ Cdiv Ctail : ℝ, 0 < Cdiv ∧ 0 ≤ Ctail ∧
      (∫ xi in gmAffineMiddleFrequencyRegion
          (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
        2 *
          (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
            (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
          ((32 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
            (Q * (16 * (M₂ : ℝ) ^ 2 *
              ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
                (Real.sqrt (∫ u : ℝ, f u ^ 2) *
                  Real.sqrt (gmAffineJ
                    (gmAffineTildeSchwartz (B / Q) (by positivity) f) M₂)) +
              16 * (M₂ : ℝ) ^ 2 *
                ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
                  gmAffineMiddleFarBound n B Q M₂ *
                    (∫ u : ℝ, |f u|) ^ 2) +
              ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
                4 * Q *
                (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
                  (Ctail * T ^ epsilon * (2 * T / B) ^ n *
                    SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2)) +
        4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 := by
  obtain ⟨Cdiv, Ctail, hCdiv, hCtail, hmiddle⟩ :=
    exists_integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_source_tails
      hepsilon n hT f hdecay hM₁ hM₂ hM₃ hQ hY hB hwidth
  refine ⟨Cdiv, Ctail, hCdiv, hCtail, hmiddle.trans ?_⟩
  have hsigma := norm_gmAffineSigmaIIReal_le_J_add_far
    n hB hQ (show 0 < (8 * M₃ : ℝ) by positivity)
      hQB hM₂ f hf hsupp
  let D : ℝ := Cdiv *
    (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let K : ℝ := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · exact add_le_add hsigma le_rfl
      · exact hK
    · positivity
  · exact le_rfl

theorem gmAffineFirstPoissonRadius_le_of_scale
    {M M₁ M₃ : ℕ} (hM₁M : M₁ ≤ M) (hM₃ : 0 < M₃)
    {Q Y : ℝ} (hQ : 0 ≤ Q) (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    gmAffineFirstPoissonRadius M₁ M₃ Q ≤ Y := by
  have hM₁Real : (M₁ : ℝ) ≤ M := by exact_mod_cast hM₁M
  have hM₃Real : (1 : ℝ) ≤ M₃ := by exact_mod_cast hM₃
  have hnum : Q * (2 * M₁ : ℝ) ≤ Q * (2 * M : ℝ) := by
    gcongr
  have hden : (8 : ℝ) ≤ (8 * M₃ : ℝ) := by
    norm_num at hM₃Real ⊢
    nlinarith
  unfold gmAffineFirstPoissonRadius
  calc
    Q * (2 * M₁ : ℝ) / (8 * M₃ : ℝ) ≤
        Q * (2 * M : ℝ) / (8 * M₃ : ℝ) := by
      gcongr
    _ ≤ Q * (2 * M : ℝ) / 8 := by
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = Q * (M : ℝ) / 4 := by ring
    _ ≤ Y := by linarith

/- Equation-(9.2)--(9.5) decomposition at the scale triple attaining
the finite supremum `J`.  This public bridge prevents the later
iteration from reasoning about an unrelated triple. -/
theorem exists_gmAffineJ_le_explicit_frequency_regions
    (n : ℕ) (hn : 1 ≤ n) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) {M : ℕ} (hM : 0 < M)
    {Q Y : ℝ} (hQ : 0 < Q) (hY : 0 < Y)
    (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    ∃ M₁ M₂ M₃ : ℕ,
      (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
      gmAffineJ f M ≤
        2 * gmAffineFirstPoissonRadius M₁ M₃ Q *
          (gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
            gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 +
        (∫ xi in gmAffineMiddleFrequencyRegion
            (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
          ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) +
        (gmAffineFourierDecayEnvelope n f M₁ M₂ M₃ Q) ^ 2 *
          (2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
            ((-(2 * (n : ℝ))) + 1))) := by
  obtain ⟨M₁, M₂, M₃, hscale, hEq⟩ :=
    exists_gmAffineTransformIntegral_eq_J f hM
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨hM₁, hM₁M, hM₂, hM₂M, hM₃, hM₃M⟩
  refine ⟨M₁, M₂, M₃, hscale, ?_⟩
  let X : ℝ := gmAffineFirstPoissonRadius M₁ M₃ Q
  have hX : 0 ≤ X := by
    dsimp only [X]
    unfold gmAffineFirstPoissonRadius
    positivity
  have hXY : X ≤ Y :=
    gmAffineFirstPoissonRadius_le_of_scale hM₁M hM₃ hQ.le hQMY
  have hentry := gmAffineTransformIntegral_le_smooth_fourier
    f hf hM₁ hM₂ hM₃
  have hregions := integral_gmAffineSmoothTransform_fourier_sq_eq_regions
    f M₁ M₂ M₃ hXY
  have hlow := integral_gmAffineLowFrequencyRegion_fourier_sq_le
    n f hM₁ hM₂ hM₃ hQ hX
  have hhigh := integral_gmAffineHighFrequencyRegion_fourier_sq_le
    n hn f hM₁ hM₂ hM₃ hQ hY
  rw [← hEq]
  refine hentry.trans ?_
  rw [hregions]
  exact add_le_add (add_le_add hlow le_rfl) hhigh

/- The explicit Region-I Poisson envelope at the source scale. -/
theorem gmAffineFirstPoissonRegionI_le_source_scale
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₁M : M₁ ≤ M)
    (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) (hM₃M : M₃ ≤ M)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    2 * gmAffineFirstPoissonRadius M₁ M₃ Q *
        (gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
          gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 ≤
      (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
        (∫ x : ℝ, f x) ^ 2 := by
  have henv := gmAffinePoissonEnvelopes_le_mass
    n f hf hM₁ hM₂ hM₃ hQ
  have hC : 0 ≤ gmAffineRegionIConstant n := gmAffineRegionIConstant_nonneg n
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  have hM₁r : (M₁ : ℝ) ≤ M := by exact_mod_cast hM₁M
  have hM₂r : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
  have hM₃r : (M₃ : ℝ) ≤ M := by exact_mod_cast hM₃M
  have hM₃pos : (0 : ℝ) < M₃ := by exact_mod_cast hM₃
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have henvNonneg : 0 ≤
      gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
        gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q := by
    have htsum : 0 ≤ ∑' j : ℤ, gmIntDecayProfile 2 j :=
      tsum_nonneg fun j => by
        simp only [gmIntDecayProfile]
        split_ifs <;> positivity
    apply add_nonneg
    · unfold gmAffinePoissonMainEnvelope
      positivity
    · unfold gmAffinePoissonFarEnvelope
      positivity
  have hscale :
      (M₁ : ℝ) * (M₂ : ℝ) ^ 4 * M₃ ≤ (M : ℝ) ^ 6 := by
    calc
      (M₁ : ℝ) * (M₂ : ℝ) ^ 4 * M₃ ≤
          (M : ℝ) * (M : ℝ) ^ 4 * M := by gcongr
      _ = (M : ℝ) ^ 6 := by ring
  calc
    2 * gmAffineFirstPoissonRadius M₁ M₃ Q *
        (gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
          gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 ≤
      2 * gmAffineFirstPoissonRadius M₁ M₃ Q *
        (gmAffineRegionIConstant n * Q * (M₂ : ℝ) ^ 2 * M₃ *
          (∫ x : ℝ, f x)) ^ 2 := by gcongr
    _ = (1 / 2 : ℝ) * ((gmAffineRegionIConstant n) ^ 2 * Q ^ 3 *
          ((M₁ : ℝ) * (M₂ : ℝ) ^ 4 * M₃) *
            (∫ x : ℝ, f x) ^ 2) := by
      unfold gmAffineFirstPoissonRadius
      field_simp [hM₃pos.ne']
      ring
    _ ≤ (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 *
          ((M₁ : ℝ) * (M₂ : ℝ) ^ 4 * M₃) *
            (∫ x : ℝ, f x) ^ 2 := by
      have htarget : 0 ≤ (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 *
          ((M₁ : ℝ) * (M₂ : ℝ) ^ 4 * M₃) *
            (∫ x : ℝ, f x) ^ 2 := by positivity
      linarith
    _ ≤ (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
          (∫ x : ℝ, f x) ^ 2 := by gcongr

/- The exact three-region decomposition with Region I already collapsed to
the source scale `Q³ M⁶ ‖f‖₁²`.  The selected triple is still the literal
triple attaining `gmAffineJ`; Region II and Region III remain the actual
Fourier integrals for that triple. -/
theorem exists_gmAffineJ_le_source_regionI_add_middle_add_high
    (n : ℕ) (hn : 1 ≤ n) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M : ℕ} (hM : 0 < M)
    {Q Y : ℝ} (hQ : 1 ≤ Q) (hY : 0 < Y)
    (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    ∃ M₁ M₂ M₃ : ℕ,
      (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
      gmAffineJ f M ≤
        (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
            (∫ x : ℝ, f x) ^ 2 +
          (∫ xi in gmAffineMiddleFrequencyRegion
              (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
            ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) +
          (gmAffineFourierDecayEnvelope n f M₁ M₂ M₃ Q) ^ 2 *
            (2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
              ((-(2 * (n : ℝ))) + 1))) := by
  obtain ⟨M₁, M₂, M₃, hscale, hbound⟩ :=
    exists_gmAffineJ_le_explicit_frequency_regions
      n hn f hf hM (zero_lt_one.trans_le hQ) hY hQMY
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨hM₁, hM₁M, hM₂, hM₂M, hM₃, hM₃M⟩
  refine ⟨M₁, M₂, M₃, hscale, hbound.trans ?_⟩
  have hlow := gmAffineFirstPoissonRegionI_le_source_scale
    n f hf hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hQ
  exact add_le_add (add_le_add hlow le_rfl) le_rfl

/-! ### Source-faithful cutoff and the complete raw Lemma 9.2 recurrence -/

/- The second-Poisson cutoff covers both the ambient Fourier scale and
the full translated first-Poisson window. -/
noncomputable def gmAffineSecondPoissonCutoff
    (T Q : ℝ) (M₂ M₃ : ℕ) : ℝ :=
  T * Q + 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ)

theorem gmAffineSecondPoissonCutoff_pos
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    {M₂ M₃ : ℕ} :
    0 < gmAffineSecondPoissonCutoff T Q M₂ M₃ := by
  unfold gmAffineSecondPoissonCutoff
  positivity

theorem gmAffineSecondPoissonCutoff_width
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    {M₂ M₃ : ℕ} :
    4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) ≤
      gmAffineSecondPoissonCutoff T Q M₂ M₃ := by
  unfold gmAffineSecondPoissonCutoff
  have hTQ : 0 < T * Q := mul_pos hT hQ
  linarith

theorem gmAffineSecondPoissonCutoff_ge_Q
    {T Q : ℝ} (hT : 1 ≤ T) (hQ : 0 ≤ Q) {M₂ M₃ : ℕ} :
    Q ≤ gmAffineSecondPoissonCutoff T Q M₂ M₃ := by
  unfold gmAffineSecondPoissonCutoff
  have hratio : 0 ≤ 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hT hQ]

theorem gmAffineSecondPoissonSmoothingScale_ge
    {T Q : ℝ} (hQ : 0 < Q) {M₂ M₃ : ℕ} :
    T ≤ gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q := by
  unfold gmAffineSecondPoissonCutoff
  rw [add_div, mul_div_cancel_right₀ T hQ.ne']
  have hratio : 0 ≤ 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) := by positivity
  exact le_add_of_nonneg_right (div_nonneg hratio hQ.le)

/- The source Fourier tail outside the enlarged second-Poisson window
retains arbitrary-order decay in the first window `Q`. -/
theorem two_mul_T_div_gmAffineSecondPoissonCutoff_le
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) {M₂ M₃ : ℕ} :
    2 * T / gmAffineSecondPoissonCutoff T Q M₂ M₃ ≤ 2 / Q := by
  have hB : 0 < gmAffineSecondPoissonCutoff T Q M₂ M₃ :=
    gmAffineSecondPoissonCutoff_pos hT hQ
  rw [div_le_div_iff₀ hB hQ]
  unfold gmAffineSecondPoissonCutoff
  have hratio : 0 ≤ 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) := by positivity
  nlinarith

/- The enlarged cutoff has only the polynomial size used in the
arbitrary-order tail absorption. -/
theorem gmAffineSecondPoissonCutoff_div_scale_le
    {T Q : ℝ} (hT : 1 ≤ T) (hQ : 0 < Q)
    {M₂ M₃ : ℕ} (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) :
    gmAffineSecondPoissonCutoff T Q M₂ M₃ / M₂ ≤ 2 * T * Q := by
  have hM₂r : (1 : ℝ) ≤ M₂ := by exact_mod_cast hM₂
  have hM₃r : (1 : ℝ) ≤ M₃ := by exact_mod_cast hM₃
  have hTQ : 0 ≤ T * Q := mul_nonneg (zero_le_one.trans hT) hQ.le
  have hfirst : T * Q / (M₂ : ℝ) ≤ T * Q :=
    div_le_self hTQ hM₂r
  have hsecondEq :
      (4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ)) / (M₂ : ℝ) =
        Q / (2 * M₃ : ℝ) := by field_simp <;> ring
  have hsecond : Q / (2 * M₃ : ℝ) ≤ T * Q := by
    have hden : (1 : ℝ) ≤ 2 * M₃ := by nlinarith
    calc
      Q / (2 * M₃ : ℝ) ≤ Q := div_le_self hQ.le hden
      _ ≤ T * Q := by nlinarith [mul_le_mul_of_nonneg_right hT hQ.le]
  unfold gmAffineSecondPoissonCutoff
  rw [add_div, hsecondEq]
  linarith

/- Fixed Schwartz constant controlling the two pieces of the omitted
second-Poisson lattice after the source scale inequalities are applied. -/
noncomputable def gmAffineMiddleFarSourceConstant (n : ℕ) : ℝ :=
  4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual *
      (∑' k : ℤ, gmIntDecayProfile 2 k) +
    4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual

theorem gmAffineMiddleFarSourceConstant_nonneg (n : ℕ) :
    0 ≤ gmAffineMiddleFarSourceConstant n := by
  have hsum : 0 ≤ ∑' k : ℤ, gmIntDecayProfile 2 k :=
    tsum_nonneg fun k => by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
  unfold gmAffineMiddleFarSourceConstant
  positivity

/- Quantitative absorption of the complete omitted second-Poisson
series.  This is where the paper's preliminary reduction `M ≤ T⁴` is
used: the reciprocal scaled cutoff costs at most `T³`, while the direct
scaled cutoff costs only `T`. -/
theorem gmAffineMiddleFarBound_at_source_cutoff_le
    (n : ℕ) {T Q : ℝ} (hT : 1 ≤ T) (hQ : 0 < Q)
    {M M₂ M₃ : ℕ} (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hM₂M : M₂ ≤ M) (hMT : (M : ℝ) ≤ T ^ 4) :
    gmAffineMiddleFarBound n
        (gmAffineSecondPoissonCutoff T Q M₂ M₃) Q M₂ ≤
      gmAffineMiddleFarSourceConstant n * T ^ 3 / Q ^ (n + 1) := by
  let S : ℝ := SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual
  let Z : ℝ := ∑' k : ℤ, gmIntDecayProfile 2 k
  let B : ℝ := gmAffineSecondPoissonCutoff T Q M₂ M₃
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hM₂scale : (M₂ : ℝ) ≤ T ^ 4 :=
    (by exact_mod_cast hM₂M : (M₂ : ℝ) ≤ M) |>.trans hMT
  have hBpos : 0 < B := by
    dsimp only [B]
    exact gmAffineSecondPoissonCutoff_pos hTpos hQ
  have hBbase : T * Q ≤ B := by
    dsimp only [B]
    unfold gmAffineSecondPoissonCutoff
    have hr : 0 ≤ 4 * Q * (M₂ : ℝ) / (8 * M₃ : ℝ) := by positivity
    linarith
  have hBdivLower : T * Q / (M₂ : ℝ) ≤ B / M₂ :=
    div_le_div_of_nonneg_right hBbase hM₂r.le
  have hBdivPos : 0 < B / (M₂ : ℝ) := div_pos hBpos hM₂r
  have hBdivUpper : B / (M₂ : ℝ) ≤ 2 * T * Q := by
    dsimp only [B]
    exact gmAffineSecondPoissonCutoff_div_scale_le hT hQ hM₂ hM₃
  have htarget : Q ≤ T ^ 3 * (B / (M₂ : ℝ)) := by
    have hratio : (1 : ℝ) ≤ T ^ 4 / (M₂ : ℝ) := by
      rw [le_div_iff₀ hM₂r]
      simpa only [one_mul] using hM₂scale
    calc
      Q ≤ Q * (T ^ 4 / (M₂ : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hratio hQ.le]
      _ = T ^ 3 * (T * Q / (M₂ : ℝ)) := by
        field_simp [hM₂r.ne']
      _ ≤ T ^ 3 * (B / (M₂ : ℝ)) := by gcongr
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact tsum_nonneg fun k => by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
  have hfirst :
      4 * S / ((B / (M₂ : ℝ)) * Q ^ n) ≤
        4 * S * T ^ 3 / Q ^ (n + 1) := by
    have hden : 0 < (B / (M₂ : ℝ)) * Q ^ n :=
      mul_pos hBdivPos (pow_pos hQ n)
    rw [div_le_div_iff₀ hden (pow_pos hQ (n + 1))]
    calc
      4 * S * Q ^ (n + 1) = (4 * S * Q ^ n) * Q := by
        rw [pow_succ]
        ring
      _ ≤ (4 * S * Q ^ n) * (T ^ 3 * (B / (M₂ : ℝ))) := by
        gcongr
      _ = 4 * S * T ^ 3 * ((B / (M₂ : ℝ)) * Q ^ n) := by ring
  have hTcube : T ≤ T ^ 3 := by nlinarith [sq_nonneg (T - 1)]
  have hsecond :
      2 * ((B / (M₂ : ℝ)) * S / Q ^ (n + 2)) ≤
        4 * S * T ^ 3 / Q ^ (n + 1) := by
    calc
      2 * ((B / (M₂ : ℝ)) * S / Q ^ (n + 2)) ≤
          2 * ((2 * T * Q) * S / Q ^ (n + 2)) := by gcongr
      _ = 4 * S * T / Q ^ (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        field_simp [hQ.ne']
        ring
      _ ≤ 4 * S * T ^ 3 / Q ^ (n + 1) := by gcongr
  unfold gmAffineMiddleFarBound
  change (4 * S / ((B / (M₂ : ℝ)) * Q ^ n)) * Z +
      2 * ((B / (M₂ : ℝ)) * S / Q ^ (n + 2)) ≤ _
  calc
    (4 * S / ((B / (M₂ : ℝ)) * Q ^ n)) * Z +
        2 * ((B / (M₂ : ℝ)) * S / Q ^ (n + 2)) ≤
      (4 * S * T ^ 3 / Q ^ (n + 1)) * Z +
        4 * S * T ^ 3 / Q ^ (n + 1) := by gcongr
    _ = gmAffineMiddleFarSourceConstant n * T ^ 3 / Q ^ (n + 1) := by
      dsimp only [S, Z]
      unfold gmAffineMiddleFarSourceConstant
      ring

/- The apparent product-window cardinality factor cancels the outer
`M₃` scale.  This is the exact finite substitute for the paper's
`1 + M₁/M₃` count in Region II. -/
theorem gmAffineFirstPoissonRadius_card_factor_mul_scale_le
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) * (M₃ : ℝ) ≤
      4 * Q * ((M₁ : ℝ) + M₃) := by
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₃r : (0 : ℝ) < M₃ := by exact_mod_cast hM₃
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  unfold gmAffineFirstPoissonRadius
  field_simp [hM₃r.ne']
  nlinarith [mul_nonneg hQ0 hM₁r.le,
    mul_le_mul_of_nonneg_right hQ hM₃r.le]

/- A uniform polynomial bound for the fixed first-frequency range.  It
is used only on the rapidly decaying omitted piece, so retaining the
harmless `Y + Q + 1` factor is both source-faithful and sufficient. -/
theorem card_gmAffineFirstPoissonEllRange_real_le_source
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q Y : ℝ} (hQ : 0 ≤ Q) (hY : 0 ≤ Y) :
    ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) ≤
      3 * (Y + Q + 1) := by
  have hM₁r : (1 : ℝ) ≤ M₁ := by exact_mod_cast hM₁
  have hM₃r : (1 : ℝ) ≤ M₃ := by exact_mod_cast hM₃
  have hYdiv : Y / (M₁ : ℝ) ≤ Y := div_le_self hY hM₁r
  have hQdiv : Q / (8 * M₃ : ℝ) ≤ Q := by
    have hden : (1 : ℝ) ≤ 8 * M₃ := by nlinarith
    exact div_le_self hQ hden
  refine (card_gmAffineFirstPoissonEllRange_real_le hM₁ hM₃ hQ hY).trans ?_
  unfold gmAffineFirstPoissonEllRadius
  nlinarith

/- The positive dyadic shell has at most twice its physical scale.
This elementary casted form is used repeatedly in the source tail
bookkeeping below. -/
theorem card_gmAffinePositiveShell_real_le_two_mul
    {M : ℕ} (hM : 0 < M) :
    ((gmAffinePositiveShell M).card : ℝ) ≤ 2 * M := by
  have hcard : (gmAffinePositiveShell M).card ≤ 2 * M := by
    rw [card_gmAffinePositiveShell]
    omega
  exact_mod_cast hcard

/- The common Region-II prefactor after the first-frequency cardinality
is combined with the outer `M₃` scale.  This is the quantitative form of
the cancellation `M₃ (1 + M₁/M₃) ≪ M` in Lemma 9.2. -/
theorem gmAffineRegionIIPrefactor_le
    {epsilon Q Y Cdiv : ℝ} (hQ : 1 ≤ Q) (hY : 0 ≤ Y)
    {M M₁ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₁M : M₁ ≤ M)
    (hM₃ : 0 < M₃) (hM₃M : M₃ ≤ M)
    (hCdiv : 0 ≤ Cdiv) :
    2 *
        (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
        ((32 * M₃ : ℝ) *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) ≤
      512 * Cdiv *
        (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon * Q * M *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 := by
  let A : ℝ :=
    (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon
  let L : ℝ := SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact Real.rpow_nonneg (add_nonneg hY hR) epsilon
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hfactor := gmAffineFirstPoissonRadius_card_factor_mul_scale_le
    hM₁ hM₃ hQ
  have hsum : (M₁ : ℝ) + M₃ ≤ 2 * M := by
    exact_mod_cast
      (Nat.add_le_add hM₁M hM₃M |>.trans (by omega : M + M ≤ 2 * M))
  have hpair :
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) * (M₃ : ℝ) ≤
        8 * Q * M := by
    calc
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) * (M₃ : ℝ) ≤
          4 * Q * ((M₁ : ℝ) + M₃) := hfactor
      _ ≤ 4 * Q * (2 * M) := by gcongr
      _ = 8 * Q * M := by ring
  change 2 * (Cdiv * A *
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
      ((32 * M₃ : ℝ) * L ^ 2) ≤
    512 * Cdiv * A * Q * M * L ^ 2
  rw [show
    2 * (Cdiv * A *
        (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
        ((32 * M₃ : ℝ) * L ^ 2) =
      64 * Cdiv * A * L ^ 2 *
        ((2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) * M₃) by ring]
  calc
    64 * Cdiv * A * L ^ 2 *
        ((2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) * M₃) ≤
      64 * Cdiv * A * L ^ 2 * (8 * Q * M) := by gcongr
    _ = 512 * Cdiv * A * Q * M * L ^ 2 := by ring

/- The omitted second-Poisson lattice in Region II, before multiplication
by the common Region-II prefactor.  The derivative order `n` is retained
as the explicit negative power `Q⁻⁽ⁿ⁺¹⁾`. -/
theorem gmAffineRegionIISecondPoissonTail_le
    (n : ℕ) (f : SchwartzMap ℝ ℝ)
    {T Q : ℝ} (hT : 1 ≤ T) (hQ : 0 < Q)
    {M M₂ M₃ : ℕ} (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) (hMT : (M : ℝ) ≤ T ^ 4) :
    16 * (M₂ : ℝ) ^ 2 *
        ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
        gmAffineMiddleFarBound n
          (gmAffineSecondPoissonCutoff T Q M₂ M₃) Q M₂ *
        (∫ u : ℝ, |f u|) ^ 2 ≤
      64 * gmAffineMiddleFarSourceConstant n * T ^ 3 /
          Q ^ (n + 1) * (M : ℝ) ^ 4 * (∫ u : ℝ, |f u|) ^ 2 := by
  have hcard := card_gmAffinePositiveShell_real_le_two_mul hM₂
  have hfar := gmAffineMiddleFarBound_at_source_cutoff_le
    n hT hQ hM₂ hM₃ hM₂M hMT
  have hM₂r : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
  have hM₂nonneg : (0 : ℝ) ≤ M₂ := Nat.cast_nonneg _
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hscale : (M₂ : ℝ) ^ 4 ≤ (M : ℝ) ^ 4 :=
    pow_le_pow_left₀ hM₂nonneg hM₂r 4
  have hmass : 0 ≤ ∫ u : ℝ, |f u| :=
    integral_nonneg fun u => abs_nonneg (f u)
  have hC : 0 ≤ gmAffineMiddleFarSourceConstant n :=
    gmAffineMiddleFarSourceConstant_nonneg n
  have hmiddleNonneg : 0 ≤ gmAffineMiddleFarBound n
      (gmAffineSecondPoissonCutoff T Q M₂ M₃) Q M₂ :=
    gmAffineMiddleFarBound_nonneg n
      (gmAffineSecondPoissonCutoff_pos (zero_lt_one.trans_le hT) hQ)
      hQ hM₂
  calc
    16 * (M₂ : ℝ) ^ 2 *
        ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
        gmAffineMiddleFarBound n
          (gmAffineSecondPoissonCutoff T Q M₂ M₃) Q M₂ *
        (∫ u : ℝ, |f u|) ^ 2 ≤
      16 * (M₂ : ℝ) ^ 2 * (2 * M₂ : ℝ) ^ 2 *
        (gmAffineMiddleFarSourceConstant n * T ^ 3 / Q ^ (n + 1)) *
        (∫ u : ℝ, |f u|) ^ 2 := by gcongr
    _ = 64 * gmAffineMiddleFarSourceConstant n * T ^ 3 /
        Q ^ (n + 1) * (M₂ : ℝ) ^ 4 * (∫ u : ℝ, |f u|) ^ 2 := by ring
    _ ≤ 64 * gmAffineMiddleFarSourceConstant n * T ^ 3 /
        Q ^ (n + 1) * (M : ℝ) ^ 4 * (∫ u : ℝ, |f u|) ^ 2 := by
      gcongr

/- The first-Poisson omitted lattice occurring outside the middle
frequency estimate.  Squaring preserves the full `Q⁻²ⁿ` saving. -/
theorem gmAffineRegionIIHighTail_le
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {Q Y : ℝ} (hQ : 1 ≤ Q) (hY : 0 ≤ Y)
    {M M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) (hM₃M : M₃ ≤ M) :
    4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 ≤
      4 * Y *
        (gmAffineRegionIFarConstant n * (M : ℝ) ^ 3 *
          (∫ x : ℝ, f x) / Q ^ n) ^ 2 := by
  have hfar := gmAffinePoissonFarEnvelope_le_mass_div_pow
    n f hf hM₁ hM₂ hM₃ hQ
  have hM₂r : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
  have hM₃r : (M₃ : ℝ) ≤ M := by exact_mod_cast hM₃M
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hmass : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hf
  have hscale : (M₂ : ℝ) ^ 2 * M₃ ≤ (M : ℝ) ^ 3 := by
    calc
      (M₂ : ℝ) ^ 2 * M₃ ≤ (M : ℝ) ^ 2 * M := by gcongr
      _ = (M : ℝ) ^ 3 := by ring
  have hfar' :
      gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q ≤
        gmAffineRegionIFarConstant n * (M : ℝ) ^ 3 *
          (∫ x : ℝ, f x) / Q ^ n := by
    refine hfar.trans ?_
    have hC : 0 ≤ gmAffineRegionIFarConstant n :=
      gmAffineRegionIFarConstant_nonneg n
    have hnum :
        gmAffineRegionIFarConstant n * (M₂ : ℝ) ^ 2 * M₃ *
            (∫ x : ℝ, f x) ≤
          gmAffineRegionIFarConstant n * (M : ℝ) ^ 3 *
            (∫ x : ℝ, f x) := by
      calc
        gmAffineRegionIFarConstant n * (M₂ : ℝ) ^ 2 * M₃ *
            (∫ x : ℝ, f x) =
          gmAffineRegionIFarConstant n * ((M₂ : ℝ) ^ 2 * M₃) *
            (∫ x : ℝ, f x) := by ring
        _ ≤ gmAffineRegionIFarConstant n * (M : ℝ) ^ 3 *
            (∫ x : ℝ, f x) := by gcongr
    exact div_le_div_of_nonneg_right hnum
      (pow_nonneg (zero_le_one.trans hQ) n)
  have hfarNonneg :
      0 ≤ gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q := by
    have hsum : 0 ≤ ∑' j : ℤ, gmIntDecayProfile 2 j :=
      tsum_nonneg fun j => by
        unfold gmIntDecayProfile
        split_ifs <;> positivity
    unfold gmAffinePoissonFarEnvelope
    positivity
  have hsquare := pow_le_pow_left₀ hfarNonneg hfar' 2
  exact mul_le_mul_of_nonneg_left hsquare (mul_nonneg (by norm_num) hY)

/- The omitted Fourier modes from the second Poisson step.  The enlarged
cutoff is used only through the proved comparison `2T/B ≤ 2/Q`; all finite
shell and first-frequency losses are displayed explicitly. -/
theorem gmAffineRegionIIFirstPoissonTail_le
    (n : ℕ) {epsilon T Q Y Ctail : ℝ}
    (hT : 0 < T) (hQ : 1 ≤ Q) (hY : 0 ≤ Y) (hCtail : 0 ≤ Ctail)
    (f : SchwartzMap ℝ ℝ)
    {M M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) :
    ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
        4 * Q *
        (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
          (Ctail * T ^ epsilon *
            (2 * T / gmAffineSecondPoissonCutoff T Q M₂ M₃) ^ n *
            SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2 ≤
      192 * (Y + Q + 1) * Q * (M : ℝ) ^ 4 *
        (Ctail * T ^ epsilon * (2 / Q) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) ^ 2 := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hcardEll := card_gmAffineFirstPoissonEllRange_real_le_source
    hM₁ hM₃ (zero_le_one.trans hQ) hY
  have hcard := card_gmAffinePositiveShell_real_le_two_mul hM₂
  have hratio := two_mul_T_div_gmAffineSecondPoissonCutoff_le
    hT hQpos (M₂ := M₂) (M₃ := M₃)
  have hBpos : 0 < gmAffineSecondPoissonCutoff T Q M₂ M₃ :=
    gmAffineSecondPoissonCutoff_pos hT hQpos
  have hratioNonneg :
      0 ≤ 2 * T / gmAffineSecondPoissonCutoff T Q M₂ M₃ := by
    exact div_nonneg (mul_nonneg (by norm_num) hT.le) hBpos.le
  have hratioPow :
      (2 * T / gmAffineSecondPoissonCutoff T Q M₂ M₃) ^ n ≤
        (2 / Q) ^ n :=
    pow_le_pow_left₀ hratioNonneg hratio n
  let Z₀ : ℝ := Ctail * T ^ epsilon *
    (2 * T / gmAffineSecondPoissonCutoff T Q M₂ M₃) ^ n *
      SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)
  let Z : ℝ := Ctail * T ^ epsilon * (2 / Q) ^ n *
    SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)
  have hZ₀ : 0 ≤ Z₀ := by dsimp only [Z₀]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hZZ : Z₀ ≤ Z := by
    dsimp only [Z₀, Z]
    gcongr
  have hinsideNonneg :
      0 ≤ ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * Z₀ := by
    positivity
  have hinside :
      ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * Z₀ ≤
        4 * (M₂ : ℝ) ^ 2 * Z := by
    calc
      ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * Z₀ ≤
          (2 * M₂ : ℝ) * (2 * M₂ : ℝ) * Z := by gcongr
      _ = 4 * (M₂ : ℝ) ^ 2 * Z := by ring
  have hsq := pow_le_pow_left₀ hinsideNonneg hinside 2
  have hM₂r : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
  have hM₂nonneg : (0 : ℝ) ≤ M₂ := Nat.cast_nonneg _
  have hscale : (M₂ : ℝ) ^ 4 ≤ (M : ℝ) ^ 4 :=
    pow_le_pow_left₀ hM₂nonneg hM₂r 4
  change ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
      4 * Q *
        (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * Z₀) ^ 2 ≤
    192 * (Y + Q + 1) * Q * (M : ℝ) ^ 4 * Z ^ 2
  calc
    ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
        4 * Q *
          (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * Z₀) ^ 2 ≤
      (3 * (Y + Q + 1)) * 4 * Q *
        (4 * (M₂ : ℝ) ^ 2 * Z) ^ 2 := by gcongr
    _ = 192 * (Y + Q + 1) * Q * (M₂ : ℝ) ^ 4 * Z ^ 2 := by ring
    _ ≤ 192 * (Y + Q + 1) * Q * (M : ℝ) ^ 4 * Z ^ 2 := by
      gcongr

/- The literal right side produced for Region II after both Poisson
expansions.  It is kept as a named expression so subsequent power
bookkeeping can be audited without duplicating the analytic formula. -/
noncomputable def gmAffineRegionIIRawBound
    (epsilon : ℝ) (n : ℕ) (T Q Y : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ)
    (M₁ M₂ M₃ : ℕ) (Cdiv Ctail : ℝ) : ℝ :=
  let B := gmAffineSecondPoissonCutoff T Q M₂ M₃
  let D := Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
    (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let K := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  let I := 16 * (M₂ : ℝ) ^ 2 *
    ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
      (Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ
          (gmAffineTildeSchwartz (B / Q) (by
            unfold B gmAffineSecondPoissonCutoff
            positivity) f) M₂))
  let E := 16 * (M₂ : ℝ) ^ 2 *
    ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
      gmAffineMiddleFarBound n B Q M₂ * (∫ u : ℝ, |f u|) ^ 2
  let P := ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
    4 * Q *
      (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
        (Ctail * T ^ epsilon * (2 * T / B) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2
  2 * D * K * (Q * (I + E) + P) +
    4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2

/- The literal affine-energy core of the Region-II expression. -/
noncomputable def gmAffineRegionIICoreRawBound
    (epsilon T Q Y : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (Cdiv : ℝ) : ℝ :=
  let B := gmAffineSecondPoissonCutoff T Q M₂ M₃
  let D := Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
    (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let K := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  let I := 16 * (M₂ : ℝ) ^ 2 *
    ((Q / M₂) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) *
      (Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ
          (gmAffineTildeSchwartz (B / Q) (by
            unfold B gmAffineSecondPoissonCutoff
            positivity) f) M₂))
  2 * D * (K * (Q * I))

/- All omitted-lattice and high-frequency terms remaining after the
affine-energy core is removed from Region II. -/
noncomputable def gmAffineRegionIITailRawBound
    (epsilon : ℝ) (n : ℕ) (T Q Y : ℝ) (f : SchwartzMap ℝ ℝ)
    (M₁ M₂ M₃ : ℕ) (Cdiv Ctail : ℝ) : ℝ :=
  let B := gmAffineSecondPoissonCutoff T Q M₂ M₃
  let D := Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
    (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let K := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  let E := 16 * (M₂ : ℝ) ^ 2 *
    ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
      gmAffineMiddleFarBound n B Q M₂ * (∫ u : ℝ, |f u|) ^ 2
  let P := ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) *
    4 * Q *
      (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
        (Ctail * T ^ epsilon * (2 * T / B) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2
  2 * D * K * (Q * E + P) +
    4 * Y * (gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2

/- Polynomial majorant for every omitted term in Region II.  Its three
summands are, in order, the second-Poisson lattice tail, the Fourier tail
from the first-frequency range, and the first-Poisson high tail. -/
noncomputable def gmAffineRegionIITailSourceBound
    (epsilon : ℝ) (n : ℕ) (T Q Y : ℝ) (f : SchwartzMap ℝ ℝ)
    (M : ℕ) (Cdiv Ctail : ℝ) : ℝ :=
  (512 * Cdiv *
      (Y + Y) ^ epsilon * Q * M *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
    (Q *
        (64 * gmAffineMiddleFarSourceConstant n * T ^ 3 /
          Q ^ (n + 1) * (M : ℝ) ^ 4 * (∫ u : ℝ, |f u|) ^ 2) +
      192 * (Y + Q + 1) * Q * (M : ℝ) ^ 4 *
        (Ctail * T ^ epsilon * (2 / Q) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) ^ 2) +
    4 * Y *
      (gmAffineRegionIFarConstant n * (M : ℝ) ^ 3 *
        (∫ x : ℝ, f x) / Q ^ n) ^ 2

theorem gmAffineRegionIITailRawBound_le_source
    {epsilon T Q Y Cdiv Ctail : ℝ}
    (n : ℕ)
    (hepsilon : 0 ≤ epsilon)
    (hT : 1 ≤ T) (hQ : 1 ≤ Q) (hY : 0 < Y)
    (hCdiv : 0 ≤ Cdiv) (hCtail : 0 ≤ Ctail)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₁M : M₁ ≤ M)
    (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) (hM₃M : M₃ ≤ M)
    (hMT : (M : ℝ) ≤ T ^ 4)
    (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    gmAffineRegionIITailRawBound epsilon n T Q Y
        f M₁ M₂ M₃ Cdiv Ctail ≤
      gmAffineRegionIITailSourceBound epsilon n T Q Y f M Cdiv Ctail := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  let R : ℝ := gmAffineFirstPoissonRadius M₁ M₃ Q
  let A : ℝ := (Y + R) ^ epsilon
  let A₀ : ℝ := (Y + Y) ^ epsilon
  let L : ℝ := SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual
  let E : ℝ := 16 * (M₂ : ℝ) ^ 2 *
    ((gmAffinePositiveShell M₂).card : ℝ) ^ 2 *
      gmAffineMiddleFarBound n
        (gmAffineSecondPoissonCutoff T Q M₂ M₃) Q M₂ *
          (∫ u : ℝ, |f u|) ^ 2
  let E₀ : ℝ := 64 * gmAffineMiddleFarSourceConstant n * T ^ 3 /
    Q ^ (n + 1) * (M : ℝ) ^ 4 * (∫ u : ℝ, |f u|) ^ 2
  let P : ℝ :=
    ((gmAffineFirstPoissonEllRange M₁ M₃ Q Y).card : ℝ) * 4 * Q *
      (((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
        (Ctail * T ^ epsilon *
          (2 * T / gmAffineSecondPoissonCutoff T Q M₂ M₃) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))) ^ 2
  let P₀ : ℝ := 192 * (Y + Q + 1) * Q * (M : ℝ) ^ 4 *
    (Ctail * T ^ epsilon * (2 / Q) ^ n *
      SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) ^ 2
  let D : ℝ := Cdiv * A * (2 * R + 3)
  let K : ℝ := (32 * M₃ : ℝ) * L ^ 2
  let F : ℝ := 512 * Cdiv * A₀ * Q * M * L ^ 2
  have hRnonneg : 0 ≤ R := by
    dsimp only [R]
    unfold gmAffineFirstPoissonRadius
    positivity
  have hRY : R ≤ Y :=
    gmAffineFirstPoissonRadius_le_of_scale hM₁M hM₃
      (zero_le_one.trans hQ) hQMY
  have hbase : Y + R ≤ Y + Y := by linarith
  have hbasePos : 0 < Y + R := by linarith
  have hbaseTargetPos : 0 < Y + Y := by linarith
  have hAA : A ≤ A₀ := by
    dsimp only [A, A₀]
    exact Real.rpow_le_rpow hbasePos.le hbase hepsilon
  have hANonneg : 0 ≤ A := Real.rpow_nonneg hbasePos.le epsilon
  have hA₀Nonneg : 0 ≤ A₀ := Real.rpow_nonneg hbaseTargetPos.le epsilon
  have hLnonneg : 0 ≤ L := by dsimp only [L]; positivity
  have hprefRaw := gmAffineRegionIIPrefactor_le
    hQ hY.le hM₁ hM₁M hM₃ hM₃M hCdiv (epsilon := epsilon)
  have hpref : 2 * D * K ≤ F := by
    dsimp only [D, K, F, A, A₀, L, R]
    refine hprefRaw.trans ?_
    gcongr
  have hE : E ≤ E₀ := by
    dsimp only [E, E₀]
    exact gmAffineRegionIISecondPoissonTail_le
      n f hT hQpos hM₂ hM₂M hM₃ hMT
  have hP : P ≤ P₀ := by
    dsimp only [P, P₀]
    exact gmAffineRegionIIFirstPoissonTail_le
      n hTpos hQ hY.le hCtail f hM₁ hM₂ hM₂M hM₃
  have hmassAbs : 0 ≤ ∫ u : ℝ, |f u| :=
    integral_nonneg fun u => abs_nonneg (f u)
  have hmiddleNonneg : 0 ≤ gmAffineMiddleFarBound n
      (gmAffineSecondPoissonCutoff T Q M₂ M₃) Q M₂ :=
    gmAffineMiddleFarBound_nonneg n
      (gmAffineSecondPoissonCutoff_pos hTpos hQpos) hQpos hM₂
  have hENonneg : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hPNonneg : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hE₀Nonneg : 0 ≤ E₀ := by
    dsimp only [E₀]
    have hC : 0 ≤ gmAffineMiddleFarSourceConstant n :=
      gmAffineMiddleFarSourceConstant_nonneg n
    positivity
  have hP₀Nonneg : 0 ≤ P₀ := by
    dsimp only [P₀]
    positivity
  have hinner : Q * E + P ≤ Q * E₀ + P₀ := by
    exact add_le_add (mul_le_mul_of_nonneg_left hE (zero_le_one.trans hQ)) hP
  have hinnerTargetNonneg : 0 ≤ Q * E₀ + P₀ :=
    add_nonneg (mul_nonneg (zero_le_one.trans hQ) hE₀Nonneg) hP₀Nonneg
  have hinnerNonneg : 0 ≤ Q * E + P :=
    add_nonneg (mul_nonneg (zero_le_one.trans hQ) hENonneg) hPNonneg
  have hFNonneg : 0 ≤ F := by
    dsimp only [F]
    positivity
  have hmain : 2 * D * K * (Q * E + P) ≤ F * (Q * E₀ + P₀) := by
    calc
      2 * D * K * (Q * E + P) ≤ F * (Q * E + P) :=
        mul_le_mul_of_nonneg_right hpref hinnerNonneg
      _ ≤ F * (Q * E₀ + P₀) :=
        mul_le_mul_of_nonneg_left hinner hFNonneg
  have hhigh := gmAffineRegionIIHighTail_le
    n f hf hQ hY.le hM₁ hM₂ hM₂M hM₃ hM₃M
  unfold gmAffineRegionIITailRawBound gmAffineRegionIITailSourceBound
  dsimp only
  gcongr

theorem gmAffineRegionIIRawBound_eq_core_add_tail
    (epsilon : ℝ) (n : ℕ) {T Q Y : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (Cdiv Ctail : ℝ) :
    gmAffineRegionIIRawBound epsilon n T Q Y hT hQ
        f M₁ M₂ M₃ Cdiv Ctail =
      gmAffineRegionIICoreRawBound epsilon T Q Y hT hQ
          f M₁ M₂ M₃ Cdiv +
        gmAffineRegionIITailRawBound epsilon n T Q Y
          f M₁ M₂ M₃ Cdiv Ctail := by
  unfold gmAffineRegionIIRawBound gmAffineRegionIICoreRawBound
    gmAffineRegionIITailRawBound
  ring

/- The `gmAffineRegionIICoreConstant` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineRegionIICoreConstant : ℝ :=
  8192 * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3

theorem gmAffineRegionIICoreConstant_nonneg :
    0 ≤ gmAffineRegionIICoreConstant := by
  unfold gmAffineRegionIICoreConstant
  positivity

/- Exact polynomial collapse of the retained Region-II core.  The
selected triple is still the one attaining `J`; no independent scale
variables or detached cardinality estimate occur in this theorem. -/
theorem gmAffineRegionIICoreRawBound_le_source
    {epsilon T Q Y : ℝ} (hT : 0 < T) (hQ : 1 ≤ Q) (hY : 0 ≤ Y)
    (f : SchwartzMap ℝ ℝ) {M M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₁M : M₁ ≤ M)
    (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) (hM₃M : M₃ ≤ M)
    {Cdiv : ℝ} (hCdiv : 0 ≤ Cdiv) :
    gmAffineRegionIICoreRawBound epsilon T Q Y hT
        (zero_lt_one.trans_le hQ) f M₁ M₂ M₃ Cdiv ≤
      Cdiv * gmAffineRegionIICoreConstant *
        (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
        Q ^ 3 * (M : ℝ) ^ 2 *
        (Real.sqrt (∫ u : ℝ, f u ^ 2) *
          Real.sqrt (gmAffineJ
            (gmAffineTildeSchwartz
              (gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q)
              (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)) := by
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hwindow : 0 ≤
      (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon := by positivity
  have hfactor := gmAffineFirstPoissonRadius_card_factor_mul_scale_le
    hM₁ hM₃ hQ
  have hsumScale : (M₁ : ℝ) + M₃ ≤ 2 * M := by
    exact_mod_cast (Nat.add_le_add hM₁M hM₃M |>.trans (by omega : M + M ≤ 2 * M))
  have hM₂r : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
  have hscale :
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) * (M₃ : ℝ) *
          (M₂ : ℝ) ≤ 8 * Q * (M : ℝ) ^ 2 := by
    calc
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) * (M₃ : ℝ) *
          (M₂ : ℝ) ≤
        (4 * Q * ((M₁ : ℝ) + M₃)) * (M₂ : ℝ) := by gcongr
      _ ≤ (4 * Q * (2 * M)) * M := by gcongr
      _ = 8 * Q * (M : ℝ) ^ 2 := by ring
  let H : ℝ := Real.sqrt (∫ u : ℝ, f u ^ 2) *
    Real.sqrt (gmAffineJ
      (gmAffineTildeSchwartz
        (gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q)
        (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  unfold gmAffineRegionIICoreRawBound gmAffineRegionIICoreConstant
  dsimp only
  change 2 *
      (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
        (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
      ((32 * M₃ : ℝ) *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        (Q * (16 * (M₂ : ℝ) ^ 2 *
          ((Q / (M₂ : ℝ)) * SchwartzMap.seminorm ℝ 0 0
            gmAffineLocalBumpDual) * H))) ≤
    Cdiv * (8192 * SchwartzMap.seminorm ℝ 0 0
        gmAffineLocalBumpDual ^ 3) *
      (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
      Q ^ 3 * (M : ℝ) ^ 2 * H
  have hM₂pos : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  rw [show
    2 *
        (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
        ((32 * M₃ : ℝ) *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
          (Q * (16 * (M₂ : ℝ) ^ 2 *
            ((Q / (M₂ : ℝ)) * SchwartzMap.seminorm ℝ 0 0
              gmAffineLocalBumpDual) * H))) =
      1024 * Cdiv *
        (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3 * Q ^ 2 *
        ((2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) *
          (M₃ : ℝ) * (M₂ : ℝ)) * H by
      field_simp [hM₂pos.ne']
      ring]
  calc
    1024 * Cdiv *
        (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3 * Q ^ 2 *
        ((2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) *
          (M₃ : ℝ) * (M₂ : ℝ)) * H ≤
      1024 * Cdiv *
        (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3 * Q ^ 2 *
        (8 * Q * (M : ℝ) ^ 2) * H := by gcongr
    _ = Cdiv * (8192 * SchwartzMap.seminorm ℝ 0 0
          gmAffineLocalBumpDual ^ 3) *
        (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
        Q ^ 3 * (M : ℝ) ^ 2 * H := by ring

/-! ### Quantitative Region-III collapse -/

section
variable (n : ℕ)
include n

/- The `gmAffineRegionIIIKernelConstant` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineRegionIIIKernelConstant  : ℝ :=
  42 * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual +
    4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual *
      (∑' j : ℤ, gmIntDecayProfile 2 j) +
    16 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual

theorem gmAffineRegionIIIKernelConstant_nonneg  :
    0 ≤ gmAffineRegionIIIKernelConstant n := by
  have hsum : 0 ≤ ∑' j : ℤ, gmIntDecayProfile 2 j :=
    tsum_nonneg fun j => by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
  unfold gmAffineRegionIIIKernelConstant
  positivity

/- The complete near-plus-omitted Poisson kernel in Region III has only
the source polynomial scale `Q M₃`; arbitrary derivative dependence is
confined to a fixed cutoff constant. -/
theorem gmAffineRegionIIIKernelEnvelope_le
     {M₃ : ℕ} (hM₃ : 0 < M₃) {Q : ℝ} (hQ : 1 ≤ Q) :
    gmAffinePoissonNearKernelEnvelope M₃ Q +
        gmAffinePoissonTailKernelEnvelope n M₃ Q ≤
      gmAffineRegionIIIKernelConstant n * Q * M₃ := by
  have hM₃one : (1 : ℝ) ≤ M₃ := by exact_mod_cast hM₃
  have hM₃pos : (0 : ℝ) < M₃ := by exact_mod_cast hM₃
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  let L : ℝ := SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual
  let S : ℝ := SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual
  let Z : ℝ := ∑' j : ℤ, gmIntDecayProfile 2 j
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact tsum_nonneg fun j => by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
  have hnear :
      gmAffinePoissonNearKernelEnvelope M₃ Q ≤ 42 * Q * M₃ * L := by
    unfold gmAffinePoissonNearKernelEnvelope
    change (2 * (Q / (8 * M₃ : ℝ)) + 5) * ((8 * M₃ : ℝ) * L) ≤ _
    rw [show
      (2 * (Q / (8 * M₃ : ℝ)) + 5) * ((8 * M₃ : ℝ) * L) =
        (((2 * (Q / (8 * M₃ : ℝ)) + 5) * (8 * M₃ : ℝ)) * L) by ring]
    apply mul_le_mul_of_nonneg_right _ hL
    field_simp [hM₃pos.ne']
    nlinarith
  have hQn : (1 : ℝ) ≤ Q ^ n := one_le_pow₀ hQ
  have hQn2 : (1 : ℝ) ≤ Q ^ (n + 2) := one_le_pow₀ hQ
  have htail :
      gmAffinePoissonTailKernelEnvelope n M₃ Q ≤
        Q * M₃ * (4 * S * Z + 16 * S) := by
    unfold gmAffinePoissonTailKernelEnvelope
    change (4 * S / Q ^ n) * Z +
        2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2)) ≤ _
    have hfirst : 4 * S / Q ^ n ≤ 4 * S :=
      div_le_self (by positivity) hQn
    have hsecond : (8 * M₃ : ℝ) * S / Q ^ (n + 2) ≤
        (8 * M₃ : ℝ) * S := div_le_self (by positivity) hQn2
    calc
      (4 * S / Q ^ n) * Z +
          2 * ((8 * M₃ : ℝ) * S / Q ^ (n + 2)) ≤
        (4 * S) * Z + 2 * ((8 * M₃ : ℝ) * S) := by gcongr
      _ ≤ (M₃ : ℝ) * (4 * S * Z + 16 * S) := by
        nlinarith [mul_le_mul_of_nonneg_right hM₃one
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hS) hZ)]
      _ ≤ Q * M₃ * (4 * S * Z + 16 * S) := by
        have hbracket : 0 ≤ 4 * S * Z + 16 * S := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hQ hM₃pos.le]
  dsimp only [L, S, Z] at hnear htail ⊢
  unfold gmAffineRegionIIIKernelConstant
  linarith

section
variable (f : SchwartzMap ℝ ℝ)
include f

/- The `gmAffineRegionIIIEnvelopeConstant` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineRegionIIIEnvelopeConstant
     : ℝ :=
  16 * (2 : ℝ) ^ n *
    SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) *
      gmAffineRegionIIIKernelConstant n

theorem gmAffineRegionIIIEnvelopeConstant_nonneg
     :
    0 ≤ gmAffineRegionIIIEnvelopeConstant n f := by
  unfold gmAffineRegionIIIEnvelopeConstant
  have hkernel := gmAffineRegionIIIKernelConstant_nonneg n
  positivity
end


/- The `gmAffineRegionIIIEnvelopeMassConstant` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineRegionIIIEnvelopeMassConstant
     (D : ℝ) : ℝ :=
  16 * (2 : ℝ) ^ n * D * gmAffineRegionIIIKernelConstant n

/- Polynomial scale of the complete Region-III Fourier envelope.  The
loss `Mⁿ` is harmless because the accompanying high-frequency integral
has scale `Y^(1-2n)` and the source later fixes `Y = T⁶`, `M ≤ T⁴`. -/
theorem gmAffineFourierDecayEnvelope_le_source
     (f : SchwartzMap ℝ ℝ)
    {Q : ℝ} (hQ : 1 ≤ Q)
    {M M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₁M : M₁ ≤ M)
    (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) (hM₃M : M₃ ≤ M) :
    gmAffineFourierDecayEnvelope n f M₁ M₂ M₃ Q ≤
      gmAffineRegionIIIEnvelopeConstant n f * Q * (M : ℝ) ^ (n + 3) := by
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hM₂one : (1 : ℝ) ≤ M₂ := by exact_mod_cast hM₂
  have hM₁Mreal : (M₁ : ℝ) ≤ M := by exact_mod_cast hM₁M
  have hM₂Mreal : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
  have hM₃Mreal : (M₃ : ℝ) ≤ M := by exact_mod_cast hM₃M
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hsignedNat := card_gmAffineSignedShell_le M₁
  have hsigned : ((gmAffineSignedShell M₁).card : ℝ) ≤ 4 * M₁ := by
    exact_mod_cast
      (hsignedNat.trans (by omega : 2 * (M₁ + 1) ≤ 4 * M₁))
  have hpositive := card_gmAffinePositiveShell_real_le_two_mul hM₂
  have hshell :
      ((gmAffineSignedShell M₁).card : ℝ) *
          ((gmAffinePositiveShell M₂).card : ℝ) *
          ((2 * M₂ : ℝ) / M₁) ≤
        16 * (M₂ : ℝ) ^ 2 := by
    calc
      ((gmAffineSignedShell M₁).card : ℝ) *
          ((gmAffinePositiveShell M₂).card : ℝ) *
          ((2 * M₂ : ℝ) / M₁) ≤
        (4 * M₁ : ℝ) * (2 * M₂ : ℝ) * ((2 * M₂ : ℝ) / M₁) := by
          gcongr
      _ = 16 * (M₂ : ℝ) ^ 2 := by
        field_simp [hM₁r.ne']
        ring
  let d : ℝ := (M₂ : ℝ) / (2 * M₁ : ℝ)
  let S : ℝ :=
    SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f))
  let K : ℝ := gmAffineRegionIIIKernelConstant n
  have hd : 0 < d := by dsimp only [d]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact gmAffineRegionIIIKernelConstant_nonneg n
  have hinvEq : d⁻¹ = (2 * M₁ : ℝ) / M₂ := by
    dsimp only [d]
    field_simp [hM₁r.ne', hM₂r.ne']
  have hinv : d⁻¹ ≤ 2 * M := by
    rw [hinvEq]
    calc
      (2 * M₁ : ℝ) / M₂ ≤ 2 * M₁ :=
        div_le_self (by positivity) hM₂one
      _ ≤ 2 * M := by gcongr
  have hinvNonneg : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hpow : (d⁻¹) ^ n ≤ (2 * M : ℝ) ^ n :=
    pow_le_pow_left₀ hinvNonneg hinv n
  have hratio : S / d ^ n ≤ S * (2 * M : ℝ) ^ n := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_left hpow hS
  have hkernel := gmAffineRegionIIIKernelEnvelope_le n hM₃ hQ
  have hkernelNonneg : 0 ≤
      gmAffinePoissonNearKernelEnvelope M₃ Q +
        gmAffinePoissonTailKernelEnvelope n M₃ Q :=
    add_nonneg
      (gmAffinePoissonNearKernelEnvelope_nonneg hM₃
        (zero_lt_one.trans_le hQ))
      (gmAffinePoissonTailKernelEnvelope_nonneg n hM₃
        (zero_lt_one.trans_le hQ))
  have hscale : (M₂ : ℝ) ^ 2 * M₃ ≤ (M : ℝ) ^ 3 := by
    calc
      (M₂ : ℝ) ^ 2 * M₃ ≤ (M : ℝ) ^ 2 * M := by gcongr
      _ = (M : ℝ) ^ 3 := by ring
  unfold gmAffineFourierDecayEnvelope gmAffineRegionIIIEnvelopeConstant
  change (((gmAffineSignedShell M₁).card : ℝ) *
      ((gmAffinePositiveShell M₂).card : ℝ) * ((2 * M₂ : ℝ) / M₁)) *
      (S / d ^ n) *
      (gmAffinePoissonNearKernelEnvelope M₃ Q +
        gmAffinePoissonTailKernelEnvelope n M₃ Q) ≤
    16 * (2 : ℝ) ^ n * S * K * Q * (M : ℝ) ^ (n + 3)
  calc
    (((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) * ((2 * M₂ : ℝ) / M₁)) *
        (S / d ^ n) *
        (gmAffinePoissonNearKernelEnvelope M₃ Q +
          gmAffinePoissonTailKernelEnvelope n M₃ Q) ≤
      (16 * (M₂ : ℝ) ^ 2) * (S * (2 * M : ℝ) ^ n) *
        (K * Q * M₃) := by gcongr
    _ = 16 * S * K * Q * (2 * M : ℝ) ^ n *
        ((M₂ : ℝ) ^ 2 * M₃) := by ring
    _ ≤ 16 * S * K * Q * (2 * M : ℝ) ^ n * (M : ℝ) ^ 3 := by
      gcongr
    _ = 16 * (2 : ℝ) ^ n * S * K * Q * (M : ℝ) ^ (n + 3) := by
      rw [mul_pow, pow_add]
      ring

/- The `gmAffineRegionIIIRawBound` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineRegionIIIRawBound
     (Y : ℝ) (f : SchwartzMap ℝ ℝ)
    (M₁ M₂ M₃ : ℕ) (Q : ℝ) : ℝ :=
  (gmAffineFourierDecayEnvelope n f M₁ M₂ M₃ Q) ^ 2 *
    (2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
      ((-(2 * (n : ℝ))) + 1)))
end


theorem gmAffineHighFrequencyIntegralFactor_le
    {n : ℕ} (hn : 1 ≤ n) {Y : ℝ} (hY : 0 < Y) :
    2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
        ((-(2 * (n : ℝ))) + 1)) ≤
      2 * Y ^ (1 - 2 * (n : ℝ)) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (1 : ℝ) ≤ 2 * (n : ℝ) - 1 := by linarith
  have hpow : 0 ≤ Y ^ (1 - 2 * (n : ℝ)) :=
    Real.rpow_nonneg hY.le _
  rw [show (-(2 * (n : ℝ))) + 1 = 1 - 2 * (n : ℝ) by ring]
  rw [show
    2 * (-Y ^ (1 - 2 * (n : ℝ)) / (1 - 2 * (n : ℝ))) =
      (2 * Y ^ (1 - 2 * (n : ℝ))) / (2 * (n : ℝ) - 1) by
        rw [show 1 - 2 * (n : ℝ) = -(2 * (n : ℝ) - 1) by ring,
          neg_div_neg_eq]
        ring]
  exact div_le_self (mul_nonneg (by norm_num) hpow) hden

/- The `gmAffineRegionIIISourceBound` definition used by the source-facing construction in `LargeValuesAffineIteration`. -/
noncomputable def gmAffineRegionIIISourceBound
    (n : ℕ) (Y : ℝ) (f : SchwartzMap ℝ ℝ) (M : ℕ) (Q : ℝ) : ℝ :=
  (gmAffineRegionIIIEnvelopeConstant n f * Q * (M : ℝ) ^ (n + 3)) ^ 2 *
    (2 * Y ^ (1 - 2 * (n : ℝ)))

theorem gmAffineRegionIIIRawBound_le_source
    (n : ℕ) (hn : 1 ≤ n) (f : SchwartzMap ℝ ℝ)
    {Q Y : ℝ} (hQ : 1 ≤ Q) (hY : 0 < Y)
    {M M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₁M : M₁ ≤ M)
    (hM₂ : 0 < M₂) (hM₂M : M₂ ≤ M)
    (hM₃ : 0 < M₃) (hM₃M : M₃ ≤ M) :
    gmAffineRegionIIIRawBound n Y f M₁ M₂ M₃ Q ≤
      gmAffineRegionIIISourceBound n Y f M Q := by
  have henv := gmAffineFourierDecayEnvelope_le_source
    n f hQ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  have henvNonneg := gmAffineFourierDecayEnvelope_nonneg
    n f hM₁ hM₂ hM₃ (zero_lt_one.trans_le hQ)
  have henvSq := pow_le_pow_left₀ henvNonneg henv 2
  have hfactor := gmAffineHighFrequencyIntegralFactor_le hn hY
  have hfactorNonneg :
      0 ≤ 2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
        ((-(2 * (n : ℝ))) + 1)) := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hdenNeg : (-(2 * (n : ℝ))) + 1 < 0 := by linarith
    have hpow : 0 ≤ Y ^ ((-(2 * (n : ℝ))) + 1) :=
      Real.rpow_nonneg hY.le _
    exact mul_nonneg (by norm_num)
      (div_nonneg_of_nonpos (neg_nonpos.mpr hpow) hdenNeg.le)
  unfold gmAffineRegionIIIRawBound gmAffineRegionIIISourceBound
  exact mul_le_mul henvSq hfactor hfactorNonneg (by positivity)

/- Complete raw form of Guth--Maynard Lemma 9.2, attached to the
literal scale triple attaining `J(f)`.  No tail, support, or scale term
has yet been hidden in asymptotic notation. -/
theorem exists_gmAffineJ_le_raw_lemma92
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (n : ℕ) (hn : 1 ≤ n)
    {T Q Y : ℝ} (hT : 1 ≤ T) (hQ : 1 ≤ Q)
    (hY : 0 < Y)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f)
    (hdecay : GMAffineFourierDecayAt T f)
    {M : ℕ} (hM : 0 < M) (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    ∃ M₁ M₂ M₃ : ℕ, ∃ Cdiv Ctail : ℝ,
      (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
      0 < Cdiv ∧ 0 ≤ Ctail ∧
      gmAffineJ f M ≤
        (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
            (∫ x : ℝ, f x) ^ 2 +
          gmAffineRegionIIRawBound epsilon n T Q Y
            (zero_lt_one.trans_le hT) (zero_lt_one.trans_le hQ)
            f M₁ M₂ M₃ Cdiv Ctail +
          gmAffineRegionIIIRawBound n Y f M₁ M₂ M₃ Q := by
  obtain ⟨M₁, M₂, M₃, hscale, hJ⟩ :=
    exists_gmAffineJ_le_source_regionI_add_middle_add_high
      n hn f hf hM hQ hY hQMY
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨hM₁, hM₁M, hM₂, hM₂M, hM₃, hM₃M⟩
  let B := gmAffineSecondPoissonCutoff T Q M₂ M₃
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hBpos : 0 < B := by
    dsimp only [B]
    exact gmAffineSecondPoissonCutoff_pos hTpos hQpos
  obtain ⟨Cdiv, Ctail, hCdiv, hCtail, hmiddle⟩ :=
    exists_integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_J_at_cutoff
      hepsilon n hTpos hQpos hBpos
        (by dsimp only [B]; exact
          gmAffineSecondPoissonCutoff_ge_Q hT (zero_le_one.trans hQ))
        f hf hsupp hdecay hM₁ hM₂ hM₃ hY.le
        (by dsimp only [B]; exact
          gmAffineSecondPoissonCutoff_width hTpos hQpos)
  have hmiddleRaw :
      (∫ xi in gmAffineMiddleFrequencyRegion
          (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
        gmAffineRegionIIRawBound epsilon n T Q Y hTpos hQpos
          f M₁ M₂ M₃ Cdiv Ctail := by
    dsimp only [B] at hmiddle
    unfold gmAffineRegionIIRawBound
    dsimp only
    convert hmiddle using 1
    all_goals ring_nf
  refine ⟨M₁, M₂, M₃, Cdiv, Ctail, hscale, hCdiv, hCtail, ?_⟩
  exact hJ.trans (add_le_add (add_le_add le_rfl hmiddleRaw) le_rfl)

/- Raw Lemma 9.2 with divisor and Fourier constants fixed before the
height and before the maximizing scale triple.  This is the uniform form
that may be iterated in Proposition 9.1. -/
theorem exists_gmAffineJ_le_raw_lemma92_of_constants
    {epsilon Cdiv Ctail : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (hCdiv : 0 < Cdiv) (hCtail : 0 ≤ Ctail)
    {T Q Y : ℝ} (hT : 1 ≤ T) (hQ : 1 ≤ Q) (hY : 0 < Y)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f)
    (hCdecay : ∀ xi : ℝ, xi ≠ 0 →
      ‖fourier (gmAffineComplexify f) xi‖ ≤
        Ctail * T ^ epsilon * (T / |xi|) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))
    (hcard : ∀ {M₁ M₃ : ℕ}, 0 < M₁ → 0 < M₃ → ∀ xi : ℝ,
      gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi| → |xi| ≤ Y →
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3))
    {M : ℕ} (hM : 0 < M) (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    ∃ M₁ M₂ M₃ : ℕ,
      (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
      gmAffineJ f M ≤
        (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
            (∫ x : ℝ, f x) ^ 2 +
          gmAffineRegionIIRawBound epsilon n T Q Y
            (zero_lt_one.trans_le hT) (zero_lt_one.trans_le hQ)
            f M₁ M₂ M₃ Cdiv Ctail +
          gmAffineRegionIIIRawBound n Y f M₁ M₂ M₃ Q := by
  obtain ⟨M₁, M₂, M₃, hscale, hJ⟩ :=
    exists_gmAffineJ_le_source_regionI_add_middle_add_high
      n hn f hf hM hQ hY hQMY
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨hM₁, hM₁M, hM₂, hM₂M, hM₃, hM₃M⟩
  let B := gmAffineSecondPoissonCutoff T Q M₂ M₃
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hBpos : 0 < B := by
    dsimp only [B]
    exact gmAffineSecondPoissonCutoff_pos hTpos hQpos
  have hmiddleBase :=
    integral_gmAffineMiddleFrequencyRegion_fourier_sq_le_sigmaIIReal_add_source_tails_of_constants
      hTpos hCdiv hCtail n f hCdecay hM₁ hM₂ hM₃ hQpos hY.le hBpos
        (hcard hM₁ hM₃)
        (by dsimp only [B]; exact
          gmAffineSecondPoissonCutoff_width hTpos hQpos)
  have hsigma := norm_gmAffineSigmaIIReal_le_J_add_far
    n hBpos hQpos (show 0 < (8 * M₃ : ℝ) by positivity)
      (by dsimp only [B]; exact
        gmAffineSecondPoissonCutoff_ge_Q hT (zero_le_one.trans hQ))
      hM₂ f hf hsupp
  let D : ℝ := Cdiv *
    (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
      (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)
  let K : ℝ := (32 * M₃ : ℝ) *
    SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
    unfold gmAffineFirstPoissonRadius
    positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hmiddle := hmiddleBase.trans (by
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · exact add_le_add hsigma le_rfl
        · exact hK
      · positivity
    · exact le_rfl)
  have hmiddleRaw :
      (∫ xi in gmAffineMiddleFrequencyRegion
          (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
        gmAffineRegionIIRawBound epsilon n T Q Y hTpos hQpos
          f M₁ M₂ M₃ Cdiv Ctail := by
    dsimp only [B] at hmiddle
    unfold gmAffineRegionIIRawBound
    dsimp only
    convert hmiddle using 1
    all_goals ring_nf
  refine ⟨M₁, M₂, M₃, hscale, ?_⟩
  exact hJ.trans (add_le_add (add_le_add le_rfl hmiddleRaw) le_rfl)

/- Fully collapsed analytic form of Lemma 9.2 before the source choices
`Q = T^η` and `Y = T⁶`.  Every term comes from the literal triple attaining
`J(f)`; the only remaining work is explicit power absorption. -/
theorem exists_gmAffineJ_le_source_lemma92_components
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (n : ℕ) (hn : 1 ≤ n)
    {T Q Y : ℝ} (hT : 1 ≤ T) (hQ : 1 ≤ Q) (hY : 0 < Y)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f)
    (hdecay : GMAffineFourierDecayAt T f)
    {M : ℕ} (hM : 0 < M) (hMT : (M : ℝ) ≤ T ^ 4)
    (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    ∃ M₁ M₂ M₃ : ℕ, ∃ Cdiv Ctail : ℝ,
      (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
      0 < Cdiv ∧ 0 ≤ Ctail ∧
      gmAffineJ f M ≤
        (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
            (∫ x : ℝ, f x) ^ 2 +
          (Cdiv * gmAffineRegionIICoreConstant *
            (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
            Q ^ 3 * (M : ℝ) ^ 2 *
            (Real.sqrt (∫ u : ℝ, f u ^ 2) *
              Real.sqrt (gmAffineJ
                (gmAffineTildeSchwartz
                  (gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q)
                  (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)) +
            gmAffineRegionIITailSourceBound epsilon n T Q Y
              f M Cdiv Ctail) +
          gmAffineRegionIIISourceBound n Y f M Q := by
  obtain ⟨M₁, M₂, M₃, Cdiv, Ctail, hscale, hCdiv, hCtail, hJ⟩ :=
    exists_gmAffineJ_le_raw_lemma92 hepsilon n hn hT hQ hY
      f hf hsupp hdecay hM hQMY
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨hM₁, hM₁M, hM₂, hM₂M, hM₃, hM₃M⟩
  have hcore := gmAffineRegionIICoreRawBound_le_source
    (zero_lt_one.trans_le hT) hQ hY.le f
      hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hCdiv.le
      (epsilon := epsilon) (Cdiv := Cdiv)
  have htail := gmAffineRegionIITailRawBound_le_source
    hepsilon.le hT hQ hY hCdiv.le hCtail f hf
      hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hMT hQMY
      (n := n)
  have hhigh := gmAffineRegionIIIRawBound_le_source
    n hn f hQ hY hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  have hsplit := gmAffineRegionIIRawBound_eq_core_add_tail
    epsilon n (zero_lt_one.trans_le hT) (zero_lt_one.trans_le hQ)
      f M₁ M₂ M₃ Cdiv Ctail (Y := Y)
  refine ⟨M₁, M₂, M₃, Cdiv, Ctail, hscale, hCdiv, hCtail, hJ.trans ?_⟩
  rw [hsplit]
  exact add_le_add (add_le_add le_rfl (add_le_add hcore htail)) hhigh

/- Uniform-constant version of the completely collapsed Lemma 9.2
components.  The returned maximizing triple carries no newly selected
analytic constant. -/
theorem exists_gmAffineJ_le_source_lemma92_components_of_constants
    {epsilon Cdiv Ctail : ℝ} (hepsilon : 0 < epsilon)
    (n : ℕ) (hn : 1 ≤ n) (hCdiv : 0 < Cdiv) (hCtail : 0 ≤ Ctail)
    {T Q Y : ℝ} (hT : 1 ≤ T) (hQ : 1 ≤ Q) (hY : 0 < Y)
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hsupp : GMAffineIterationSupported f)
    (hCdecay : ∀ xi : ℝ, xi ≠ 0 →
      ‖fourier (gmAffineComplexify f) xi‖ ≤
        Ctail * T ^ epsilon * (T / |xi|) ^ n *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f))
    (hcard : ∀ {M₁ M₃ : ℕ}, 0 < M₁ → 0 < M₃ → ∀ xi : ℝ,
      gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi| → |xi| ≤ Y →
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3))
    {M : ℕ} (hM : 0 < M) (hMT : (M : ℝ) ≤ T ^ 4)
    (hQMY : Q * (M : ℝ) ≤ 4 * Y) :
    ∃ M₁ M₂ M₃ : ℕ,
      (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
      gmAffineJ f M ≤
        (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
            (∫ x : ℝ, f x) ^ 2 +
          (Cdiv * gmAffineRegionIICoreConstant *
            (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
            Q ^ 3 * (M : ℝ) ^ 2 *
            (Real.sqrt (∫ u : ℝ, f u ^ 2) *
              Real.sqrt (gmAffineJ
                (gmAffineTildeSchwartz
                  (gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q)
                  (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)) +
            gmAffineRegionIITailSourceBound epsilon n T Q Y
              f M Cdiv Ctail) +
          gmAffineRegionIIISourceBound n Y f M Q := by
  obtain ⟨M₁, M₂, M₃, hscale, hJ⟩ :=
    exists_gmAffineJ_le_raw_lemma92_of_constants n hn hCdiv hCtail
      hT hQ hY f hf hsupp hCdecay hcard hM hQMY
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨hM₁, hM₁M, hM₂, hM₂M, hM₃, hM₃M⟩
  have hcore := gmAffineRegionIICoreRawBound_le_source
    (zero_lt_one.trans_le hT) hQ hY.le f
      hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hCdiv.le
      (epsilon := epsilon) (Cdiv := Cdiv)
  have htail := gmAffineRegionIITailRawBound_le_source
    hepsilon.le hT hQ hY hCdiv.le hCtail f hf
      hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hMT hQMY (n := n)
  have hhigh := gmAffineRegionIIIRawBound_le_source
    n hn f hQ hY hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  have hsplit := gmAffineRegionIIRawBound_eq_core_add_tail
    epsilon n (zero_lt_one.trans_le hT) (zero_lt_one.trans_le hQ)
      f M₁ M₂ M₃ Cdiv Ctail (Y := Y)
  refine ⟨M₁, M₂, M₃, hscale, hJ.trans ?_⟩
  rw [hsplit]
  exact add_le_add (add_le_add le_rfl (add_le_add hcore htail)) hhigh

/- The exact collapsed conclusion of Lemma 9.2 at fixed source scales and
fixed analytic constants.  Naming the proposition makes the subsequent
uniform quantifier order explicit; it is not itself asserted without the
consumer theorem below. -/
def GMAffineLemma92ComponentsAt
    (epsilon : ℝ) (n : ℕ) (Cdiv Ctail T Q Y : ℝ)
    (hT : 0 < T) (hQ : 0 < Q) (f : SchwartzMap ℝ ℝ) (M : ℕ) : Prop :=
  ∃ M₁ M₂ M₃ : ℕ,
    (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
    gmAffineJ f M ≤
      (gmAffineRegionIConstant n) ^ 2 * Q ^ 3 * (M : ℝ) ^ 6 *
          (∫ x : ℝ, f x) ^ 2 +
        (Cdiv * gmAffineRegionIICoreConstant *
          (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          Q ^ 3 * (M : ℝ) ^ 2 *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz
                (gmAffineSecondPoissonCutoff T Q M₂ M₃ / Q)
                (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)) +
          gmAffineRegionIITailSourceBound epsilon n T Q Y
            f M Cdiv Ctail) +
        gmAffineRegionIIISourceBound n Y f M Q

/-! ### Source choices `Q = T^η`, `Y = T⁶` -/

/- A uniform small exponent for the Lemma 9.2 improvement.  The cap at
`1/20` supplies every coarse scale comparison, while `η ≤ δ/20` leaves
half of the requested `T^δ` budget for constants and smoothing losses. -/
noncomputable def gmAffineIterationEta (delta : ℝ) : ℝ :=
  min (delta / 20) (1 / 20)

theorem gmAffineIterationEta_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    0 < gmAffineIterationEta delta := by
  unfold gmAffineIterationEta
  exact lt_min (div_pos hdelta (by norm_num)) (by norm_num)

theorem gmAffineIterationEta_le_delta_div_twenty (delta : ℝ) :
    gmAffineIterationEta delta ≤ delta / 20 := by
  unfold gmAffineIterationEta
  exact min_le_left _ _

theorem gmAffineIterationEta_le_one (delta : ℝ) :
    gmAffineIterationEta delta ≤ 1 := by
  have h := min_le_right (delta / 20) (1 / 20 : ℝ)
  unfold gmAffineIterationEta
  linarith

theorem ten_mul_gmAffineIterationEta_le
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    10 * gmAffineIterationEta delta ≤ delta := by
  have h := gmAffineIterationEta_le_delta_div_twenty delta
  linarith

theorem one_le_rpow_gmAffineIterationEta
    {delta T : ℝ} (hdelta : 0 < delta) (hT : 1 ≤ T) :
    1 ≤ T ^ gmAffineIterationEta delta := by
  exact Real.one_le_rpow hT (gmAffineIterationEta_pos hdelta).le

theorem rpow_gmAffineIterationEta_le_self
    (delta : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    T ^ gmAffineIterationEta delta ≤ T := by
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hT
      (gmAffineIterationEta_le_one delta)

/- The paper's choices `Q=T^η`, `Y=T⁶` satisfy the first-Poisson window
condition whenever the preliminary reduction `M ≤ T⁴` holds. -/
theorem gmAffineIterationQ_mul_M_le_four_Y
    {delta T : ℝ} (hT : 1 ≤ T)
    {M : ℕ} (hMT : (M : ℝ) ≤ T ^ 4) :
    T ^ gmAffineIterationEta delta * (M : ℝ) ≤ 4 * T ^ 6 := by
  have hQ := rpow_gmAffineIterationEta_le_self delta hT
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hfirst :
      T ^ gmAffineIterationEta delta * (M : ℝ) ≤ T * T ^ 4 :=
    mul_le_mul hQ hMT hMnonneg hTnonneg
  have hpow56 : T ^ 5 ≤ T ^ 6 := by
    calc
      T ^ 5 = T ^ 5 * 1 := by ring
      _ ≤ T ^ 5 * T := mul_le_mul_of_nonneg_left hT (pow_nonneg hTnonneg 5)
      _ = T ^ 6 := by ring
  nlinarith

theorem gmAffineIterationQ_cube_eq
    (delta : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (T ^ gmAffineIterationEta delta) ^ (3 : ℕ) =
      T ^ (3 * gmAffineIterationEta delta) := by
  simpa [mul_comm] using
    (Real.rpow_mul_natCast hT (gmAffineIterationEta delta) 3).symm

section
variable {delta T : ℝ} (hdelta : 0 < delta) (hT : 2 ≤ T)
include delta T hdelta hT

theorem gmAffineIterationDoubleSix_rpow_le
     :
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta ≤
      T ^ (7 * gmAffineIterationEta delta) := by
  have hTnonneg : 0 ≤ T := by linarith
  have hbase : T ^ (6 : ℕ) + T ^ (6 : ℕ) ≤ T ^ (7 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right hT (pow_nonneg hTnonneg 6)
    nlinarith [show T ^ (7 : ℕ) = T ^ (6 : ℕ) * T by ring]
  have hp := Real.rpow_le_rpow
    (add_nonneg (pow_nonneg hTnonneg 6) (pow_nonneg hTnonneg 6))
    hbase (gmAffineIterationEta_pos hdelta).le
  calc
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta ≤
        (T ^ (7 : ℕ)) ^ gmAffineIterationEta delta := hp
    _ = T ^ (7 * gmAffineIterationEta delta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTnonneg]
      norm_num

/- Region I and the retained Region-II core together spend at most the
requested `T^δ` factor under the source choices. -/
theorem gmAffineIterationCorePower_le
     :
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta *
        (T ^ gmAffineIterationEta delta) ^ (3 : ℕ) ≤
      T ^ delta := by
  have hTone : 1 ≤ T := by linarith
  have hTnonneg : 0 ≤ T := by linarith
  have hleft := gmAffineIterationDoubleSix_rpow_le hdelta hT
  have hcube := gmAffineIterationQ_cube_eq delta hTnonneg
  have hsumExponent :
      7 * gmAffineIterationEta delta +
          3 * gmAffineIterationEta delta ≤ delta := by
    simpa [show 7 * gmAffineIterationEta delta +
        3 * gmAffineIterationEta delta =
          10 * gmAffineIterationEta delta by ring] using
      ten_mul_gmAffineIterationEta_le hdelta.le
  calc
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta *
        (T ^ gmAffineIterationEta delta) ^ (3 : ℕ) ≤
      T ^ (7 * gmAffineIterationEta delta) *
        (T ^ gmAffineIterationEta delta) ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right hleft
        (pow_nonneg (Real.rpow_nonneg hTnonneg _) 3)
    _ = T ^ (7 * gmAffineIterationEta delta) *
        T ^ (3 * gmAffineIterationEta delta) := by rw [hcube]
    _ = T ^ (7 * gmAffineIterationEta delta +
        3 * gmAffineIterationEta delta) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hTone)]
    _ ≤ T ^ delta :=
      Real.rpow_le_rpow_of_exponent_le hTone hsumExponent

/- The literal divisor-loss and first-Poisson scale factor in Region II
fits inside the requested `T^delta` budget at the source choices
`Q=T^eta`, `Y=T^6`. -/
theorem gmAffineIterationRegionIIScaleFactor_le
    
    {M M₁ M₃ : ℕ} (hM₁M : M₁ ≤ M) (hM₃ : 0 < M₃)
    (hMT : (M : ℝ) ≤ T ^ 4) :
    (T ^ (6 : ℕ) + gmAffineFirstPoissonRadius M₁ M₃
        (T ^ gmAffineIterationEta delta)) ^ gmAffineIterationEta delta *
      (T ^ gmAffineIterationEta delta) ^ (3 : ℕ) ≤ T ^ delta := by
  have hTone : 1 ≤ T := by linarith
  have hQnonneg : 0 ≤ T ^ gmAffineIterationEta delta := by positivity
  have hQMY := gmAffineIterationQ_mul_M_le_four_Y
    (delta := delta) hTone hMT
  have hR : gmAffineFirstPoissonRadius M₁ M₃
      (T ^ gmAffineIterationEta delta) ≤ T ^ (6 : ℕ) :=
    gmAffineFirstPoissonRadius_le_of_scale hM₁M hM₃ hQnonneg hQMY
  have hbase :
      T ^ (6 : ℕ) + gmAffineFirstPoissonRadius M₁ M₃
          (T ^ gmAffineIterationEta delta) ≤
        T ^ (6 : ℕ) + T ^ (6 : ℕ) := add_le_add le_rfl hR
  have hrpow := Real.rpow_le_rpow
    (add_nonneg (pow_nonneg (by linarith : 0 ≤ T) 6)
      (by unfold gmAffineFirstPoissonRadius; positivity))
    hbase (gmAffineIterationEta_pos hdelta).le
  exact (mul_le_mul_of_nonneg_right hrpow
    (pow_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) _) 3)).trans
      (gmAffineIterationCorePower_le hdelta hT)
end


/-! ### Arbitrary-order source-tail absorption -/

/- A positive source exponent times a sufficiently large natural decay
order dominates any prescribed real polynomial exponent.  This is the
literal finite choice hidden by the phrase "take the Fourier-decay order
sufficiently large" in the proof of Lemma 9.2. -/
theorem exists_nat_mul_ge_of_pos
    {eta A : ℝ} (heta : 0 < eta) :
    ∃ n : ℕ, A ≤ eta * n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (A / eta)
  refine ⟨n, ?_⟩
  rw [div_le_iff₀ heta] at hn
  simpa only [mul_comm] using hn

/- Natural powers of the source cutoff `Q=T^eta` are exactly real powers
with exponent `eta*n`. -/
theorem pow_rpow_eq_rpow_mul_nat
    {T eta : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (T ^ eta) ^ n = T ^ (eta * n) := by
  simpa only [Nat.cast_ofNat] using
    (Real.rpow_mul_natCast hT eta n).symm

section
variable {T eta A : ℝ} (hT : 1 ≤ T) {n : ℕ}
include T eta A hT n

/- Once the natural decay order beats a polynomial exponent, division by
`Q^n`, with `Q=T^eta`, removes that entire power for every `T≥1`. -/
theorem rpow_div_pow_rpow_le_one
     (hn : A ≤ eta * n) :
    T ^ A / (T ^ eta) ^ n ≤ 1 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hpow : T ^ A ≤ T ^ (eta * n) :=
    Real.rpow_le_rpow_of_exponent_le hT hn
  rw [pow_rpow_eq_rpow_mul_nat hTpos.le]
  exact (div_le_one (Real.rpow_pos_of_pos hTpos _)).2 hpow

/- Squaring the source denominator doubles the available negative
exponent. -/
theorem rpow_div_sq_pow_rpow_le_one
    
    (hn : A ≤ 2 * eta * n) :
    T ^ A / ((T ^ eta) ^ n) ^ 2 ≤ 1 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hden : ((T ^ eta) ^ n) ^ 2 = T ^ (2 * eta * n) := by
    rw [pow_rpow_eq_rpow_mul_nat hTpos.le]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    norm_num
    ring_nf
  rw [hden]
  exact (div_le_one (Real.rpow_pos_of_pos hTpos _)).2
    (Real.rpow_le_rpow_of_exponent_le hT hn)
end


section
variable {T : ℝ} {M : ℕ} (hMT : (M : ℝ) ≤ T ^ 4)
include T M hMT

theorem gmAffineIteration_M_pow_four_le
     :
    (M : ℝ) ^ 4 ≤ T ^ 16 := by
  calc
    (M : ℝ) ^ 4 ≤ (T ^ 4) ^ 4 := by gcongr
    _ = T ^ 16 := by ring

theorem gmAffineIteration_M_pow_three_le
     :
    (M : ℝ) ^ 3 ≤ T ^ 12 := by
  calc
    (M : ℝ) ^ 3 ≤ (T ^ 4) ^ 3 := by gcongr
    _ = T ^ 12 := by ring
end


section
variable {delta T : ℝ}
include delta T

/- Coarse source-scale bound for the three additive frequency scales in
the first-Poisson tail. -/
theorem gmAffineIteration_Y_add_Q_add_one_le
     (hT : 1 ≤ T) :
    T ^ (6 : ℕ) + T ^ gmAffineIterationEta delta + 1 ≤
      3 * T ^ (6 : ℕ) := by
  have hQ : T ^ gmAffineIterationEta delta ≤ T :=
    rpow_gmAffineIterationEta_le_self delta hT
  have hT6 : T ≤ T ^ (6 : ℕ) := by bound
  linarith

section
variable (hdelta : 0 < delta) (hT : 2 ≤ T)
    {M : ℕ} (hMT : (M : ℝ) ≤ T ^ 4) (n : ℕ)
include hdelta hT M hMT n

/- The first omitted Region-II lattice has a single arbitrary negative
power of `Q`; all remaining source factors cost at most
`T^(23+8*eta)`. -/
theorem gmAffineIterationRegionIIFirstTail_scale_le
     :
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta *
        (T ^ gmAffineIterationEta delta) * (M : ℝ) *
        ((T ^ gmAffineIterationEta delta) *
          (T ^ 3 / (T ^ gmAffineIterationEta delta) ^ (n + 1) *
            (M : ℝ) ^ 4)) ≤
      T ^ (23 + 8 * gmAffineIterationEta delta) /
        (T ^ gmAffineIterationEta delta) ^ n := by
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hQpos : 0 < T ^ gmAffineIterationEta delta := by positivity
  have hdouble := gmAffineIterationDoubleSix_rpow_le hdelta hT
  have hM4 := gmAffineIteration_M_pow_four_le hMT
  have hM : (M : ℝ) ≤ T ^ 4 := hMT
  calc
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta *
        (T ^ gmAffineIterationEta delta) * (M : ℝ) *
        ((T ^ gmAffineIterationEta delta) *
          (T ^ 3 / (T ^ gmAffineIterationEta delta) ^ (n + 1) *
            (M : ℝ) ^ 4)) ≤
      T ^ (7 * gmAffineIterationEta delta) *
        (T ^ gmAffineIterationEta delta) * T ^ 4 *
        ((T ^ gmAffineIterationEta delta) *
          (T ^ 3 / (T ^ gmAffineIterationEta delta) ^ (n + 1) *
            T ^ 16)) := by gcongr
    _ = T ^ (23 + 8 * gmAffineIterationEta delta) /
        (T ^ gmAffineIterationEta delta) ^ n := by
      field_simp [hQpos.ne']
      rw [pow_succ (T ^ gmAffineIterationEta delta) n]
      have hq2 : (T ^ gmAffineIterationEta delta) ^ (2 : ℕ) =
          T ^ (2 * gmAffineIterationEta delta) := by
        simpa [mul_comm] using
          (Real.rpow_mul_natCast hTpos.le
            (gmAffineIterationEta delta) 2).symm
      rw [hq2]
      ring_nf
      rw [pow_rpow_eq_rpow_mul_nat hTpos.le n]
      have hfactor :
          T ^ (gmAffineIterationEta delta * 9) * T ^ (23 : ℕ) =
            T ^ gmAffineIterationEta delta *
              T ^ (23 + gmAffineIterationEta delta * 8) := by
        calc
          T ^ (gmAffineIterationEta delta * 9) * T ^ (23 : ℕ) =
              T ^ (gmAffineIterationEta delta * 9) * T ^ (23 : ℝ) := by simp
          _ =
              T ^ (gmAffineIterationEta delta * 9 + 23) :=
            (Real.rpow_add hTpos _ _).symm
          _ = T ^ (gmAffineIterationEta delta +
                (23 + gmAffineIterationEta delta * 8)) := by
            congr 1
            ring
          _ = T ^ gmAffineIterationEta delta *
                T ^ (23 + gmAffineIterationEta delta * 8) :=
            Real.rpow_add hTpos _ _
      have hsevenTwo :
          T ^ (gmAffineIterationEta delta * 7) *
              T ^ (gmAffineIterationEta delta * 2) =
            T ^ (gmAffineIterationEta delta * 9) := by
        calc
          T ^ (gmAffineIterationEta delta * 7) *
                T ^ (gmAffineIterationEta delta * 2) =
              T ^ (gmAffineIterationEta delta * 7 +
                gmAffineIterationEta delta * 2) :=
            (Real.rpow_add hTpos _ _).symm
          _ = T ^ (gmAffineIterationEta delta * 9) := by
            congr 1
            ring
      grind

/- The squared first-frequency Fourier tail has two arbitrary negative
powers of `Q`; its complete source-scale cost is
`3*4^n*T^(26+11*eta)`. -/
theorem gmAffineIterationRegionIISecondTail_scale_le
     :
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta *
        (T ^ gmAffineIterationEta delta) * (M : ℝ) *
        ((T ^ (6 : ℕ) + T ^ gmAffineIterationEta delta + 1) *
          (T ^ gmAffineIterationEta delta) * (M : ℝ) ^ 4 *
          (T ^ gmAffineIterationEta delta *
            (2 / T ^ gmAffineIterationEta delta) ^ n) ^ 2) ≤
      (3 * (4 : ℝ) ^ n) *
        (T ^ (26 + 11 * gmAffineIterationEta delta) /
          ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) := by
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hQpos : 0 < T ^ gmAffineIterationEta delta := by positivity
  have hdouble := gmAffineIterationDoubleSix_rpow_le hdelta hT
  have hsum := gmAffineIteration_Y_add_Q_add_one_le
    (delta := delta) hTone
  have hM4 := gmAffineIteration_M_pow_four_le hMT
  calc
    (T ^ (6 : ℕ) + T ^ (6 : ℕ)) ^ gmAffineIterationEta delta *
        (T ^ gmAffineIterationEta delta) * (M : ℝ) *
        ((T ^ (6 : ℕ) + T ^ gmAffineIterationEta delta + 1) *
          (T ^ gmAffineIterationEta delta) * (M : ℝ) ^ 4 *
          (T ^ gmAffineIterationEta delta *
            (2 / T ^ gmAffineIterationEta delta) ^ n) ^ 2) ≤
      T ^ (7 * gmAffineIterationEta delta) *
        (T ^ gmAffineIterationEta delta) * T ^ 4 *
        ((3 * T ^ (6 : ℕ)) *
          (T ^ gmAffineIterationEta delta) * T ^ 16 *
          (T ^ gmAffineIterationEta delta *
            (2 / T ^ gmAffineIterationEta delta) ^ n) ^ 2) := by
      gcongr
    _ = (3 * (4 : ℝ) ^ n) *
        (T ^ (26 + 11 * gmAffineIterationEta delta) /
          ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) := by
      rw [div_pow]
      field_simp [hQpos.ne']
      have htwo : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
        calc
          ((2 : ℝ) ^ n) ^ 2 = 2 ^ (n * 2) := by rw [pow_mul]
          _ = 2 ^ (2 * n) := by rw [Nat.mul_comm]
          _ = ((2 : ℝ) ^ 2) ^ n := by rw [pow_mul]
          _ = (4 : ℝ) ^ n := by norm_num
      rw [htwo]
      have hq4 : (T ^ gmAffineIterationEta delta) ^ (4 : ℕ) =
          T ^ (4 * gmAffineIterationEta delta) := by
        simpa [mul_comm] using
          (Real.rpow_mul_natCast hTpos.le
            (gmAffineIterationEta delta) 4).symm
      rw [hq4]
      have hpower :
          T ^ (7 * gmAffineIterationEta delta) *
              T ^ (4 * gmAffineIterationEta delta) * T ^ (26 : ℕ) =
            T ^ (26 + 11 * gmAffineIterationEta delta) := by
        calc
          T ^ (7 * gmAffineIterationEta delta) *
                T ^ (4 * gmAffineIterationEta delta) * T ^ (26 : ℕ) =
              T ^ (7 * gmAffineIterationEta delta +
                4 * gmAffineIterationEta delta) * T ^ (26 : ℕ) := by
            rw [Real.rpow_add hTpos]
          _ = T ^ (7 * gmAffineIterationEta delta +
                4 * gmAffineIterationEta delta) * T ^ (26 : ℝ) := by simp
          _ = T ^ (7 * gmAffineIterationEta delta +
                4 * gmAffineIterationEta delta + 26) :=
            (Real.rpow_add hTpos _ _).symm
          _ = T ^ (26 + 11 * gmAffineIterationEta delta) := by
            congr 1
            ring
      rw [hpower]
      ring_nf
end


/- The omitted first-Poisson high tail costs `T^30` before its two
arbitrary negative powers of `Q`. -/
theorem gmAffineIterationRegionIIHighTail_scale_le
     (hT : 1 ≤ T)
    {M : ℕ} (hMT : (M : ℝ) ≤ T ^ 4) (n : ℕ) :
    T ^ (6 : ℕ) *
        ((M : ℝ) ^ 3 /
          (T ^ gmAffineIterationEta delta) ^ n) ^ 2 ≤
      T ^ (30 : ℕ) /
        ((T ^ gmAffineIterationEta delta) ^ n) ^ 2 := by
  have hQpos : 0 < T ^ gmAffineIterationEta delta := by positivity
  have hM3 := gmAffineIteration_M_pow_three_le hMT
  calc
    T ^ (6 : ℕ) *
        ((M : ℝ) ^ 3 /
          (T ^ gmAffineIterationEta delta) ^ n) ^ 2 ≤
      T ^ (6 : ℕ) *
        (T ^ 12 /
          (T ^ gmAffineIterationEta delta) ^ n) ^ 2 := by
      gcongr
    _ = T ^ (30 : ℕ) /
        ((T ^ gmAffineIterationEta delta) ^ n) ^ 2 := by
      field_simp [hQpos.ne']
end


section
variable (n : ℕ)
include n

/- Fixed (in height and affine scale) coefficient left after all three
Region-II tail scales are stripped off. -/
noncomputable def gmAffineRegionIITailAbsorptionConstant
     (f : SchwartzMap ℝ ℝ) (Cdiv Ctail : ℝ) : ℝ :=
  (512 * Cdiv *
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
      (64 * gmAffineMiddleFarSourceConstant n *
          (∫ u : ℝ, |f u|) ^ 2 +
        192 * 3 * (4 : ℝ) ^ n * Ctail ^ 2 *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ^ 2) +
    4 * (gmAffineRegionIFarConstant n * (∫ x : ℝ, f x)) ^ 2

/- Function-independent coefficient obtained after imposing a
Fourier-to-mass ratio bound. -/
noncomputable def gmAffineRegionIITailMassConstant
     (Cdiv D : ℝ) : ℝ :=
  (512 * Cdiv *
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
      (64 * gmAffineMiddleFarSourceConstant n +
        192 * 3 * (4 : ℝ) ^ n * D ^ 2) +
    4 * gmAffineRegionIFarConstant n ^ 2

theorem gmAffineRegionIITailMassConstant_nonneg
     {Cdiv D : ℝ} (hCdiv : 0 ≤ Cdiv) :
    0 ≤ gmAffineRegionIITailMassConstant n Cdiv D := by
  unfold gmAffineRegionIITailMassConstant
  have hmiddle := gmAffineMiddleFarSourceConstant_nonneg n
  positivity
end


/- Before choosing the arbitrary decay order, the complete Region-II
tail is a sum of three fixed coefficients times the three source-scale
ratios proved above. -/
theorem gmAffineRegionIITailSourceBound_le_scale_ratios
    {delta T Cdiv Ctail : ℝ} (hdelta : 0 < delta) (hT : 2 ≤ T)
    (hCdiv : 0 ≤ Cdiv) (f : SchwartzMap ℝ ℝ)
    {M : ℕ} (hMT : (M : ℝ) ≤ T ^ 4) (n : ℕ) :
    gmAffineRegionIITailSourceBound (gmAffineIterationEta delta) n T
        (T ^ gmAffineIterationEta delta) (T ^ (6 : ℕ))
        f M Cdiv Ctail ≤
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n *
            (∫ u : ℝ, |f u|) ^ 2) *
          (T ^ (23 + 8 * gmAffineIterationEta delta) /
            (T ^ gmAffineIterationEta delta) ^ n) +
      (512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * 3 * (4 : ℝ) ^ n * Ctail ^ 2 *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ^ 2) *
          (T ^ (26 + 11 * gmAffineIterationEta delta) /
            ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) +
      4 * (gmAffineRegionIFarConstant n * (∫ x : ℝ, f x)) ^ 2 *
        (T ^ (30 : ℕ) /
          ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) := by
  have hfirst := gmAffineIterationRegionIIFirstTail_scale_le
    hdelta hT hMT n
  have hsecond := gmAffineIterationRegionIISecondTail_scale_le
    hdelta hT hMT n
  have hhigh := gmAffineIterationRegionIIHighTail_scale_le
    (delta := delta) (by linarith : (1 : ℝ) ≤ T) hMT n
  have hmiddle : 0 ≤ gmAffineMiddleFarSourceConstant n :=
    gmAffineMiddleFarSourceConstant_nonneg n
  have hL : 0 ≤ SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual := by
    positivity
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
    positivity
  unfold gmAffineRegionIITailSourceBound
  calc
    (512 * Cdiv *
          (T ^ 6 + T ^ 6) ^ gmAffineIterationEta delta *
          T ^ gmAffineIterationEta delta * ↑M *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
          (T ^ gmAffineIterationEta delta *
              (64 * gmAffineMiddleFarSourceConstant n * T ^ 3 /
                  (T ^ gmAffineIterationEta delta) ^ (n + 1) * ↑M ^ 4 *
                  (∫ u, |f u|) ^ 2) +
            192 * (T ^ 6 + T ^ gmAffineIterationEta delta + 1) *
              T ^ gmAffineIterationEta delta * ↑M ^ 4 *
              (Ctail * T ^ gmAffineIterationEta delta *
                  (2 / T ^ gmAffineIterationEta delta) ^ n *
                  SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)) ^ 2) +
        4 * T ^ 6 *
          (gmAffineRegionIFarConstant n * ↑M ^ 3 * (∫ x, f x) /
              (T ^ gmAffineIterationEta delta) ^ n) ^ 2 =
      ((512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n * (∫ u, |f u|) ^ 2)) *
          ((T ^ 6 + T ^ 6) ^ gmAffineIterationEta delta *
            T ^ gmAffineIterationEta delta * ↑M *
            (T ^ gmAffineIterationEta delta *
              (T ^ 3 /
                (T ^ gmAffineIterationEta delta) ^ (n + 1) * ↑M ^ 4))) +
      ((512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * Ctail ^ 2 *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ^ 2)) *
          ((T ^ 6 + T ^ 6) ^ gmAffineIterationEta delta *
            T ^ gmAffineIterationEta delta * ↑M *
            ((T ^ 6 + T ^ gmAffineIterationEta delta + 1) *
              T ^ gmAffineIterationEta delta * ↑M ^ 4 *
              (T ^ gmAffineIterationEta delta *
                (2 / T ^ gmAffineIterationEta delta) ^ n) ^ 2)) +
      (4 * (gmAffineRegionIFarConstant n * (∫ x, f x)) ^ 2) *
          (T ^ 6 *
            (↑M ^ 3 / (T ^ gmAffineIterationEta delta) ^ n) ^ 2) := by
        ring
    _ ≤ ((512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (64 * gmAffineMiddleFarSourceConstant n * (∫ u, |f u|) ^ 2)) *
          (T ^ (23 + 8 * gmAffineIterationEta delta) /
            (T ^ gmAffineIterationEta delta) ^ n) +
      ((512 * Cdiv *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2) *
        (192 * Ctail ^ 2 *
          SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) ^ 2)) *
          ((3 * (4 : ℝ) ^ n) *
            (T ^ (26 + 11 * gmAffineIterationEta delta) /
              ((T ^ gmAffineIterationEta delta) ^ n) ^ 2)) +
      (4 * (gmAffineRegionIFarConstant n * (∫ x, f x)) ^ 2) *
          (T ^ (30 : ℕ) /
            ((T ^ gmAffineIterationEta delta) ^ n) ^ 2) := by
        gcongr
    _ = _ := by ring

/- Every affine scale `M≤T⁴` contributes at most the corresponding
source power in Region III. -/
theorem gmAffineIteration_M_pow_add_three_le
    {T : ℝ} {M n : ℕ} (hMT : (M : ℝ) ≤ T ^ 4) :
    (M : ℝ) ^ (n + 3) ≤ T ^ (4 * (n + 3)) := by
  calc
    (M : ℝ) ^ (n + 3) ≤ (T ^ 4) ^ (n + 3) := by gcongr
    _ = T ^ (4 * (n + 3)) := by rw [pow_mul]

/- Exact source exponent underlying the Region-III tail. -/
theorem gmAffineIterationRegionIII_source_scale_eq
    {delta T : ℝ} (hT : 0 < T) (n : ℕ) :
    (T ^ gmAffineIterationEta delta * T ^ (4 * (n + 3))) ^ 2 *
        (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ)) =
      T ^ (2 * gmAffineIterationEta delta + 30 - 4 * (n : ℝ)) := by
  have hTnonneg : 0 ≤ T := hT.le
  have hq2 : (T ^ gmAffineIterationEta delta) ^ (2 : ℕ) =
      T ^ (2 * gmAffineIterationEta delta) := by
    simpa [mul_comm] using
      (Real.rpow_mul_natCast hTnonneg
        (gmAffineIterationEta delta) 2).symm
  have hp : T ^ (4 * (n + 3)) =
      T ^ ((4 * (n + 3) : ℕ) : ℝ) :=
    (Real.rpow_natCast T (4 * (n + 3))).symm
  have hp2 : (T ^ ((4 * (n + 3) : ℕ) : ℝ)) ^ (2 : ℕ) =
      T ^ (2 * ((4 * (n + 3) : ℕ) : ℝ)) := by
    simpa [mul_comm] using
      (Real.rpow_mul_natCast hTnonneg
        ((4 * (n + 3) : ℕ) : ℝ) 2).symm
  have hY : (T ^ (6 : ℕ)) ^ (1 - 2 * (n : ℝ)) =
      T ^ (6 * (1 - 2 * (n : ℝ))) := by
    exact (Real.rpow_natCast_mul hTnonneg 6
      (1 - 2 * (n : ℝ))).symm
  rw [mul_pow, hq2, hp, hp2, hY]
  rw [← Real.rpow_add hT, ← Real.rpow_add hT]
  congr 1
  norm_num
  ring

/- The first retained window by itself spends only a fraction of the
requested source epsilon budget. -/
theorem gmAffineIterationQ_cube_le
    {delta T : ℝ} (hdelta : 0 < delta) (hT : 1 ≤ T) :
    (T ^ gmAffineIterationEta delta) ^ (3 : ℕ) ≤ T ^ delta := by
  rw [gmAffineIterationQ_cube_eq delta (zero_le_one.trans hT)]
  apply Real.rpow_le_rpow_of_exponent_le hT
  have heta := ten_mul_gmAffineIterationEta_le hdelta.le
  linarith

/- The height-specialized recurrence produced by the complete three-region
Lemma 9.2 calculation.  Naming this proposition exposes the quantifier order
needed below: the decay order and analytic constants can be fixed before the
height and affine scale. -/
def GMAffineLemma92RecurrenceAt
    (delta Cdiv Ctail : ℝ) (n : ℕ) (T : ℝ)
    (hT : 0 < T) (f : SchwartzMap ℝ ℝ) (M : ℕ) : Prop :=
  ∃ M₁ M₂ M₃ : ℕ,
    (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
    gmAffineJ f M ≤
      (gmAffineRegionIConstant n) ^ 2 * T ^ delta *
          (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
        (Cdiv * gmAffineRegionIICoreConstant * T ^ delta *
          (M : ℝ) ^ 2 *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz
                (gmAffineSecondPoissonCutoff T
                  (T ^ gmAffineIterationEta delta) M₂ M₃ /
                  (T ^ gmAffineIterationEta delta))
                (by
                  apply div_pos
                  · exact gmAffineSecondPoissonCutoff_pos
                      hT (Real.rpow_pos_of_pos hT _)
                  · exact Real.rpow_pos_of_pos hT _) f) M₂)) +
          gmAffineRegionIITailAbsorptionConstant n f Cdiv Ctail) +
        2 * gmAffineRegionIIIEnvelopeConstant n f ^ 2

/- Lemma 9.2 recurrence with every omitted-frequency term expressed as a
function-independent multiple of the current positive mass squared. -/
def GMAffineLemma92MassRecurrenceAt
    (delta Cdiv D : ℝ) (n : ℕ) (T : ℝ)
    (hT : 0 < T) (f : SchwartzMap ℝ ℝ) (M : ℕ) : Prop :=
  ∃ M₁ M₂ M₃ : ℕ,
    (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
    gmAffineJ f M ≤
      (gmAffineRegionIConstant n) ^ 2 * T ^ delta *
          (M : ℝ) ^ 6 * (∫ x : ℝ, f x) ^ 2 +
        (Cdiv * gmAffineRegionIICoreConstant * T ^ delta *
          (M : ℝ) ^ 2 *
          (Real.sqrt (∫ u : ℝ, f u ^ 2) *
            Real.sqrt (gmAffineJ
              (gmAffineTildeSchwartz
                (gmAffineSecondPoissonCutoff T
                  (T ^ gmAffineIterationEta delta) M₂ M₃ /
                  (T ^ gmAffineIterationEta delta))
                (by
                  apply div_pos
                  · exact gmAffineSecondPoissonCutoff_pos
                      hT (Real.rpow_pos_of_pos hT _)
                  · exact Real.rpow_pos_of_pos hT _) f) M₂)) +
          gmAffineRegionIITailMassConstant n Cdiv D *
            (∫ x : ℝ, f x) ^ 2) +
        2 * gmAffineRegionIIIEnvelopeMassConstant n D ^ 2 *
          (∫ x : ℝ, f x) ^ 2

/-! ### Source Proposition 9.1 by finite natural-number descent -/


