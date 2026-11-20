module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalMass
public import Mathlib.Tactic
public import RequestProject.PlanarNotation

/-!
# Conformal invariance of the actual weak antiholomorphic defect

The defect is the genuine L² vector `dx u - i • dy u`, constructed from the
weak-gradient components of the actual H¹ space. For smooth restrictions the
composition differential multiplies this defect by `deriv F`. The actual
conformal Jacobian change of variables proves equality of its squared L² norms.
Density in the genuine H¹ norm extends this equality to every H¹ vector.

The coordinate map is supplied and holomorphic only on the open disk. No weak
derivative transfer formula, Hardy hypothesis, or PDE regularity is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

section

variable (Ω : Set ℂ) (Φ : SmoothDiskMap) (hhol : DifferentiableOn ℂ Φ.map unitDisk)
    (hinj : InjOn Φ.map unitDisk) (f : smoothTraceTests)

/-- The actual weak antiholomorphic defect, without the irrelevant factor 1/2. -/
def h1AntiholomorphicDefect : NeumannH1 Ω →L[ℂ] L2 Ω :=
  h1Gradient Ω 0 - Complex.I • h1Gradient Ω 1

@[simp] theorem h1AntiholomorphicDefect_apply (u : NeumannH1 Ω) :
    h1AntiholomorphicDefect Ω u = h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u := rfl

/-- The corresponding actual smooth differential. -/
def antiholomorphicDifferential (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I

/-- The real-linear computation behind conformal invariance of this defect. -/
theorem realCLM_antiholomorphic_factor (A : ℂ →L[ℝ] ℂ) (c : ℂ) :
    A c - Complex.I * A (c * Complex.I) =
      c * (A 1 - Complex.I * A Complex.I) := by
  rw [realCLM_apply_complex A c, realCLM_apply_complex A (c * Complex.I)]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;> ring

/-- The smooth H¹ defect has its genuine almost-everywhere representative. -/
theorem h1AntiholomorphicDefect_smooth_ae :
    (h1AntiholomorphicDefect Ω (smoothTraceH1 Ω f) : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      antiholomorphicDifferential (f : ℂ → ℂ) := by
  let u := smoothTraceH1 Ω f
  have h0 : (h1Gradient Ω 0 u) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ f z (coordDir 0) :=
    (smoothTraceTests_memLp_deriv Ω f 0).coeFn_toLp
  have h1 : (h1Gradient Ω 1 u) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ f z (coordDir 1) :=
    (smoothTraceTests_memLp_deriv Ω f 1).coeFn_toLp
  change (h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u : L2 Ω)
      =ᵐ[volume.restrict Ω]
    antiholomorphicDifferential f
  filter_upwards [Lp.coeFn_sub (h1Gradient Ω 0 u) (Complex.I • h1Gradient Ω 1 u),
    Lp.coeFn_smul Complex.I (h1Gradient Ω 1 u), h0, h1] with z hsub hsmul hx hy
  rw [hsub]
  simp [hsmul]
  simp [*]
  rfl

theorem norm_sq_h1AntiholomorphicDefect_smooth :
    ‖h1AntiholomorphicDefect Ω (smoothTraceH1 Ω f)‖ ^ 2 =
      ∫ z in Ω, ‖antiholomorphicDifferential (f : ℂ → ℂ) z‖ ^ 2 := by
  rw [← integral_norm_sq_lp]
  exact integral_congr_ae
    ((h1AntiholomorphicDefect_smooth_ae Ω f).fun_comp (fun w : ℂ => ‖w‖ ^ 2))

include hhol in
/-- The actual chain differential of a smooth pullback, before integration. -/
theorem antiholomorphicDifferential_smoothDiskComposition {z : ℂ} (hz : z ∈ unitDisk) :
    antiholomorphicDifferential (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f : ℂ → ℂ) z =
      deriv Φ.map z * antiholomorphicDifferential (f : ℂ → ℂ) (Φ.map z) := by
  have hfd : ∀ v : ℂ, fderiv ℝ Φ.map z v = deriv Φ.map z * v := by
    intro v
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    exact fderiv_eq_deriv_mul
  unfold antiholomorphicDifferential
  rw [fderiv_smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f (ball_subset_closedBall hz)]
  simp only [ContinuousLinearMap.comp_apply, hfd, mul_one]
  exact realCLM_antiholomorphic_factor _ _

include hhol in
theorem norm_sq_antiholomorphicDifferential_smoothDiskComposition {z : ℂ} (hz : z ∈ unitDisk) :
    ‖antiholomorphicDifferential (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f : ℂ → ℂ) z‖ ^ 2 =
      ‖deriv Φ.map z‖ ^ 2 * ‖antiholomorphicDifferential (f : ℂ → ℂ) (Φ.map z)‖ ^ 2 := by
  rw [antiholomorphicDifferential_smoothDiskComposition Φ hhol f hz,
    norm_mul, mul_pow]

include hhol hinj in
/-- The exact Jacobian cancels the conformal differential weight. -/
theorem integral_antiholomorphicDifferential_smoothDiskComposition :
    (∫ z in unitDisk,
      ‖antiholomorphicDifferential (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f : ℂ → ℂ) z‖ ^ 2) =
      ∫ w in Φ.domain, ‖antiholomorphicDifferential (f : ℂ → ℂ) w‖ ^ 2 := by
  rw [localConformal_integral_image isOpen_ball hhol hinj]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  exact norm_sq_antiholomorphicDifferential_smoothDiskComposition Φ hhol f hz

end

section SuppliedCoordinates

section

variable (Φ : ConformalDiskMap) (u : NeumannH1 Φ.domain)

/-- Conformal invariance for every vector of the actual weak-gradient H¹ space. -/
theorem localConformalH1Pullback_antiholomorphicDefect_norm_sq :
    ‖h1AntiholomorphicDefect unitDisk
      (Φ.h1Pullback Φ.lipschitzDomain u)‖ ^ 2 =
      ‖h1AntiholomorphicDefect Φ.domain u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain).induction_on
     u ?_ ?_
  · exact isClosed_eq
      (((h1AntiholomorphicDefect unitDisk).continuous.comp
        (Φ.h1Pullback Φ.lipschitzDomain).continuous).norm.pow 2)
      ((h1AntiholomorphicDefect Φ.domain).continuous.norm.pow 2)
  · intro f
    change ‖h1AntiholomorphicDefect unitDisk
      (Φ.h1Pullback Φ.lipschitzDomain
        (smoothTraceH1 Φ.domain f))‖ ^ 2 =
      ‖h1AntiholomorphicDefect Φ.domain
        (smoothTraceH1 Φ.domain f)‖ ^ 2
    rw [localConformalH1Pullback_smooth Φ,
      norm_sq_h1AntiholomorphicDefect_smooth, norm_sq_h1AntiholomorphicDefect_smooth]
    exact integral_antiholomorphicDifferential_smoothDiskComposition Φ Φ.holomorphic Φ.inj f

theorem localConformalH1Pullback_antiholomorphicDefect_norm :
    ‖h1AntiholomorphicDefect unitDisk
      (Φ.h1Pullback Φ.lipschitzDomain u)‖ =
      ‖h1AntiholomorphicDefect Φ.domain u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (localConformalH1Pullback_antiholomorphicDefect_norm_sq Φ u)

/-- The stable zero-equivalence used to transport an actual disk weak CR equation. -/
theorem localConformalH1Pullback_antiholomorphicDefect_eq_zero_iff :
    h1AntiholomorphicDefect unitDisk (Φ.h1Pullback Φ.lipschitzDomain u) = 0 ↔
      h1AntiholomorphicDefect Φ.domain u = 0 := by
  have hn := localConformalH1Pullback_antiholomorphicDefect_norm Φ u
  constructor
  · intro hd
    apply norm_eq_zero.mp
    rw [← hn, hd, norm_zero]
  · intro hp
    apply norm_eq_zero.mp
    rw [hn, hp, norm_zero]

theorem localConformalH1Pullback_antiholomorphic_iff :
    h1Gradient unitDisk 0 (Φ.h1Pullback Φ.lipschitzDomain u) =
        Complex.I • h1Gradient unitDisk 1 (Φ.h1Pullback Φ.lipschitzDomain u) ↔
      h1Gradient Φ.domain 0 u =
        Complex.I • h1Gradient Φ.domain 1 u := by
  simpa [sub_eq_zero] using
    localConformalH1Pullback_antiholomorphicDefect_eq_zero_iff Φ u

end

end SuppliedCoordinates

end PolyaNeumann

end
