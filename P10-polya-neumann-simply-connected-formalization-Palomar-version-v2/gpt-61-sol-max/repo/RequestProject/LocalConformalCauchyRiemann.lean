module

public import RequestProject.LocalConformalH1


public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalMass
public import Mathlib.Tactic

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric

/-- The actual weak antiholomorphic defect, without the irrelevant factor 1/2. -/
def h1AntiholomorphicDefect (Ω : PlanarSet) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  h1Gradient Ω 0 - Complex.I • h1Gradient Ω 1

@[simp] theorem h1AntiholomorphicDefect_apply Ω u :
    h1AntiholomorphicDefect Ω u = h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u := rfl

/-- The corresponding actual smooth differential. -/
def antiholomorphicDifferential f z  :=
  fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I

/-- The real-linear computation behind conformal invariance of this defect. -/
theorem realCLM_antiholomorphic_factor (A : ℂ →L[ℝ] ℂ) c :
    A c - Complex.I * A (c * Complex.I) =
      c * (A 1 - Complex.I * A Complex.I) := by
  rw [common_realCLM_apply_complex A c, common_realCLM_apply_complex A (c * Complex.I)]
  apply Complex.ext <;>
    simp   <;> ring

/-- The smooth H¹ defect has its genuine almost-everywhere representative. -/
theorem h1AntiholomorphicDefect_smooth_ae Ω f :
    (h1AntiholomorphicDefect Ω (smoothTraceH1 Ω f) : PlaneMap) =ᵐ[volume.restrict Ω]
      antiholomorphicDifferential (f : PlaneMap) := by
  let u := smoothTraceH1 Ω f
  have h0 : (h1Gradient Ω 0 u : PlaneMap) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (f : PlaneMap) z (coordDir 0) :=
    (smoothTraceTests_memLp_deriv Ω f 0).coeFn_toLp
  have h1 : (h1Gradient Ω 1 u : PlaneMap) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (f : PlaneMap) z (coordDir 1) :=
    (smoothTraceTests_memLp_deriv Ω f 1).coeFn_toLp
  change ((h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u))
      =ᵐ[volume.restrict Ω]
    antiholomorphicDifferential f
  filter_upwards [Lp.coeFn_sub (h1Gradient Ω 0 u) (Complex.I • h1Gradient Ω 1 u),
    Lp.coeFn_smul Complex.I (h1Gradient Ω 1 u), h0, h1] with z hsub hsmul hx hy
  rw [hsub]
  simp  
  rw [hsmul]
  simp  
  rw [hx, hy]
  rfl

theorem norm_sq_h1AntiholomorphicDefect_smooth Ω f :
    ‖h1AntiholomorphicDefect Ω (smoothTraceH1 Ω f)‖ ^ 2 =
      ∫ z in Ω, ‖antiholomorphicDifferential (f : PlaneMap) z‖ ^ 2 := by
  rw [norm_sq_L2_eq_integral]
  exact integral_congr_ae
    ((h1AntiholomorphicDefect_smooth_ae Ω f).fun_comp (fun w : ℂ => ‖w‖ ^ 2))

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk)
include R hR F hFs hhol

/-- The actual chain differential of a smooth pullback, before integration. -/
theorem antiholomorphicDifferential_smoothDiskComposition f
     (hz : z ∈ unitDisk) :
    antiholomorphicDifferential (smoothDiskCompositionLin hR F hFs f : PlaneMap) z =
      deriv F z * antiholomorphicDifferential (f : PlaneMap) (F z) := by
  have hfd : ∀ v : ℂ, fderiv ℝ F z v = deriv F z * v := by
    intro v
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    exact fderiv_eq_deriv_mul
  unfold antiholomorphicDifferential
  rw [fderiv_smoothDiskCompositionLin hR F hFs f (ball_subset_closedBall hz)]
  simp_all [realCLM_antiholomorphic_factor]

theorem norm_sq_antiholomorphicDifferential_smoothDiskComposition f
     (hz : z ∈ unitDisk) :
    ‖antiholomorphicDifferential (smoothDiskCompositionLin hR F hFs f : PlaneMap) z‖ ^ 2 =
      ‖deriv F z‖ ^ 2 * ‖antiholomorphicDifferential (f : PlaneMap) (F z)‖ ^ 2 := by
  rw [antiholomorphicDifferential_smoothDiskComposition hR F hFs hhol f hz,
    norm_mul, mul_pow]

/-- The exact Jacobian cancels the conformal differential weight. -/
theorem integral_antiholomorphicDifferential_smoothDiskComposition
    (hinj : InjOn F unitDisk) f :
    (∫ z in unitDisk,
      ‖antiholomorphicDifferential (smoothDiskCompositionLin hR F hFs f : PlaneMap) z‖ ^ 2) =
      ∫ w in F '' unitDisk, ‖antiholomorphicDifferential (f : PlaneMap) w‖ ^ 2 := by
  rw [localConformal_integral_image isOpen_ball hhol hinj]
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  simp_all [norm_sq_antiholomorphicDifferential_smoothDiskComposition]

end


section SuppliedCoordinates

variable {R C } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
local notation "h1PullbackFixed" => localConformalH1Pullback hR F hFs hL


section
variable (u : NeumannH1 (F '' unitDisk))
include u

section
include hb hhol hinj hC

/-- Conformal invariance for every vector of the actual weak-gradient H¹ space. -/
theorem localConformalH1Pullback_antiholomorphicDefect_norm_sq :
    ‖h1AntiholomorphicDefect unitDisk
      (h1PullbackFixed u)‖ ^ 2 =
      ‖h1AntiholomorphicDefect (F '' unitDisk) u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => ‖h1AntiholomorphicDefect (ball 0 1)
      (h1PullbackFixed v)‖ ^ 2 =
      ‖h1AntiholomorphicDefect (F '' ball 0 1) v‖ ^ 2) u ?_ ?_
  · exact isClosed_eq
      (((h1AntiholomorphicDefect (ball 0 1)).continuous.comp
        (h1PullbackFixed).continuous).norm.pow 2)
      ((h1AntiholomorphicDefect (F '' ball 0 1)).continuous.norm.pow 2)
  · intro f
    change ‖h1AntiholomorphicDefect (ball 0 1)
      (h1PullbackFixed
        (smoothTraceH1 (F '' ball 0 1) f))‖ ^ 2 =
      ‖h1AntiholomorphicDefect (F '' ball 0 1)
        (smoothTraceH1 (F '' ball 0 1) f)‖ ^ 2
    rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC,
      norm_sq_h1AntiholomorphicDefect_smooth, norm_sq_h1AntiholomorphicDefect_smooth]
    simp_all [integral_antiholomorphicDifferential_smoothDiskComposition]

theorem localConformalH1Pullback_antiholomorphicDefect_norm :
    ‖h1AntiholomorphicDefect unitDisk
      (h1PullbackFixed u)‖ =
      ‖h1AntiholomorphicDefect (F '' unitDisk) u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (localConformalH1Pullback_antiholomorphicDefect_norm_sq hR F hFs hb hL hhol hinj hC u)

/-- The stable zero-equivalence used to transport an actual disk weak CR equation. -/
theorem localConformalH1Pullback_antiholomorphicDefect_eq_zero_iff :
    h1AntiholomorphicDefect unitDisk (h1PullbackFixed u) = 0 ↔
      h1AntiholomorphicDefect (F '' unitDisk) u = 0 := by
  have hn := localConformalH1Pullback_antiholomorphicDefect_norm hR F hFs hb hL hhol hinj hC u
  constructor
  · intro hd
    apply norm_eq_zero.mp
    rw [← hn, hd, norm_zero]
  measurability

theorem localConformalH1Pullback_antiholomorphic_iff :
    h1Gradient unitDisk 0 (h1PullbackFixed u) =
        Complex.I • h1Gradient unitDisk 1 (h1PullbackFixed u) ↔
      h1Gradient (F '' unitDisk) 0 u =
        Complex.I • h1Gradient (F '' unitDisk) 1 u := by
  simpa  [sub_eq_zero] using
    localConformalH1Pullback_antiholomorphicDefect_eq_zero_iff hR F hFs hb hL hhol hinj hC u

end


end


end SuppliedCoordinates

end PolyaNeumann

end
