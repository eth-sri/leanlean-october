module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalTrace
public import RequestProject.NeumannNormalizedBoundary
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Topology.Order.Compact

/-!
# Actual boundary loads in supplied conformal coordinates

The physical density is an arbitrary element of the ordinary `dθ` boundary
L² space. Under the proved change of parameter its conormal density is
`τ' • (g ∘ τ)`. The one-dimensional Jacobian theorem constructs this as an
actual L² element, and density of smooth H¹ restrictions proves its pairing
with every actual H¹ trace. The normalized load is `Λ⁻¹ᐟ²` of the unitary
boundary Fourier transform, so its average Fourier coefficients carry
exactly `sqrt (2π)`. No constant-speed claim is made about the conformal
circle image, and coordinate existence remains a separate obligation.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Real
open scoped InnerProductSpace ComplexConjugate

section
variable {τ } {c } (hτ : IsC1TraceReparam τ c)

include τ c hτ in
private theorem boundaryLoad_reparam_image_Icc :
    τ '' boundaryInterval = boundaryInterval := by
  simpa  [hτ.zero, hτ.endpoint] using
    hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
      (hτ.monotone.monotoneOn _)

private theorem boundaryLoad_integrable_reparam_weight
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (hτ : IsC1TraceReparam τ c) {q : ℝ → V}
    (hq : IntegrableOn q boundaryHalfOpenInterval) :
    IntegrableOn (fun θ => deriv τ θ • q (τ θ)) boundaryHalfOpenInterval := by
  have hq'  :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr hq
  have hi := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn (Icc 0 circlePeriod)) q).mp
      (by grind only [boundaryLoad_reparam_image_Icc])
  exact (integrableOn_Icc_iff_integrableOn_Ioc
    (f := fun θ => deriv τ θ • q (τ θ)) (by finiteness)).mp hi

include τ c hτ in
/-- Change of variables for an arbitrary complex integrand, with ordinary
coordinate measure on both cuts. -/
theorem integral_traceReparam_conormal (q : ComplexCurve) :
    (∫ θ in boundaryHalfOpenInterval, deriv τ θ • q (τ θ)) =
      ∫ s in boundaryHalfOpenInterval, q s := by
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn (Icc 0 circlePeriod)) q
  simpa  [boundaryLoad_reparam_image_Icc hτ, integral_Icc_eq_integral_Ioc]
    using h.symm

private theorem boundaryLoad_weighted_norm_sq_le d K (z : ℂ)
    (hd : 0 ≤ d) (hdK : d ≤ K) : ‖d • z‖ ^ 2 ≤ K * (d * ‖z‖ ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, mul_pow]
  have h := mul_le_mul_of_nonneg_right hdK (mul_nonneg hd (sq_nonneg ‖z‖))
  nlinarith

include τ c hτ in
/-- Every actual L² boundary density has an actual L² transformed conormal
density. The input need not have a continuous representative. -/
theorem traceReparamConormal_memLp (g : BoundaryL2) :
    MemLp (fun θ => deriv τ θ • g (τ θ)) 2
      (volume.restrict boundaryHalfOpenInterval) := by
  have hg  :=
    (Lp.memLp g).integrable (by norm_num)
  have hG := boundaryLoad_integrable_reparam_weight hτ hg
  have hg2  :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).mp (Lp.memLp g)
  have hweight : IntegrableOn (fun θ => deriv τ θ * ‖g (τ θ)‖ ^ 2)
      boundaryHalfOpenInterval := by
    simpa   using boundaryLoad_integrable_reparam_weight hτ hg2
  obtain ⟨K, hK⟩ := hτ.lipschitz
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  have hmeas : AEStronglyMeasurable (fun θ => ‖deriv τ θ • g (τ θ)‖ ^ 2)
      (volume.restrict boundaryHalfOpenInterval) := by
    simp only [pow_two]
    exact hG.aestronglyMeasurable.norm.mul hG.aestronglyMeasurable.norm
  refine (hweight.const_mul K).mono' hmeas (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact boundaryLoad_weighted_norm_sq_le (deriv τ θ) K (g (τ θ))
    hτ.monotone.deriv_nonneg
    ((le_abs_self _).trans (by simpa   using
      (norm_deriv_le_of_lipschitz hK)))

/-- The transformed conormal density in the actual ordinary boundary L²
space. Multiplication by the real derivative is the physical Jacobian. -/
def traceReparamConormalL2 {τ } {c }
    (hτ : IsC1TraceReparam τ c) g  :=
  (traceReparamConormal_memLp hτ g).toLp (fun θ => deriv τ θ • g (τ θ))

include τ c hτ in
theorem traceReparamConormalL2_ae g :
    (traceReparamConormalL2 hτ g : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval] fun θ => deriv τ θ • g (τ θ) :=
  (traceReparamConormal_memLp hτ g).coeFn_toLp

end


private theorem boundaryLoad_complex_pairing_weight (a z : ℂ) (d : ℝ) :
    a * (d • z) = d • (a * z) := by
  simp  
  ring

/-- Reparametrization preserves the actual physical load pairing against
every H¹ vector. The identity is proved from Jacobian substitution on the
dense smooth restrictions, rather than supplied as a premise. -/
theorem h1ReparamBoundaryTrace_inner_conormalL2 
    (hb : Bornology.IsBounded Ω) hL
     (hγ : IsBoundaryParam Ω γ)
      (hτ : IsC1TraceReparam τ c)
    u g :
    ⟪h1ReparamBoundaryTrace hL hγ hτ u, traceReparamConormalL2 hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hL hγ u, g⟫_ℂ := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v =>
      ⟪h1ReparamBoundaryTrace hL hγ hτ v, traceReparamConormalL2 hτ g⟫_ℂ =
        ⟪h1BoundaryTrace hL hγ v, g⟫_ℂ) u ?_ ?_
  · exact isClosed_eq
      ((h1ReparamBoundaryTrace hL hγ hτ).continuous.inner continuous_const)
      ((h1BoundaryTrace hL hγ).continuous.inner continuous_const)
  · intro f
    rw [smoothTraceH1Lin_apply, h1BoundaryTrace_inner_smooth hb hL hγ f g,
      L2.inner_def]
    calc
      _ = ∫ θ in Ioc 0 circlePeriod,
          conj (f (γ (τ θ))) * (deriv τ θ • g (τ θ)) := by
        apply integral_congr_ae
        filter_upwards [h1ReparamBoundaryTrace_smooth_ae hb hL hγ hτ f,
          traceReparamConormalL2_ae hτ g] with θ htrace hload
        simp only [RCLike.inner_apply', htrace, hload]
      _ = ∫ θ in Ioc 0 circlePeriod,
          deriv τ θ • (conj (f (γ (τ θ))) * g (τ θ)) := by
        grind only [boundaryLoad_complex_pairing_weight, PolyaNeumann.smoothTraceTests]
      _ = _ := integral_traceReparam_conormal hτ (fun θ => conj (f (γ θ)) * g θ)

private theorem boundaryLoad_sqrt_weight_cancel w (hw : 0 < w) :
    (Real.sqrt w : ℂ) * ((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
  rw [Real.rpow_neg hw.le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  exact mul_inv_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr hw).ne')

theorem common_boundaryLoad_half_pairing q t b
    (hq : ∀ n, q n = (Real.sqrt (sobWeight n) : ℂ) * t n) :
    ⟪q, sobolevSmoothing (1 / 2 : ℝ) (by norm_num) b⟫_ℂ = ⟪t, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', hq, sobolevSmoothing, diagOp_apply,
    map_mul, Complex.conj_ofReal]
  grind [sobWeight, boundaryLoad_sqrt_weight_cancel, PolyaNeumann.sobWeight]

/-- The genuine weak load for the actual conformal half trace. Its unitary
Fourier normalization is `sqrt (2π) Λ⁻¹ᐟ² Ĝ`, including frequency zero. -/
def localConformalBoundaryLoad {τ } {c }
    (hτ : IsC1TraceReparam τ c) g  :=
  sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
    (boundaryFourier (traceReparamConormalL2 hτ g))

section LocalConformal

variable {R } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) {C }
    (hC : DiskInverseJacobianBound F C)
    {γ } (hγ : IsBoundaryParam (F '' unitDisk) γ)
    {τ } {c } (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ))

include hb hhol hinj hC hcoord

/-- Pairing the actual conformal half trace with the constructed weak load
is exactly the ordinary physical boundary pairing, for all H¹ vectors. -/
theorem localConformalBoundaryLoad_inner
    u g :
    ⟪localConformalDiskHalfTrace hR F hFs hL u, localConformalBoundaryLoad hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hL hγ u, g⟫_ℂ := by
  have hhalf := common_boundaryLoad_half_pairing
    (localConformalDiskHalfTrace hR F hFs hL u)
    (boundaryFourier (localConformalDiskH1Trace hR F hFs hL u))
    (boundaryFourier (traceReparamConormalL2 hτ g))
    (fun n => by rfl)
  have hordinary :
      ⟪localConformalDiskH1Trace hR F hFs hL u, traceReparamConormalL2 hτ g⟫_ℂ =
        ⟪h1BoundaryTrace hL hγ u, g⟫_ℂ := by
    rw [← localConformalDiskH1Trace_eq_reparam hR F hFs hb hL hhol hinj hC hγ hτ hcoord]
    simp_all [h1ReparamBoundaryTrace_inner_conormalL2]
  exact hhalf.trans ((boundaryFourier.inner_map_map _ _).trans hordinary)

/-- An actual physical weak Neumann solution is the actual normalized
solution with the constructed conformal weak load. -/
theorem isBoundaryNeumannSolution_isNormalizedNeumannSolution 
    g u
    (hu : IsBoundaryNeumannSolution hL hγ E g u) :
    IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ g) u := by
  intro v
  exact (hu v).trans
    (localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord v g).symm

end LocalConformal

end PolyaNeumann

end
