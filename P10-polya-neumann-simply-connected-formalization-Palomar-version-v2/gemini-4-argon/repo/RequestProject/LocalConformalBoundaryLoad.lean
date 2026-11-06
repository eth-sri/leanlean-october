module

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Real
open scoped InnerProductSpace ComplexConjugate ContDiff

variable {τ : ℝ → ℝ} {c : ℝ}

local notation "Φ0" => IsC1TraceReparam τ c

private theorem boundaryLoad_reparam_image_Icc  
    (hτ : Φ0) :
    τ '' Icc 0 (2 * π) = Icc 0 (2 * π) := by
  simpa [hτ.zero, hτ.endpoint] using
    hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
      (hτ.monotone.monotoneOn _)

private theorem boundaryLoad_integrable_reparam_weight
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (hτ : Φ0) {q : ℝ → V}
    (hq : IntegrableOn q (Ioc 0 (2 * π))) :
    IntegrableOn (fun θ => deriv τ θ • q (τ θ)) (Ioc 0 (2 * π)) := by
  exact (integrableOn_Icc_iff_integrableOn_Ioc
    (f := fun θ => deriv τ θ • q (τ θ)) (by finiteness)).mp ((integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Icc (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt) (hτ.monotone.monotoneOn (Icc 0 (2 * π))) q).mp (by simpa [boundaryLoad_reparam_image_Icc hτ] using ((integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr hq)))

/-- Change of variables for an arbitrary complex integrand, with ordinary
coordinate measure on both cuts. -/
theorem integral_traceReparam_conormal  
    (hτ : Φ0) (q : ℝ → ℂ) :
    (∫ θ in Ioc 0 (2 * π), deriv τ θ • q (τ θ)) =
      ∫ s in Ioc 0 (2 * π), q s := by
  simpa [boundaryLoad_reparam_image_Icc hτ, integral_Icc_eq_integral_Ioc]
    using (integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Icc (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt) (hτ.monotone.monotoneOn (Icc 0 (2 * π))) q).symm

private theorem boundaryLoad_weighted_norm_sq_le (d K : ℝ) (z : ℂ)
    (hd : 0 ≤ d) (hdK : d ≤ K) : ‖d • z‖ ^ 2 ≤ K * (d * ‖z‖ ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, mul_pow]
  have h := mul_le_mul_of_nonneg_right hdK (mul_nonneg hd (sq_nonneg ‖z‖))
  nlinarith

/-- Every actual L² boundary density has an actual L² transformed conormal
density. The input need not have a continuous representative. -/
theorem traceReparamConormal_memLp  
    (hτ : Φ0) (g : BoundaryL2) :
    MemLp (fun θ => deriv τ θ • g (τ θ)) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
  have hG := boundaryLoad_integrable_reparam_weight hτ ((Lp.memLp g).integrable (by norm_num))
  have hweight : IntegrableOn (fun θ => deriv τ θ * ‖g (τ θ)‖ ^ 2)
      (Ioc 0 (2 * π)) := by
    simpa using boundaryLoad_integrable_reparam_weight hτ ((memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).mp (Lp.memLp g))
  obtain ⟨K, hK⟩ := hτ.lipschitz
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  refine (hweight.const_mul K).mono' (by
    simp only [pow_two]
    exact hG.aestronglyMeasurable.norm.mul hG.aestronglyMeasurable.norm) (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact boundaryLoad_weighted_norm_sq_le (deriv τ θ) K (g (τ θ))
    hτ.monotone.deriv_nonneg
    ((le_abs_self _).trans (by simpa using
      (norm_deriv_le_of_lipschitz hK)))

/-- The transformed conormal density in the actual ordinary boundary L²
space. Multiplication by the real derivative is the physical Jacobian. -/
def traceReparamConormalL2  
    (hτ : Φ0) (g : BoundaryL2) : BoundaryL2 :=
  (traceReparamConormal_memLp hτ g).toLp (fun θ => deriv τ θ • g (τ θ))

theorem traceReparamConormalL2_ae  
    (hτ : Φ0) g :
    (traceReparamConormalL2 hτ g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))] fun θ => deriv τ θ • g (τ θ) :=
  (traceReparamConormal_memLp hτ g).coeFn_toLp

private theorem boundaryLoad_half_pairing q t b
    (hq : ∀ n, q n = (Real.sqrt (sobWeight n) : ℂ) * t n) :
    ⟪q, sobolevSmoothing (1 / 2) (by norm_num) b⟫_ℂ = ⟪t, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', hq, sobolevSmoothing, diagOp_apply,
    map_mul, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (sobWeight n)) *
        (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) * (conj (t n) * b n) := by ring
    _ = _ := by rw [show (Real.sqrt _ : ℂ) * (_ ^ (-(1 / 2 : ℝ)) : ℝ) = 1 by
      rw [Real.rpow_neg (sobWeight_pos n).le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
      exact mul_inv_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos n)).ne'), one_mul]

/-- The genuine weak load for the actual conformal half trace. Its unitary
Fourier normalization is `sqrt (2π) Λ⁻¹ᐟ² Ĝ`, including frequency zero. -/
def localConformalBoundaryLoad  
    (hτ : Φ0) (g : BoundaryL2) : L2Z :=
  sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
    (boundaryFourier (traceReparamConormalL2 hτ g))

section LocalConformal

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Metric.ball 0 R))
    (hb : Bornology.IsBounded (F '' Metric.ball 0 1))
    (hL : IsLipschitzDomain (F '' Metric.ball 0 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hinj : InjOn F (Metric.ball 0 1)) {C : ℝ}
    (hC : ∀ z ∈ Metric.ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' Metric.ball 0 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hhol hinj hC hcoord

/-- Pairing the actual conformal half trace with the constructed weak load
is exactly the ordinary physical boundary pairing, for all H¹ vectors. -/
theorem localConformalBoundaryLoad_inner
    (u : NeumannH1 (F '' Metric.ball 0 1)) g :
    ⟪localConformalDiskHalfTrace hR F hFs hL u, localConformalBoundaryLoad hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ u, g⟫_ℂ := by
  have hhalf := boundaryLoad_half_pairing
    (localConformalDiskHalfTrace hR F hFs hL u)
    (boundaryFourier (localConformalDiskH1Trace hR F hFs hL u))
    (boundaryFourier (traceReparamConormalL2 hτ g))
    (fun n => by simpa [sobWeight] using
      localConformalDiskHalfTrace_apply hR F hFs hL u n)
  exact hhalf.trans ((boundaryFourier.inner_map_map _ _).trans (by
    rw [← localConformalDiskH1Trace_eq_reparam hR F hFs hb hL hhol hinj hC hγ hτ hcoord]
    exact (by
      refine (denseRange_smoothTraceH1Lin hb hL).induction_on
        (p := fun v =>
          ⟪h1ReparamBoundaryTrace hL hγ hτ v, traceReparamConormalL2 hτ g⟫_ℂ =
            ⟪h1BoundaryTrace hb hL hγ v, g⟫_ℂ) u ?_ ?_
      · exact isClosed_eq
          ((h1ReparamBoundaryTrace hL hγ hτ).continuous.inner continuous_const)
          ((h1BoundaryTrace hb hL hγ).continuous.inner continuous_const)
      · intro f
        rw [smoothTraceH1Lin_apply, h1BoundaryTrace_inner_smooth hb hL hγ f g,
          L2.inner_def]
        calc
          _ = ∫ θ in Ioc 0 (2 * π),
              conj (f (γ (τ θ))) * (deriv τ θ • g (τ θ)) := by
            apply integral_congr_ae
            filter_upwards [h1ReparamBoundaryTrace_smooth_ae hb hL hγ hτ f,
              traceReparamConormalL2_ae hτ g] with θ htrace hload
            simp only [RCLike.inner_apply', htrace, hload]
          _ = ∫ θ in Ioc 0 (2 * π),
              deriv τ θ • (conj (f (γ (τ θ))) * g (τ θ)) := by
            apply integral_congr_ae
            exact Eventually.of_forall fun θ => (by
              simp
              ring)
          _ = _ := integral_traceReparam_conormal hτ (fun θ => conj (f (γ θ)) * g θ))))

/-- An actual physical weak Neumann solution is the actual normalized
solution with the constructed conformal weak load. -/
theorem isBoundaryNeumannSolution_isNormalizedNeumannSolution 
    g u
    (hu : IsBoundaryNeumannSolution hb hL hγ E g u) :
    IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (localConformalBoundaryLoad hτ g) u := by
  intro v
  exact (hu v).trans
    (localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord v g).symm

end LocalConformal

end PolyaNeumann

end
