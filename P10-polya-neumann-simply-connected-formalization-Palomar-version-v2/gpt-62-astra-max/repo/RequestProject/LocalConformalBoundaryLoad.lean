module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalTrace
public import RequestProject.NeumannNormalizedBoundary
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Topology.Order.Compact
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Real
open scoped InnerProductSpace ComplexConjugate

private theorem boundaryLoad_reparam_image_Icc {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) :
    τ '' angleInterval = angleInterval := by
  simpa only [hτ.zero, hτ.endpoint] using
    hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
      (hτ.monotone.monotoneOn _)

private theorem boundaryLoad_integrable_reparam_weight
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) {q : ℝ → V}
    (hq : IntegrableOn q angleIoc) :
    IntegrableOn (fun θ => deriv τ θ • q (τ θ)) angleIoc := by
  have hq'  :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr hq
  have hi := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn angleInterval) q).mp
      (by simpa only [boundaryLoad_reparam_image_Icc hτ] using hq')
  exact (integrableOn_Icc_iff_integrableOn_Ioc
     (by finiteness)).mp hi

/-- Change of variables for an arbitrary complex integrand, with ordinary
coordinate measure on both cuts. -/
theorem integral_traceReparam_conormal {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (q : ℝ → ℂ) :
    (∫ θ in angleIoc, deriv τ θ • q (τ θ)) =
      ∫ s in angleIoc, q s := by
  
  simpa only [boundaryLoad_reparam_image_Icc hτ, integral_Icc_eq_integral_Ioc]
    using (integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc
      (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
      (hτ.monotone.monotoneOn angleInterval) q).symm

private theorem boundaryLoad_weighted_norm_sq_le (d K : ℝ) (z : ℂ)
    (hd : 0 ≤ d) (hdK : d ≤ K) : ‖d • z‖ ^ 2 ≤ K * (d * ‖z‖ ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, mul_pow]
  have h := mul_le_mul_of_nonneg_right hdK (mul_nonneg hd (sq_nonneg ‖z‖))
  nlinarith

/-- Every actual L² boundary density has an actual L² transformed conormal
density. The input need not have a continuous representative. -/
theorem traceReparamConormal_memLp {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) :
    MemLp (fun θ => deriv τ θ • g (τ θ)) 2
      angleMeasure := by
  
  have hG := boundaryLoad_integrable_reparam_weight hτ ((Lp.memLp g).integrable (by norm_num))
  have hg2  :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mp (Lp.memLp g)
  
  obtain ⟨K, hK⟩ := hτ.lipschitz
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  
  refine ((boundaryLoad_integrable_reparam_weight hτ hg2).const_mul K).mono' (by
    simp only [pow_two]
    exact hG.aestronglyMeasurable.norm.mul hG.aestronglyMeasurable.norm) (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact boundaryLoad_weighted_norm_sq_le (deriv τ θ) K (g (τ θ))
    hτ.monotone.deriv_nonneg
    ((le_abs_self _).trans ((norm_deriv_le_of_lipschitz hK)))

/-- The transformed conormal density in the actual ordinary boundary L²
space. Multiplication by the real derivative is the physical Jacobian. -/
def traceReparamConormalL2 {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) : BoundaryL2 :=
  (traceReparamConormal_memLp hτ g).toLp (fun θ => deriv τ θ • g (τ θ))

theorem traceReparamConormalL2_ae {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) :
    (traceReparamConormalL2 hτ g : ℝ → ℂ)
      =ᵐ[angleMeasure] fun θ => deriv τ θ • g (τ θ) :=
  (traceReparamConormal_memLp hτ g).coeFn_toLp

private theorem boundaryLoad_complex_pairing_weight (a z : ℂ) (d : ℝ) :
    a * (d • z) = d • (a * z) := by
  simp
  ring

/-- Reparametrization preserves the actual physical load pairing against
every H¹ vector. The identity is proved from Jacobian substitution on the
dense smooth restrictions, rather than supplied as a premise. -/
theorem h1ReparamBoundaryTrace_inner_conormalL2 {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (u : NeumannH1 Ω) (g : BoundaryL2) :
    ⟪h1ReparamBoundaryTrace hL hγ hτ u, traceReparamConormalL2 hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hL hγ u, g⟫_ℂ := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
     u ?_ ?_
  · exact isClosed_eq
      ((by fun_prop))
      ((by fun_prop))
  · intro f
    rw [smoothTraceH1Lin_apply, h1BoundaryTrace_inner_smooth hb hL hγ f g,
      L2.inner_def]
    calc
      _ = ∫ θ in angleIoc,
          conj (f (γ (τ θ))) * (deriv τ θ • g (τ θ)) := by
        apply integral_congr_ae
        filter_upwards [h1ReparamBoundaryTrace_smooth_ae hb hL hγ hτ f,
          traceReparamConormalL2_ae hτ g] with θ htrace hload
        simp only [RCLike.inner_apply', htrace, hload]
      _ = ∫ θ in angleIoc,
          deriv τ θ • (conj (f (γ (τ θ))) * g (τ θ)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun θ => boundaryLoad_complex_pairing_weight _ _ _
      _ = _ := integral_traceReparam_conormal hτ (fun θ => conj (f (γ θ)) * g θ)

private theorem boundaryLoad_sqrt_weight_cancel (w : ℝ) (hw : 0 < w) :
    (Real.sqrt w : ℂ) * ((w ^ (-halfOrder) : ℝ) : ℂ) = 1 := by
  rw [Real.rpow_neg hw.le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
  exact mul_inv_cancel₀ (by exact_mod_cast (by positivity))

theorem boundaryLoad_half_pairing (q t b : L2Z)
    (hq : ∀ n, q n = (Real.sqrt (sobWeight n) : ℂ) * t n) :
    ⟪q, sobolevSmoothing halfOrder (by norm_num) b⟫_ℂ = ⟪t, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', hq, sobolevSmoothing, diagOp_apply,
    map_mul, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (sobWeight n)) *
        ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ)) * (conj (t n) * b n) := by ring
    _ = _ := by rw [boundaryLoad_sqrt_weight_cancel _ (sobWeight_pos n), one_mul]

/-- The genuine weak load for the actual conformal half trace. Its unitary
Fourier normalization is `sqrt (2π) Λ⁻¹ᐟ² Ĝ`, including frequency zero. -/
def localConformalBoundaryLoad {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) : L2Z :=
  sobolevSmoothing halfOrder (by norm_num)
    (boundaryFourier (traceReparamConormalL2 hτ g))

section LocalConformal

/-- Pairing the actual conformal half trace with the constructed weak load
is exactly the ordinary physical boundary pairing, for all H¹ vectors. -/
theorem localConformalBoundaryLoad_inner (Φ : ConformalDiskMap) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (u : NeumannH1 Φ.domain) (g : BoundaryL2) :
    ⟪Φ.pulledBackHalfTrace Φ.lipschitzDomain u, localConformalBoundaryLoad hτ g⟫_ℂ =
      ⟪h1BoundaryTrace Φ.lipschitzDomain hγ u, g⟫_ℂ := by
  have hhalf := boundaryLoad_half_pairing
    (Φ.pulledBackHalfTrace Φ.lipschitzDomain u)
    (boundaryFourier (Φ.pulledBackTrace Φ.lipschitzDomain u))
    (boundaryFourier (traceReparamConormalL2 hτ g))
    (fun n => localConformalDiskHalfTrace_apply Φ Φ.lipschitzDomain u n)
  have hordinary :
      ⟪Φ.pulledBackTrace Φ.lipschitzDomain u, traceReparamConormalL2 hτ g⟫_ℂ =
        ⟪h1BoundaryTrace Φ.lipschitzDomain hγ u, g⟫_ℂ := by
    rw [← localConformalDiskH1Trace_eq_reparam Φ hγ hτ hcoord]
    exact h1ReparamBoundaryTrace_inner_conormalL2 Φ.bounded Φ.lipschitzDomain hγ hτ u g
  exact hhalf.trans ((boundaryFourier.inner_map_map _ _).trans hordinary)

/-- An actual physical weak Neumann solution is the actual normalized
solution with the constructed conformal weak load. -/
theorem isBoundaryNeumannSolution_isNormalizedNeumannSolution (Φ : ConformalDiskMap) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {E : ℝ} (g : BoundaryL2)
    (u : NeumannH1 Φ.domain) (hu : IsBoundaryNeumannSolution Φ.bounded Φ.lipschitzDomain hγ E g u) :
    IsNormalizedNeumannSolution (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E
      (localConformalBoundaryLoad hτ g) u := by
  intro v
  exact (hu v).trans
    (localConformalBoundaryLoad_inner Φ hγ hτ hcoord v g).symm

end LocalConformal

end PolyaNeumann

end
