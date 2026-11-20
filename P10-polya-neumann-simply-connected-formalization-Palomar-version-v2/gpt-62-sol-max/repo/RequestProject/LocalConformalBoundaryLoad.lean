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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Real
open scoped InnerProductSpace ComplexConjugate

private theorem boundaryLoad_reparam_image_Icc {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) :
    τ '' Icc (0 : ℝ) (2 * π) = Icc (0 : ℝ) (2 * π) := by
  simpa only [hτ.zero, hτ.endpoint] using
    hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le
      (hτ.monotone.monotoneOn _)

section

variable {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
include hτ

private theorem traceReparam_deriv (θ : ℝ) :
    HasDerivWithinAt τ (deriv τ θ) (Icc 0 (2 * π)) θ :=
  (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt

private theorem boundaryLoad_integrable_reparam_weight
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℝ → V}
    (hq : IntegrableOn q (Ioc (0 : ℝ) (2 * π))) :
    IntegrableOn (fun θ => deriv τ θ • q (τ θ)) (Ioc (0 : ℝ) (2 * π)) := by
  have h := integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Icc (fun θ _ => traceReparam_deriv hτ θ) (hτ.monotone.monotoneOn _) q
  rw [boundaryLoad_reparam_image_Icc hτ, integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top,
    integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top] at h
  exact h.mp hq

/-- Change of variables with ordinary coordinate measure on both cuts. -/
theorem integral_traceReparam_conormal {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q : ℝ → V) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), deriv τ θ • q (τ θ)) =
      ∫ s in Ioc (0 : ℝ) (2 * π), q s := by
  simpa only [boundaryLoad_reparam_image_Icc hτ, integral_Icc_eq_integral_Ioc] using
    (integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Icc
      (fun θ _ => traceReparam_deriv hτ θ) (hτ.monotone.monotoneOn _) q).symm

/-- The positive Jacobian preserves null sets in the cut. -/
theorem isC1TraceReparam_ae_comp {p : ℝ → Prop}
    (hp : ∀ᵐ s ∂volume.restrict (Ioc 0 (2 * π)), p s) :
    ∀ᵐ θ ∂volume.restrict (Ioc 0 (2 * π)), p (τ θ) := by
  classical
  let q : ℝ → ℝ := fun s => if p s then 0 else 1
  have hz : q =ᵐ[volume.restrict (Ioc 0 (2 * π))] 0 := hp.mono fun s hs => by simp [q, hs]
  have hq : IntegrableOn q (Ioc 0 (2 * π)) := (integrable_zero _ _ _).congr hz.symm
  have hj := boundaryLoad_integrable_reparam_weight hτ hq
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))] (fun θ => deriv τ θ • q (τ θ)) :=
    Eventually.of_forall fun θ => mul_nonneg hτ.monotone.deriv_nonneg (by positivity)
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hj).mp (by
    rw [integral_traceReparam_conormal hτ q, integral_congr_ae hz]; simp)
  filter_upwards [he, ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hτ.lower_ae]
    with θ hθ hlo
  by_contra hbad
  have hd : 0 < deriv τ θ := hτ.lower_pos.trans_le hlo
  simp [q, hbad, hd.ne', smul_eq_mul] at hθ

end

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
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  have hg :=
    (Lp.memLp g).integrable (by norm_num)
  have hG := boundaryLoad_integrable_reparam_weight hτ hg
  have hg2 :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).mp (Lp.memLp g)
  have hweight : IntegrableOn (fun θ => deriv τ θ * ‖g (τ θ)‖ ^ 2)
      (Ioc (0 : ℝ) (2 * π)) := by
    exact boundaryLoad_integrable_reparam_weight hτ hg2
  obtain ⟨K, hK⟩ := hτ.lipschitz
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  have hmeas : AEStronglyMeasurable (fun θ => ‖deriv τ θ • g (τ θ)‖ ^ 2)
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
    simp only [pow_two]
    exact hG.aestronglyMeasurable.norm.mul hG.aestronglyMeasurable.norm
  refine (hweight.const_mul (K : ℝ)).mono' hmeas (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact boundaryLoad_weighted_norm_sq_le (deriv τ θ) (K : ℝ) (g (τ θ))
    hτ.monotone.deriv_nonneg
    ((le_abs_self _).trans (norm_deriv_le_of_lipschitz hK))

section

variable {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c) (g : BoundaryL2)
include τ c hτ g

/-- The transformed conormal density in the actual ordinary boundary L²
space. Multiplication by the real derivative is the physical Jacobian. -/
def traceReparamConormalL2  : BoundaryL2 :=
  (traceReparamConormal_memLp hτ g).toLp (fun θ => deriv τ θ • g (τ θ))

theorem traceReparamConormalL2_ae  :
    (traceReparamConormalL2 hτ g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => deriv τ θ • g (τ θ) :=
  (traceReparamConormal_memLp hτ g).coeFn_toLp

end

private theorem boundaryLoad_complex_pairing_weight (a z : ℂ) (d : ℝ) :
    a * (d • z) = d • (a * z) := by grind [Complex.real_smul]

/-- Reparametrization preserves the actual physical load pairing against
every H¹ vector. The identity is proved from Jacobian substitution on the
dense smooth restrictions, rather than supplied as a premise. -/
theorem h1ReparamBoundaryTrace_inner_conormalL2 {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (u : NeumannH1 Ω) (g : BoundaryL2) :
    ⟪h1ReparamBoundaryTrace hL hγ hτ u, traceReparamConormalL2 hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ u, g⟫_ℂ := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v =>
      ⟪h1ReparamBoundaryTrace hL hγ hτ v, traceReparamConormalL2 hτ g⟫_ℂ =
        ⟪h1BoundaryTrace hb hL hγ v, g⟫_ℂ) u ?_ ?_
  · exact isClosed_eq
      ((h1ReparamBoundaryTrace hL hγ hτ).continuous.inner continuous_const)
      ((h1BoundaryTrace hb hL hγ).continuous.inner continuous_const)
  · intro f
    rw [smoothTraceH1Lin_apply, h1BoundaryTrace_inner_smooth hb hL hγ f g]
    calc
      _ = ∫ θ in Ioc (0 : ℝ) (2 * π),
          conj (f (γ (τ θ))) * (deriv τ θ • g (τ θ)) := by
        apply integral_congr_ae
        filter_upwards [h1ReparamBoundaryTrace_smooth_ae hb hL hγ hτ f,
          traceReparamConormalL2_ae hτ g] with θ htrace hload
        simp only [RCLike.inner_apply', htrace, hload]
      _ = ∫ θ in Ioc (0 : ℝ) (2 * π),
          deriv τ θ • (conj (f (γ (τ θ))) * g (τ θ)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun θ => boundaryLoad_complex_pairing_weight _ _ _
      _ = _ := integral_traceReparam_conormal hτ (fun θ => conj (f (γ θ)) * g θ)

/-- The genuine weak load for the actual conformal half trace. Its unitary
Fourier normalization is `sqrt (2π) Λ⁻¹ᐟ² Ĝ`, including frequency zero. -/
def localConformalBoundaryLoad {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) : L2Z :=
  sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
    (boundaryFourier (traceReparamConormalL2 hτ g))

section LocalConformal

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' Metric.ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hcoord

/-- Pairing the actual conformal half trace with the constructed weak load
is exactly the ordinary physical boundary pairing, for all H¹ vectors. -/
theorem localConformalBoundaryLoad_inner
    (u : NeumannH1 (F '' Metric.ball (0 : ℂ) 1)) (g : BoundaryL2) :
    ⟪coords.halfTrace u, localConformalBoundaryLoad hτ g⟫_ℂ =
      ⟪h1BoundaryTrace coords.bounded coords.lipschitz hγ u, g⟫_ℂ := by
  have hhalf := inner_sobolevSmoothing_half
    (coords.halfTrace u)
    (boundaryFourier (coords.trace u))
    (boundaryFourier (traceReparamConormalL2 hτ g))
    (fun n => by rfl)
  have hordinary :
      ⟪coords.trace u, traceReparamConormalL2 hτ g⟫_ℂ =
        ⟪h1BoundaryTrace coords.bounded coords.lipschitz hγ u, g⟫_ℂ := by
    rw [← localConformalDiskH1Trace_eq_reparam coords hγ hτ hcoord]
    exact h1ReparamBoundaryTrace_inner_conormalL2 coords.bounded coords.lipschitz hγ hτ u g
  exact hhalf.trans ((boundaryFourier.inner_map_map _ _).trans hordinary)

/-- An actual physical weak Neumann solution is the actual normalized
solution with the constructed conformal weak load. -/
theorem isBoundaryNeumannSolution_isNormalizedNeumannSolution {E : ℝ}
    (g : BoundaryL2) (u : NeumannH1 (F '' Metric.ball (0 : ℂ) 1))
    (hu : IsBoundaryNeumannSolution coords.bounded coords.lipschitz hγ E g u) :
    IsNormalizedNeumannSolution (coords.halfTrace) E
      (localConformalBoundaryLoad hτ g) u := by
  intro v
  exact (hu v).trans
    (localConformalBoundaryLoad_inner coords hγ hτ hcoord v g).symm

end LocalConformal

end PolyaNeumann

end
