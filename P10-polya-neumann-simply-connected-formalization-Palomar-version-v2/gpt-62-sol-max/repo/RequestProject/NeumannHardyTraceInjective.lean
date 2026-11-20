module

public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannConstantTrace
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Uniqueness from the actual Hardy trace

The first-order conjugate Green identity is extended from compact smooth
restrictions to the genuine weak-gradient H¹ space. A zero actual trace
therefore makes the Cauchy--Riemann equation valid against global compact
tests. Its distributional Laplacian vanishes across the boundary. The
existing second-order Green identity then gives the zero-energy form
equation, whose genuine constants have injective actual trace.

No smoothness, Neumann equation, or spectral premise is imposed on the
input H¹ vector. Boundary measure is ordinary dθ and the boundary direction
in the first-order identity is the actual conjugate velocity.

This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

section FirstOrder

variable {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
include hγ hφ

theorem firstOrder_boundary_coefficient_memLp 
    (a : ℝ → ℂ) (ha : AEStronglyMeasurable a volume) {K : ℝ}
    (hK : ∀ θ, ‖a θ‖ ≤ K) :
    MemLp (fun θ => φ (γ θ) * a θ) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  have hC0 := (norm_nonneg (φ 0)).trans (hC 0)
  apply MemLp.of_bound
    ((hφ.1.continuous.comp hKγ.continuous).aestronglyMeasurable.mul ha).restrict (C * K)
  apply Eventually.of_forall
  intro θ
  change ‖φ (γ θ) * a θ‖ ≤ C * K
  rw [norm_mul]
  exact mul_le_mul (hC (γ θ)) (hK θ) (norm_nonneg _) hC0

/-- The velocity or its conjugate in the complex Green identity. -/
def boundaryVelocity (γ : ℝ → ℂ) (conjugated : Bool) (θ : ℝ) : ℂ :=
  if conjugated then conj (deriv γ θ) else deriv γ θ

def boundaryVelocitySign (conjugated : Bool) : ℂ := if conjugated then -Complex.I else Complex.I

theorem firstOrder_signed_velocity_coefficient_memLp (c : Bool) :
    MemLp (fun θ => φ (γ θ) * boundaryVelocity γ c θ) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  refine firstOrder_boundary_coefficient_memLp hγ hφ _ ?_ (K := K) fun θ => ?_
  · cases c
    · exact (measurable_deriv γ).aestronglyMeasurable
    · exact Complex.continuous_conj.comp_aestronglyMeasurable (measurable_deriv γ).aestronglyMeasurable
  · cases c <;> simpa [boundaryVelocity] using norm_deriv_le_of_lipschitz (x₀ := θ) hK

omit hφ in
variable (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) in
include hb hL in
private theorem smooth_firstOrder_green  {p : ℂ → ℂ} (hp : TestFunction univ p) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * deriv γ θ) =
      Complex.I * (∫ z in Ω, dirD p 1 z) - ∫ z in Ω, dirD p Complex.I z := by
  obtain ⟨Kp, hKp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hp.2.1 hp.1 (by simp)
  have hg : (∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * deriv γ θ) =
      2 * Complex.I * ∫ z in Ω, dbar p z := by
    simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
      using integral_boundary_eq_dbar hb hL hγ hKp hp.2.1
  have hdx : IntegrableOn (dirD p 1) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD 1).memLp' 1)
  have hdy : IntegrableOn (dirD p Complex.I) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD Complex.I).memLp' 1)
  calc
    _ = 2 * Complex.I * ∫ z in Ω, dbar p z := hg
    _ = ∫ z in Ω, (Complex.I * dirD p 1 z - dirD p Complex.I z) := by grind [integral_const_mul, dbar, dirD, Complex.I_sq]
    _ = _ := by rw [integral_sub (hdx.const_mul _) hdy, integral_const_mul]


omit hφ in
private theorem smooth_signed_firstOrder_green (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {p : ℂ → ℂ} (hp : TestFunction univ p) (c : Bool) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * boundaryVelocity γ c θ) =
      boundaryVelocitySign c * (∫ z in Ω, dirD p 1 z) - ∫ z in Ω, dirD p Complex.I z := by
  cases c
  · exact smooth_firstOrder_green hγ hb hL hp
  · have h := congrArg conj (smooth_firstOrder_green hγ hb hL hp.conj)
    simp only [map_sub, map_mul, Complex.conj_I, ← integral_conj,
      dirD_conj (hp.1.of_le (by simp)), Complex.conj_conj] at h
    exact h

/-- Green's formula extends by density for both choices of velocity. -/
theorem h1_firstOrder_green (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (c : Bool) (u : NeumannH1 Ω) :
    boundaryVelocitySign c * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
      ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) + ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
    ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * boundaryVelocity γ c θ) := by
  let B := (lpIntegralPair (firstOrder_signed_velocity_coefficient_memLp hγ hφ c)).comp
    (h1BoundaryTrace hb hL hγ)
  let P (i : Fin 2) := (lpIntegralPair (hφ.memLp' 2)).comp (h1Gradient Ω i) +
    (lpIntegralPair ((hφ.dirD (coordDir i)).memLp' 2)).comp (h1Value Ω)
  let T := boundaryVelocitySign c • P 0 - P 1
  have hB (w : NeumannH1 Ω) : B w = ∫ θ in Ioc (0 : ℝ) (2 * π),
      h1BoundaryTrace hb hL hγ w θ * (φ (γ θ) * boundaryVelocity γ c θ) :=
    lpIntegralPair_apply (firstOrder_signed_velocity_coefficient_memLp hγ hφ c) _
  have hP (i : Fin 2) (w : NeumannH1 Ω) : P i w = (∫ z in Ω, h1Gradient Ω i w z * φ z) +
      ∫ z in Ω, h1Value Ω w z * dirD φ (coordDir i) z := by
    simp  [P, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, lpIntegralPair_apply]
  -- On a compact smooth restriction the two interior terms are a product derivative.
  have eq : (T : NeumannH1 Ω → ℂ) = B := by
    apply (denseRange_smoothTraceH1Lin hb hL).equalizer T.continuous B.continuous
    funext f
    change T (smoothTraceH1 Ω f) = B (smoothTraceH1 Ω f)
    let p := fun z => f z * φ z
    have hp : TestFunction univ p := ⟨f.property.1.mul hφ.1, f.property.2.1.mul_right, subset_univ _⟩
    have hB' : B (smoothTraceH1 Ω f) = ∫ θ in Ioc (0 : ℝ) (2 * π), p (γ θ) * boundaryVelocity γ c θ := by
      rw [hB]
      refine integral_congr_ae ?_
      filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
      rw [hθ, ← mul_assoc]
    have hP' (i : Fin 2) : P i (smoothTraceH1 Ω f) = ∫ z in Ω, dirD p (coordDir i) z := by
      rw [hP, h1Value_smoothTraceH1]
      have e (z : ℂ) : dirD p (coordDir i) z = dirD f (coordDir i) z * φ z + f z * dirD φ (coordDir i) z := by
        simp [p, dirD, fderiv_fun_mul (f.property.1.differentiable (by simp) z)
          (hφ.1.differentiable (by simp) z)]
        ring
      simp_rw [e, integral_add (integrable_mul_test ((f.property.dirD _).memLp' 2) hφ)
        (integrable_mul_test (f.property.memLp' 2) (hφ.dirD (coordDir i)))]
      congr 1 <;> apply integral_congr_ae
      · filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz using congrArg (· * φ z) hz
      · filter_upwards [(smoothTraceTests_memLp Ω f).coeFn_toLp] with z hz using congrArg (· * dirD φ (coordDir i) z) hz
    rw [hB', smooth_signed_firstOrder_green hγ hb hL hp c]
    simp  [T, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hP',
      coordDir_zero, coordDir_one]
  simpa only [T, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hP, hB,
    coordDir_zero, coordDir_one] using congrFun eq u

end FirstOrder

private theorem hardy_zeroTrace_boundary_test {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (ht : h1BoundaryTrace hb hL hγ u = 0) (a : ℝ → ℂ) :
    (∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ * a θ) = 0 := by
  apply integral_eq_zero_of_ae
  rw [ht]
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) (2 * π)))] with θ hθ
  simp_all

private theorem hardy_gradient_test_factor {Ω : Set ℂ} (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) (ψ : ℂ → ℂ) :
    (∫ z in Ω, h1Gradient Ω 0 u z * ψ z) =
      Complex.I * ∫ z in Ω, h1Gradient Ω 1 u z * ψ z := by
  rw [hCR]
  calc
    _ = ∫ z in Ω, Complex.I * (h1Gradient Ω 1 u z * ψ z) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul Complex.I (h1Gradient Ω 1 u)] with z hz
      rw [hz]
      change (Complex.I * h1Gradient Ω 1 u z) * ψ z =
        Complex.I * (h1Gradient Ω 1 u z * ψ z)
      ring
    _ = _ := integral_const_mul _ _

private theorem hardy_firstOrder_algebra (A B G : ℂ)
    (h : -Complex.I * (Complex.I * G + A) - (G + B) = 0) : A = Complex.I * B := by
  have he : -Complex.I * (Complex.I * G + A) - (G + B) = -Complex.I * A - B := by
    ring_nf; simp
  rw [he] at h
  apply sub_eq_zero.mp
  calc
    A - Complex.I * B = Complex.I * (-Complex.I * A - B) := by
      ring_nf; simp
    _ = 0 := by simp_all

/-- CR and zero physical trace give the first-order distribution identity
against global compact tests, rather than only tests supported inside Ω. -/
theorem h1_antiholomorphic_global_test_of_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) =
      Complex.I * ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z := by
  have h := h1_firstOrder_green hγ hφ hb hL true u
  dsimp only [boundaryVelocitySign, boundaryVelocity] at h
  rw [hardy_zeroTrace_boundary_test hb hL hγ u ht,
    hardy_gradient_test_factor u hCR] at h
  exact hardy_firstOrder_algebra _ _ _ h

/-- The zero extension has zero distributional Laplacian, expressed using
its domain integral and arbitrary global compact smooth tests. -/
theorem h1_antiholomorphic_global_lap_test_of_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∫ z in Ω, h1Value Ω u z * lap φ z) = 0 := by
  have hx := h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht (hφ.dirD 1)
  have hy := h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht
    (hφ.dirD Complex.I)
  have hc : (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) Complex.I z) =
      ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) 1 z := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      change h1Value Ω u z * dirD (dirD φ 1) Complex.I z =
        h1Value Ω u z * dirD (dirD φ Complex.I) 1 z
      rw [dirD_comm_at hφ.1.contDiffAt])
  have hix := integrable_mul_test (Lp.memLp (h1Value Ω u)) ((hφ.dirD 1).dirD 1)
  have hiy := integrable_mul_test (Lp.memLp (h1Value Ω u))
    ((hφ.dirD Complex.I).dirD Complex.I)
  calc
    _ = (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) 1 z) +
        ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z := by
      simp  [lap, mul_add]
      exact integral_add hix hiy
    _ = Complex.I * (Complex.I * ∫ z in Ω,
        h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z) +
        ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z := by simp_all
    _ = 0 := by rw [← mul_assoc, Complex.I_mul_I]; ring

private theorem hardy_zeroTrace_gradient_test {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) = 0 := by
  have hg := h1_doubleLayer_green hb hL hγ hφ u
  rw [h1_antiholomorphic_global_lap_test_of_zero_trace hb hL hγ u hCR ht hφ,
    zero_add, hardy_zeroTrace_boundary_test hb hL hγ u ht] at hg
  exact hg

private theorem hardy_gradient_inner_smooth (Ω : Set ℂ) (u : NeumannH1 Ω)
    (f : smoothTraceTests) (i : Fin 2) :
    ⟪h1Gradient Ω i (smoothTraceH1 Ω f), h1Gradient Ω i u⟫_ℂ =
      ∫ z in Ω, h1Gradient Ω i u z * dirD (fun w => conj (f w)) (coordDir i) z := by
  rw [h1Gradient_smoothTraceH1]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply', hz]
  rw [dirD_conj (f.property.1.of_le (by simp))]
  exact mul_comm _ _

/-- The zero-energy form equation is proved from CR and zero trace. It is
a conclusion here, not an assumed Neumann PDE for the Hardy input. -/
theorem h1HelmholtzForm_zero_of_antiholomorphic_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0) : h1HelmholtzForm Ω 0 u = 0 := by
  have heq : (fun v : NeumannH1 Ω => ⟪v, h1HelmholtzForm Ω 0 u⟫_ℂ) =
      (fun _ => (0 : ℂ)) := by
    apply (denseRange_smoothTraceH1Lin hb hL).equalizer
      (continuous_id.inner continuous_const) continuous_const
    funext f
    change ⟪smoothTraceH1 Ω f, h1HelmholtzForm Ω 0 u⟫_ℂ = 0
    rw [h1HelmholtzForm_inner]
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    simp_rw [hardy_gradient_inner_smooth]
    exact hardy_zeroTrace_gradient_test hb hL hγ u hCR ht f.property.conj
  apply ext_inner_left ℂ
  intro v
  rw [inner_zero_right]
  exact congrFun heq v

/-- A genuine weak antiholomorphic H¹ vector with zero actual physical
trace is zero. The domain and parametrization are the original physical ones. -/
theorem neumannH1_eq_zero_of_antiholomorphic_zero_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u : NeumannH1 Ω)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (ht : h1BoundaryTrace hb hL hγ u = 0) : u = 0 := by
  have hu := h1HelmholtzForm_zero_of_antiholomorphic_zero_trace hb hL hγ u hCR ht
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨c, hcu⟩ := (h1HelmholtzForm_zero_eq_zero_iff_constant hb hL.1 u).mp hu
  have hc : c = 0 := by
    apply (boundaryLpConst_eq_zero_iff c).mp
    rw [← h1BoundaryTrace_h1Constant hb hL hγ c, ← hcu]
    exact ht
  apply h1Value_injective hL.1.1
  simp_all

/-- Equal actual traces identify actual weak antiholomorphic H¹ vectors. -/
theorem neumannH1_eq_of_antiholomorphic_same_trace {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u v : NeumannH1 Ω)
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hv : h1Gradient Ω 0 v = Complex.I • h1Gradient Ω 1 v)
    (ht : h1BoundaryTrace hb hL hγ u = h1BoundaryTrace hb hL hγ v) : u = v := by
  apply sub_eq_zero.mp
  apply neumannH1_eq_zero_of_antiholomorphic_zero_trace hb hL hγ (u - v)
  · rw [map_sub, map_sub, hu, hv, smul_sub]
  simp_all

end PolyaNeumann

end
