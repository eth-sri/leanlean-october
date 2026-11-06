module

public import RequestProject.LocalConformalAreaOrientation


public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

open scoped ContDiff

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

theorem hardyConjugateVelocityTest_memLp  
    (hγ : IsBoundaryParam Ω γ)  (hφ : TestFunction univ φ) :
    MemLp (fun θ => conj (φ (γ θ) * conj (deriv γ θ))) 2
      (volume.restrict boundaryHalfOpenInterval) := (firstOrder_conjugate_velocity_coefficient_memLp hγ hφ).star

/-- The actual conjugate-velocity boundary test is an L² class. -/
def hardyConjugateVelocityTestL2 {Ω } {γ }
    (hγ : IsBoundaryParam Ω γ) {φ } (hφ : TestFunction univ φ)  :=
  (hardyConjugateVelocityTest_memLp hγ hφ).toLp
    (fun θ => conj (φ (γ θ) * conj (deriv γ θ)))

/-- A continuous first-order boundary functional on the actual H¹ space. -/
def h1FirstOrderConjugateBoundaryTest {Ω : PlanarSet} (hL : IsLipschitzDomain Ω) {γ : ComplexCurve} (hγ : IsBoundaryParam Ω γ)
    {φ : PlaneMap} (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (hardyConjugateVelocityTestL2 hγ hφ)).comp (h1BoundaryTrace hL hγ)

/-- The two genuine weak derivatives and the smooth test derivatives
give a continuous first-order interior functional. -/
def h1FirstOrderConjugateInteriorTest (Ω : PlanarSet) {φ : PlaneMap}
    (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (-Complex.I) • ((smoothL2Pair Ω hφ).comp (h1Gradient Ω 0) +
      (smoothL2Pair Ω (hφ.dirD 1)).comp (h1Value Ω)) -
    ((smoothL2Pair Ω hφ).comp (h1Gradient Ω 1) +
      (smoothL2Pair Ω (hφ.dirD Complex.I)).comp (h1Value Ω))

theorem h1FirstOrderConjugateInteriorTest_apply Ω 
    (hφ : TestFunction univ φ) u :
    h1FirstOrderConjugateInteriorTest Ω hφ u =
      -Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) := by
  simp only [h1FirstOrderConjugateInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, smoothL2Pair_apply]

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ)
include Ω hb hL γ hγ

theorem h1FirstOrderConjugateBoundaryTest_apply  (hφ : TestFunction univ φ)
    u :
    h1FirstOrderConjugateBoundaryTest hL hγ hφ u =
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ u θ *
        (φ (γ θ) * conj (deriv γ θ)) := by
  apply integral_congr_ae
  filter_upwards [(hardyConjugateVelocityTest_memLp hγ hφ).coeFn_toLp] with θ hθ
  simp_all [hardyConjugateVelocityTestL2]

private theorem smooth_conjugate_firstOrder_green  (hp : TestFunction univ p) :
    (∫ θ in boundaryHalfOpenInterval, p (γ θ) * conj (deriv γ θ)) =
      -Complex.I * (∫ z in Ω, dirD p 1 z) - ∫ z in Ω, dirD p Complex.I z := by
  have h := congrArg conj (smooth_firstOrder_green hb hL hγ hp.conj)
  simpa only [map_sub, map_mul, Complex.conj_I, ← integral_conj,
    dirD_conj (hp.1.of_le (by simp)), Complex.conj_conj] using h

end




section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ)
include Ω hb hL γ hγ

section
variable {φ } (hφ : TestFunction univ φ)
include φ hφ

private theorem h1FirstOrderConjugate_green_smooth
    f :
    h1FirstOrderConjugateBoundaryTest hL hγ hφ (smoothTraceH1 Ω f) =
      h1FirstOrderConjugateInteriorTest Ω hφ (smoothTraceH1 Ω f) := by
  let p  := fun z => f z * φ z
  have hp : TestFunction univ p :=
    ⟨f.property.1.mul hφ.1, f.property.2.1.mul_right, subset_univ _⟩
  have hleft : h1FirstOrderConjugateBoundaryTest hL hγ hφ (smoothTraceH1 Ω f) =
      ∫ θ in boundaryHalfOpenInterval, p (γ θ) * conj (deriv γ θ) := by
    rw [h1FirstOrderConjugateBoundaryTest_apply hb]
    apply integral_congr_ae
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
    rw [hθ]
    ring
  have hproduct_integral := integral_dirD_smooth_mul Ω f hφ
  rw [hleft, smooth_conjugate_firstOrder_green hb hL hγ hp,
    hproduct_integral, hproduct_integral]
  have hdir0 : coordDir (0 : Coord) = (1 : ℂ) := rfl
  have hdir1 : coordDir (1 : Coord) = Complex.I := rfl
  simp only [h1FirstOrderConjugateInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, smoothL2Pair_smooth_gradient,
    smoothL2Pair_smooth_value, hdir0, hdir1]

/-- The first-order conjugate Green identity for every actual H¹ vector.
It is an equality of bounded functionals on a dense set of smooth restrictions. -/
theorem h1FirstOrderConjugateBoundaryTest_eq_interior :
    h1FirstOrderConjugateBoundaryTest hL hγ hφ = h1FirstOrderConjugateInteriorTest Ω hφ := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1FirstOrderConjugateBoundaryTest hL hγ hφ).continuous
    (h1FirstOrderConjugateInteriorTest Ω hφ).continuous
  ext <;> simp_all [h1FirstOrderConjugate_green_smooth]

/-- The raw first-order formula uses the genuine value, weak gradients,
and actual trace, with the unnormalized boundary measure dθ. -/
theorem h1_firstOrder_conjugate_green
    u :
    -Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
      ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ u θ *
        (φ (γ θ) * conj (deriv γ θ)) := by
  rw [← h1FirstOrderConjugateInteriorTest_apply Ω hφ u,
    ← h1FirstOrderConjugateBoundaryTest_eq_interior hb hL hγ hφ,
    h1FirstOrderConjugateBoundaryTest_apply hb]

end


private theorem hardy_zeroTrace_boundary_test u
    (ht : h1BoundaryTrace hL hγ u = 0) (a : ComplexCurve) :
    (∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ u θ * a θ) = 0 := by
  apply integral_eq_zero_of_ae
  rw [ht]
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 circlePeriod))] with θ hθ
  simp only [hθ, Pi.zero_apply, zero_mul]

end


private theorem hardy_gradient_test_factor  u
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) (ψ : PlaneMap) :
    (∫ z in Ω, h1Gradient Ω 0 u z * ψ z) =
      Complex.I * ∫ z in Ω, h1Gradient Ω 1 u z * ψ z := by
  rw [hCR]
  calc
    _ = ∫ z in Ω, Complex.I * (h1Gradient Ω 1 u z * ψ z) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul Complex.I (h1Gradient Ω 1 u)] with z hz
      rw [hz]
      exact mul_assoc _ _ _
    _ = _ := integral_const_mul _ _

private theorem hardy_firstOrder_algebra A B G
    (h : -Complex.I * (Complex.I * G + A) - (G + B) = 0) : A = Complex.I * B := by
  linear_combination Complex.I * h + (Complex.I * G + A) * Complex.I_sq

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL ) {γ } (hγ : IsBoundaryParam Ω γ) (u ) (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) (ht : h1BoundaryTrace hL hγ u = 0)

section
variable {φ : PlaneMap}
local notation "h1ValueFixed" => h1Value Ω u

include φ

include Ω hb hL γ hγ u hCR ht in
/-- CR and zero physical trace give the first-order distribution identity
against global compact tests, rather than only tests supported inside Ω. -/
theorem h1_antiholomorphic_global_test_of_zero_trace (hφ : TestFunction univ φ) :
    (∫ z in Ω, h1ValueFixed z * dirD φ 1 z) =
      Complex.I * ∫ z in Ω, h1ValueFixed z * dirD φ Complex.I z := by
  have h := h1_firstOrder_conjugate_green hb hL hγ hφ u
  rw [hardy_zeroTrace_boundary_test hb hL hγ u ht,
    hardy_gradient_test_factor u hCR] at h
  exact hardy_firstOrder_algebra _ _ _ h

section
include Ω hb hL γ hγ u hCR ht

/-- The zero extension has zero distributional Laplacian, expressed using
its domain integral and arbitrary global compact smooth tests. -/
theorem h1_antiholomorphic_global_lap_test_of_zero_trace (hφ : TestFunction univ φ) :
    (∫ z in Ω, h1ValueFixed z * lap φ z) = 0 := by
  have hx := h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht (hφ.dirD 1)
  have hy := h1_antiholomorphic_global_test_of_zero_trace hb hL hγ u hCR ht
    (hφ.dirD Complex.I)
  have hc : (∫ z in Ω, h1ValueFixed z * dirD (dirD φ 1) Complex.I z) =
      ∫ z in Ω, h1ValueFixed z * dirD (dirD φ Complex.I) 1 z := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      change h1ValueFixed z * dirD (dirD φ 1) Complex.I z =
        h1ValueFixed z * dirD (dirD φ Complex.I) 1 z
      rw [common_area_dirD_comm hφ.1])
  have hix := integrable_mul_test (Lp.memLp h1ValueFixed) ((hφ.dirD 1).dirD 1)
  have hiy := integrable_mul_test (Lp.memLp h1ValueFixed)
    ((hφ.dirD Complex.I).dirD Complex.I)
  calc
    _ = (∫ z in Ω, h1ValueFixed z * dirD (dirD φ 1) 1 z) +
        ∫ z in Ω, h1ValueFixed z * dirD (dirD φ Complex.I) Complex.I z := by
      simp  [lap, mul_add]
      exact integral_add hix hiy
    _ = Complex.I * (Complex.I * ∫ z in Ω,
        h1ValueFixed z * dirD (dirD φ Complex.I) Complex.I z) +
        ∫ z in Ω, h1ValueFixed z * dirD (dirD φ Complex.I) Complex.I z := by
      rw [hx, hc, hy]
    _ = 0 := by rw [← mul_assoc, Complex.I_mul_I]; ring

private theorem hardy_zeroTrace_gradient_test (hφ : TestFunction univ φ) :
    (∑ i : Coord, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) = 0 := by
  have hg := h1_doubleLayer_green hb hL hγ hφ u
  rw [h1_antiholomorphic_global_lap_test_of_zero_trace hb hL hγ u hCR ht hφ,
    zero_add, hardy_zeroTrace_boundary_test hb hL hγ u ht] at hg
  exact hg

end


end


private theorem hardy_gradient_inner_smooth Ω u
    f i :
    ⟪h1Gradient Ω i (smoothTraceH1 Ω f), h1Gradient Ω i u⟫_ℂ =
      ∫ z in Ω, h1Gradient Ω i u z * dirD (fun w => conj (f w)) (coordDir i) z := by
  rw [h1Gradient_smoothTraceH1, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply', hz]
  rw [dirD_conj (f.property.1.of_le (by simp))]
  exact mul_comm _ _

section
include Ω hb hL γ hγ u hCR ht

/-- The zero-energy form equation is proved from CR and zero trace. It is
a conclusion here, not an assumed Neumann PDE for the Hardy input. -/
theorem h1HelmholtzForm_zero_of_antiholomorphic_zero_trace : h1HelmholtzForm Ω 0 u = 0 := by
  have heq : (fun v : NeumannH1 Ω => ⟪v, h1HelmholtzForm Ω 0 u⟫_ℂ) =
      0 := by
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
theorem neumannH1_eq_zero_of_antiholomorphic_zero_trace : u = 0 := by
  have hu := h1HelmholtzForm_zero_of_antiholomorphic_zero_trace hb hL hγ u hCR ht
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨c, hcu⟩ := (h1HelmholtzForm_zero_eq_zero_iff_constant hb hL.1 u).mp hu
  have hc : c = 0 := by
    apply (boundaryLpConst_eq_zero_iff c).mp
    rw [← h1BoundaryTrace_h1Constant hb hL hγ c, ← hcu]
    exact ht
  apply h1Value_injective hL.1.1
  bound

end


end


/-- Equal actual traces identify actual weak antiholomorphic H¹ vectors. -/
theorem neumannH1_eq_of_antiholomorphic_same_trace 
    (hb : Bornology.IsBounded Ω) hL 
    (hγ : IsBoundaryParam Ω γ) u v
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hv : h1Gradient Ω 0 v = Complex.I • h1Gradient Ω 1 v)
    (ht : h1BoundaryTrace hL hγ u = h1BoundaryTrace hL hγ v) : u = v := by
  apply sub_eq_zero.mp
  apply neumannH1_eq_zero_of_antiholomorphic_zero_trace hb hL hγ (u - v)
  · rw [map_sub, map_sub, hu, hv, smul_sub]
  · rw [map_sub, ht, sub_self]

end PolyaNeumann

end
