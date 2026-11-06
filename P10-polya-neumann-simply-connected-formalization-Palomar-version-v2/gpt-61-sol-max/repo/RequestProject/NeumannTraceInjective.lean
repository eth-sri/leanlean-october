module

public import RequestProject.L2Pairing

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Topology.DenseEmbedding
public import RequestProject.NeumannBoundaryResolvent
public import RequestProject.Reconstruction

/-!
# The genuine trace is injective on Neumann eigenspaces

The classical double-layer Green identity first gives an equality of
continuous functionals on the dense smooth restrictions in H¹. It therefore
holds for every actual weak-gradient H¹ vector. If a Neumann eigenvector
has zero actual trace, its zero extension solves the global homogeneous
reconstruction equation. The already proved reconstruction uniqueness at
positive energy forces that extension, and hence the vector, to be zero.

The boundary measure is ordinary `dθ`, and the conormal test contains the
full density direction `-i γ′`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

lemma smoothConormalTest_memLp  
    (hγ : IsBoundaryParam Ω γ)  (hφ : TestFunction univ φ) :
    MemLp (fun θ => conj (fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)))) 2
      (volume.restrict boundaryHalfOpenInterval) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kφ, hKφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  have hc  :=
    (hφ.1.continuous_fderiv (by simp)).comp hKγ.continuous
  have hm : AEStronglyMeasurable
      (fun θ => fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.prodMk
        ((measurable_deriv γ).const_mul _).neg.aestronglyMeasurable)
  apply MemLp.of_bound
    (Complex.continuous_conj.comp_aestronglyMeasurable hm).restrict
    (Kφ * Kγ)
  apply Eventually.of_forall
  intro θ
  rw [Complex.norm_conj]
  calc
    _ ≤ ‖fderiv ℝ φ (γ θ)‖ * ‖-(Complex.I * deriv γ θ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ Kφ * Kγ := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
      exact mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hKφ)
        (norm_deriv_le_of_lipschitz hKγ) (norm_nonneg _) Kφ.coe_nonneg

/-- The actual conormal test, conjugated so that its pairing is linear in
the trace. It is constructed in L² rather than assumed bounded. -/
def smoothConormalTestL2 {Ω } {γ } (hγ : IsBoundaryParam Ω γ)
    {φ } hφ  :=
  (smoothConormalTest_memLp hγ hφ).toLp
    (fun θ => conj (fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))))

/-- The actual double-layer boundary functional on H¹. -/
def h1DoubleLayerBoundaryTest {Ω : PlanarSet} (hL : IsLipschitzDomain Ω) {γ : ComplexCurve} (hγ : IsBoundaryParam Ω γ)
    {φ : PlaneMap} (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (smoothConormalTestL2 hγ hφ)).comp (h1BoundaryTrace hL hγ)

def smoothL2Pair (Ω : PlanarSet) {φ : PlaneMap}
    (hφ : TestFunction univ φ) : L2 Ω →L[ℂ] ℂ :=
  lpPair (hφ.memLp' 2)

theorem smoothL2Pair_apply Ω 
    (hφ : TestFunction univ φ) u :
    smoothL2Pair Ω hφ u = ∫ z in Ω, u z * φ z := lpPair_apply (hφ.memLp' 2) u


section
variable (Ω : PlanarSet) {φ } (hφ : TestFunction univ φ) (f : smoothTraceTests)
include Ω φ hφ f

theorem smoothL2Pair_smooth_value :
    smoothL2Pair Ω hφ (h1Value Ω (smoothTraceH1 Ω f)) = ∫ z in Ω, f z * φ z := by
  rw [smoothL2Pair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp Ω f).coeFn_toLp] with z hz
  rw [h1Value_smoothTraceH1, hz]

theorem smoothL2Pair_smooth_gradient i :
    smoothL2Pair Ω hφ (h1Gradient Ω i (smoothTraceH1 Ω f)) =
      ∫ z in Ω, dirD (f : PlaneMap) (coordDir i) z * φ z := by
  rw [smoothL2Pair_apply]
  apply integral_congr_ae
  filter_upwards [(smoothTraceTests_memLp_deriv Ω f i).coeFn_toLp] with z hz
  simp_all [dirD]

end


/-- The interior Green expression is a continuous functional on the
genuine H¹ space. Its coefficients are actual smooth Laplacian/derivative
L² classes, not unspecified boundary regularity data. -/
def h1DoubleLayerInteriorTest (Ω : PlanarSet) {φ : PlaneMap} (hφ : TestFunction univ φ) :
    NeumannH1 Ω →L[ℂ] ℂ :=
  (smoothL2Pair Ω hφ.lap).comp (h1Value Ω) +
    ∑ i : Coord, (smoothL2Pair Ω (hφ.dirD (coordDir i))).comp (h1Gradient Ω i)

theorem h1DoubleLayerInteriorTest_apply Ω 
    (hφ : TestFunction univ φ) u :
    h1DoubleLayerInteriorTest Ω hφ u =
      (∫ z in Ω, h1Value Ω u z * lap φ z) +
        ∑ i : Coord, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z := by
  simp only [h1DoubleLayerInteriorTest, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, smoothL2Pair_apply]

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ) {φ } (hφ : TestFunction univ φ)

section
include Ω hb hL γ hγ φ hφ

theorem h1DoubleLayerBoundaryTest_apply u :
    h1DoubleLayerBoundaryTest hL hγ hφ u =
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ u θ *
        fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)) := by
  change ⟪smoothConormalTestL2 hγ hφ, h1BoundaryTrace hL hγ u⟫_ℂ = _
  apply integral_congr_ae
  filter_upwards [(smoothConormalTest_memLp hγ hφ).coeFn_toLp] with θ hθ
  simp_all [smoothConormalTestL2,  PolyaNeumann.NeumannH1, PolyaNeumann.BoundaryL2]

private lemma h1DoubleLayerBoundaryTest_smooth f :
    h1DoubleLayerBoundaryTest hL hγ hφ (smoothTraceH1 Ω f) =
      doubleLayer γ (fun θ => f (γ θ)) φ := by
  rw [h1DoubleLayerBoundaryTest_apply hb, doubleLayer,
    intervalIntegral.integral_of_le (by positivity)]
  apply integral_congr_ae
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
  rw [hθ]

end


private lemma h1DoubleLayerInteriorTest_smooth Ω
     (hφ : TestFunction univ φ) f :
    h1DoubleLayerInteriorTest Ω hφ (smoothTraceH1 Ω f) =
      ∫ z in Ω, (f z * lap φ z +
        ∑ i : Coord, dirD (f : PlaneMap) (coordDir i) z * dirD φ (coordDir i) z) := by
  rw [h1DoubleLayerInteriorTest_apply]
  have h0 : (∫ z in Ω, h1Value Ω (smoothTraceH1 Ω f) z * lap φ z) =
      ∫ z in Ω, f z * lap φ z := by
    apply integral_congr_ae
    filter_upwards [(f.property.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
    rw [h1Value_smoothTraceH1, hz]
  have hi : ∀ i : Coord,
      (∫ z in Ω, h1Gradient Ω i (smoothTraceH1 Ω f) z * dirD φ (coordDir i) z) =
        ∫ z in Ω, dirD (f : PlaneMap) (coordDir i) z * dirD φ (coordDir i) z := by
    intro i
    apply integral_congr_ae
    filter_upwards [((f.property.dirD (coordDir i)).memLp' 2
      (μ := volume.restrict Ω)).coeFn_toLp] with z hz
    exact congrArg (fun w => w * dirD φ (coordDir i) z) hz
  rw [h0]
  simp_rw [hi]
  have hmass := integrable_mul_test (f.property.memLp' 2 (μ := volume.restrict Ω)) hφ.lap
  have hgrad : ∀ i : Coord, IntegrableOn
      (((dirD (f : PlaneMap) (coordDir i) * dirD φ (coordDir i)))) Ω :=
    fun i => integrable_mul_test ((f.property.dirD (coordDir i)).memLp' 2) (hφ.dirD _)
  simp  
  exact ((integral_add hmass ((hgrad 0).add (hgrad 1))).trans
    (congrArg (fun x : ℂ => (∫ z in Ω, f z * lap φ z) + x)
      (integral_add (hgrad 0) (hgrad 1)))).symm

section
include Ω hb hL γ hγ φ hφ

/-- Green's double-layer identity for every actual weak-gradient H¹ vector.
It follows by equality of continuous functionals on the dense smooth
restrictions, so no extra regularity of the H¹ vector is imposed. -/
theorem h1DoubleLayerBoundaryTest_eq_interior :
    h1DoubleLayerBoundaryTest hL hγ hφ = h1DoubleLayerInteriorTest Ω hφ := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1DoubleLayerBoundaryTest hL hγ hφ).continuous
    (h1DoubleLayerInteriorTest Ω hφ).continuous
  funext f
  rw [Function.comp_apply, Function.comp_apply, smoothTraceH1Lin_apply,
    h1DoubleLayerBoundaryTest_smooth hb, h1DoubleLayerInteriorTest_smooth Ω]
  obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    f.property.2.1 f.property.1 (by simp)
  exact doubleLayer_eq_integral hb hL hγ hKf f.property.2.1 (fun θ _ => rfl) hφ.1

/-- The raw integral version of the generalized Green identity uses the
actual L² representatives of the value, weak gradients, and boundary trace. -/
theorem h1_doubleLayer_green u :
    (∫ z in Ω, h1Value Ω u z * lap φ z) +
      (∑ i : Coord, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) =
        ∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ u θ *
          fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)) := by
  rw [← h1DoubleLayerInteriorTest_apply Ω hφ u,
    ← h1DoubleLayerBoundaryTest_eq_interior hb hL hγ hφ,
    h1DoubleLayerBoundaryTest_apply hb hL hγ hφ u]

end


end


section
variable {Ω } {γ } (hγ : IsBoundaryParam Ω γ) {φ } (hφ : TestFunction univ φ)
include Ω γ hγ φ hφ

theorem firstOrder_boundary_coefficient_memLp
    a (ha : AEStronglyMeasurable a volume) 
    (hK : ∀ θ, ‖a θ‖ ≤ K) :
    MemLp (fun θ => φ (γ θ) * a θ) 2
      (volume.restrict boundaryHalfOpenInterval) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  have hC0  := (norm_nonneg (φ 0)).trans (hC 0)
  apply MemLp.of_bound
    ((hφ.1.continuous.comp hKγ.continuous).aestronglyMeasurable.mul ha).restrict (C * K)
  apply Eventually.of_forall
  intro θ
  change ‖φ (γ θ) * a θ‖ ≤ C * K
  rw [norm_mul]
  exact mul_le_mul (hC (γ θ)) (hK θ) (norm_nonneg _) hC0

theorem firstOrder_velocity_coefficient_memLp :
    MemLp (fun θ => φ (γ θ) * deriv γ θ) 2
      (volume.restrict boundaryHalfOpenInterval) := (Exists.casesOn hγ.lipschitz fun K hK => firstOrder_boundary_coefficient_memLp hγ hφ (deriv γ) (Measurable.aestronglyMeasurable (measurable_deriv γ)) fun x => norm_deriv_le_of_lipschitz hK)

theorem firstOrder_conjugate_velocity_coefficient_memLp :
    MemLp (fun θ => φ (γ θ) * conj (deriv γ θ)) 2
      (volume.restrict boundaryHalfOpenInterval) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  apply firstOrder_boundary_coefficient_memLp hγ hφ (fun θ => conj (deriv γ θ))
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (measurable_deriv γ).aestronglyMeasurable)
  intro θ
  simpa   using norm_deriv_le_of_lipschitz (x₀ := θ) hK

end


theorem smooth_firstOrder_green  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : IsBoundaryParam Ω γ)
     (hp : TestFunction univ p) :
    (∫ θ in boundaryHalfOpenInterval, p (γ θ) * deriv γ θ) =
      Complex.I * (∫ z in Ω, dirD p 1 z) - ∫ z in Ω, dirD p Complex.I z := by
  obtain ⟨Kp, hKp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hp.2.1 hp.1 (by simp)
  have hg : (∫ θ in boundaryHalfOpenInterval, p (γ θ) * deriv γ θ) =
      2 * Complex.I * ∫ z in Ω, dbar p z := by
    simpa  [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
      using integral_boundary_eq_dbar hb hL hγ hKp hp.2.1
  have hdx : IntegrableOn (dirD p 1) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD 1).memLp' 1)
  have hdy : IntegrableOn (dirD p Complex.I) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD Complex.I).memLp' 1)
  calc
    _ = 2 * Complex.I * ∫ z in Ω, dbar p z := hg
    _ = ∫ z in Ω, (Complex.I * dirD p 1 z - dirD p Complex.I z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only [dbar, dirD]
      ring_nf; simp  ; ring
    _ = _ := by rw [integral_sub (hdx.const_mul _) hdy, integral_const_mul]


theorem integral_dirD_smooth_mul Ω (f : smoothTraceTests)
     (hφ : TestFunction univ φ) v :
    (∫ z in Ω, dirD (fun z => f z * φ z) v z) =
      (∫ z in Ω, dirD (f : PlaneMap) v z * φ z) +
        ∫ z in Ω, f z * dirD φ v z := by
  have hproduct (z : ℂ) :
      dirD (fun z => f z * φ z) v z = dirD (f : PlaneMap) v z * φ z + f z * dirD φ v z := by
    rw [dirD, fderiv_fun_mul (f.property.1.differentiable (by simp) z)
      (hφ.1.differentiable (by simp) z)]
    simp [dirD]
    ring
  simp_rw [hproduct]
  exact integral_add (integrable_mul_test ((f.property.dirD v).memLp' 2) hφ)
    (integrable_mul_test (f.property.memLp' 2) (hφ.dirD v))

end PolyaNeumann

end
