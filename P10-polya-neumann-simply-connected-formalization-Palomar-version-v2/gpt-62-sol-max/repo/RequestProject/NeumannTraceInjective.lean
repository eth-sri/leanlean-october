module

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

section

variable {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
include Ω γ hγ φ hφ

lemma smoothConormalTest_memLp  :
    MemLp (fun θ => conj (fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)))) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kφ, hKφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  have hc :=
    (hφ.1.continuous_fderiv (by simp)).comp hKγ.continuous
  have hm : AEStronglyMeasurable
      (fun θ => fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hc.aestronglyMeasurable.prodMk
        ((measurable_deriv γ).const_mul _).neg.aestronglyMeasurable)
  apply MemLp.of_bound
    (Complex.continuous_conj.comp_aestronglyMeasurable hm).restrict
    ((Kφ : ℝ) * Kγ)
  apply Eventually.of_forall
  intro θ
  rw [Complex.norm_conj]
  calc
    _ ≤ ‖fderiv ℝ φ (γ θ)‖ * ‖-(Complex.I * deriv γ θ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (Kφ : ℝ) * Kγ := by simpa using mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hKφ) (norm_deriv_le_of_lipschitz hKγ) (norm_nonneg (deriv γ θ)) (NNReal.coe_nonneg Kφ)

/-- The actual conormal test, conjugated so that its pairing is linear in
the trace. It is constructed in L² rather than assumed bounded. -/
def smoothConormalTestL2  : BoundaryL2 :=
  (smoothConormalTest_memLp hγ hφ).toLp
    (fun θ => conj (fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))))

end

/-- The actual double-layer boundary functional on H¹. -/
def h1DoubleLayerBoundaryTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (smoothConormalTestL2 hγ hφ)).comp (h1BoundaryTrace hb hL hγ)

/-- The interior Green expression is a continuous functional on the
genuine H¹ space. Its coefficients are actual smooth Laplacian/derivative
L² classes, not unspecified boundary regularity data. -/
def h1DoubleLayerInteriorTest (Ω : Set ℂ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    NeumannH1 Ω →L[ℂ] ℂ :=
  (lpIntegralPair (hφ.lap.memLp' 2)).comp (h1Value Ω) +
    ∑ i : Fin 2, (lpIntegralPair ((hφ.dirD (coordDir i)).memLp' 2)).comp (h1Gradient Ω i)

theorem h1DoubleLayerInteriorTest_apply (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (u : NeumannH1 Ω) :
    h1DoubleLayerInteriorTest Ω hφ u =
      (∫ z in Ω, h1Value Ω u z * lap φ z) +
        ∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z := by
  simp  [h1DoubleLayerInteriorTest, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, lpIntegralPair_apply]


section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
include Ω hb hL γ hγ φ hφ

theorem h1DoubleLayerBoundaryTest_apply  (u : NeumannH1 Ω) :
    h1DoubleLayerBoundaryTest hb hL hγ hφ u =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)) := by
  change ⟪smoothConormalTestL2 hγ hφ, h1BoundaryTrace hb hL hγ u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(smoothConormalTest_memLp hγ hφ).coeFn_toLp] with θ hθ
  simp only [smoothConormalTestL2, RCLike.inner_apply, hθ, Complex.conj_conj]

private lemma h1DoubleLayerBoundaryTest_smooth  (f : smoothTraceTests) :
    h1DoubleLayerBoundaryTest hb hL hγ hφ (smoothTraceH1 Ω f) =
      doubleLayer γ (fun θ => f (γ θ)) φ := by
  rw [h1DoubleLayerBoundaryTest_apply, doubleLayer,
    intervalIntegral.integral_of_le (by positivity)]
  apply integral_congr_ae
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
  tauto

end

private lemma h1DoubleLayerInteriorTest_smooth (Ω : Set ℂ)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (f : smoothTraceTests) :
    h1DoubleLayerInteriorTest Ω hφ (smoothTraceH1 Ω f) =
      ∫ z in Ω, (f z * lap φ z +
        ∑ i : Fin 2, dirD (f : ℂ → ℂ) (coordDir i) z * dirD φ (coordDir i) z) := by
  rw [h1DoubleLayerInteriorTest_apply]
  have h0 : (∫ z in Ω, h1Value Ω (smoothTraceH1 Ω f) z * lap φ z) =
      ∫ z in Ω, f z * lap φ z := by
    apply integral_congr_ae
    filter_upwards [(f.property.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
    tauto
  have hi : ∀ i : Fin 2,
      (∫ z in Ω, h1Gradient Ω i (smoothTraceH1 Ω f) z * dirD φ (coordDir i) z) =
        ∫ z in Ω, dirD (f : ℂ → ℂ) (coordDir i) z * dirD φ (coordDir i) z := by
    intro i
    apply integral_congr_ae
    filter_upwards [((f.property.dirD (coordDir i)).memLp' 2
      (μ := volume.restrict Ω)).coeFn_toLp] with z hz
    tauto
  rw [h0]
  simp_rw [hi]
  have hmass := integrable_mul_test (f.property.memLp' 2 (μ := volume.restrict Ω)) hφ.lap
  have hgrad : ∀ i : Fin 2, IntegrableOn
      (fun z => dirD (f : ℂ → ℂ) (coordDir i) z * dirD φ (coordDir i) z) Ω :=
    fun i => integrable_mul_test ((f.property.dirD (coordDir i)).memLp' 2) (hφ.dirD _)
  simp  
  exact ((integral_add hmass ((hgrad 0).add (hgrad 1))).trans
    (congrArg (fun x : ℂ => (∫ z in Ω, f z * lap φ z) + x)
      (integral_add (hgrad 0) (hgrad 1)))).symm

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
include Ω hb hL γ hγ φ hφ

/-- Green's double-layer identity for every actual weak-gradient H¹ vector.
It follows by equality of continuous functionals on the dense smooth
restrictions, so no extra regularity of the H¹ vector is imposed. -/
theorem h1DoubleLayerBoundaryTest_eq_interior  :
    h1DoubleLayerBoundaryTest hb hL hγ hφ = h1DoubleLayerInteriorTest Ω hφ := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1DoubleLayerBoundaryTest hb hL hγ hφ).continuous
    (h1DoubleLayerInteriorTest Ω hφ).continuous
  funext f
  rw [Function.comp_apply, Function.comp_apply, smoothTraceH1Lin_apply,
    h1DoubleLayerBoundaryTest_smooth, h1DoubleLayerInteriorTest_smooth Ω]
  obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    f.property.2.1 f.property.1 (by simp)
  exact doubleLayer_eq_integral hb hL hγ hKf f.property.2.1 (fun θ _ => rfl) hφ.1

/-- The raw integral version of the generalized Green identity uses the
actual L² representatives of the value, weak gradients, and boundary trace. -/
theorem h1_doubleLayer_green  (u : NeumannH1 Ω) :
    (∫ z in Ω, h1Value Ω u z * lap φ z) +
      (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) =
        ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
          fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ)) := by
  rw [← h1DoubleLayerInteriorTest_apply Ω hφ u,
    ← h1DoubleLayerBoundaryTest_eq_interior hb hL hγ hφ,
    h1DoubleLayerBoundaryTest_apply hb hL hγ hφ u]

end

end PolyaNeumann

end
