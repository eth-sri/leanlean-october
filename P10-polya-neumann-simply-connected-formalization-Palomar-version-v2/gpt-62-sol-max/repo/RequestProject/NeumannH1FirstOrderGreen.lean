module

public import RequestProject.NeumannHardyTraceInjective
public import RequestProject.LpBoundedMultiplier

/-!
# First-order and conormal Green identities on the actual H¹ space

The nonconjugate velocity identity is proved first on compact smooth
restrictions by the genuine winding-number Green formula, then extended
by H¹ density through bounded functionals. Combining it with the conjugate
identity gives the two real coordinate divergence formulas. When the weak
gradient components themselves have actual H¹ representatives, these give
the genuine second-order conormal Green formula with their actual traces.

Boundary measure is ordinary dθ. Its normal density is `-i γ′`, so its
real coordinate components are `Im γ′` and `-Re γ′`.
This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

/-- Coordinate components of the outward normal density `-i γ′`. -/
def boundaryNormalCoord (γ : ℝ → ℂ) (i : Fin 2) (θ : ℝ) : ℂ :=
  if i = 0 then (deriv γ θ).im else -(deriv γ θ).re

private def velocityFactor (i : Fin 2) (c : Bool) : ℂ :=
  if i = 0 then (if c then Complex.I else -Complex.I) / 2 else -1 / 2

private theorem boundaryNormalCoord_eq (γ : ℝ → ℂ) (i : Fin 2) (θ : ℝ) :
    boundaryNormalCoord γ i θ = velocityFactor i false * boundaryVelocity γ false θ +
      velocityFactor i true * boundaryVelocity γ true θ := by
  let z := deriv γ θ
  fin_cases i <;> simp [boundaryNormalCoord, velocityFactor, boundaryVelocity, ← show z = deriv γ θ from rfl]
  · rw [show -Complex.I / 2 * z + Complex.I / 2 * conj z =
        (-Complex.I / 2) * (z - conj z) by ring, Complex.sub_conj]
    push_cast
    ring_nf
    simp
  · rw [show (-1 / 2) * z + (-1 / 2) * conj z = (-1 / 2) * (z + conj z) by ring,
      Complex.add_conj]
    push_cast
    ring

theorem boundaryNormalCoord_measurable (γ : ℝ → ℂ) (i : Fin 2) :
    AEStronglyMeasurable (boundaryNormalCoord γ i) volume := by
  change AEStronglyMeasurable
    (fun θ => if i = 0 then ((deriv γ θ).im : ℂ) else -((deriv γ θ).re : ℂ)) volume
  by_cases h : i = 0 <;> simp only [h, if_true, if_false]
  · exact Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      (Complex.imCLM.continuous.comp_aestronglyMeasurable (measurable_deriv γ).aestronglyMeasurable)
  · fun_prop

theorem boundaryNormalCoord_bound {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (i : Fin 2) (θ : ℝ) : ‖boundaryNormalCoord γ i θ‖ ≤ K := by
  unfold boundaryNormalCoord
  split_ifs
  · simpa using (Complex.abs_im_le_norm _).trans (norm_deriv_le_of_lipschitz (x₀ := θ) hK)
  · simpa using (Complex.abs_re_le_norm _).trans (norm_deriv_le_of_lipschitz (x₀ := θ) hK)

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
  {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {φ : ℂ → ℂ} (hφ : TestFunction univ φ)
include hb hL hγ hφ

/-- Coordinate divergence as a linear combination of the two complex Green identities. -/
theorem h1_coordinate_divergence (u : NeumannH1 Ω) (i : Fin 2) :
    (∫ z in Ω, h1Gradient Ω i u z * φ z) +
        (∫ z in Ω, h1Value Ω u z * dirD φ (coordDir i) z) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), h1BoundaryTrace hb hL hγ u θ *
        (φ (γ θ) * boundaryNormalCoord γ i θ) := by
  let p (c : Bool) (θ : ℝ) := h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * boundaryVelocity γ c θ)
  have hp (c : Bool) : IntegrableOn (p c) (Ioc 0 (2 * π)) :=
    (Lp.memLp (h1BoundaryTrace hb hL hγ u)).integrable_mul
      (firstOrder_signed_velocity_coefficient_memLp hγ hφ c)
  have hg (c : Bool) := h1_firstOrder_green hγ hφ hb hL c u
  have he (θ : ℝ) : h1BoundaryTrace hb hL hγ u θ * (φ (γ θ) * boundaryNormalCoord γ i θ) =
      velocityFactor i false * p false θ + velocityFactor i true * p true θ := by
    rw [boundaryNormalCoord_eq]; simp only [p]; ring
  simp_rw [he]
  rw [integral_add ((hp false).const_mul _) ((hp true).const_mul _),
    integral_const_mul, integral_const_mul]
  unfold p
  rw [← hg false, ← hg true]
  fin_cases i <;> simp [velocityFactor, boundaryVelocitySign, coordDir_zero, coordDir_one] <;>
    ring_nf <;> simp

end

section

variable {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
include hγ

def firstOrderBoundarySpeedBound : NNReal := Classical.choose hγ.lipschitz

theorem firstOrderBoundarySpeedBound_spec : LipschitzWith (firstOrderBoundarySpeedBound hγ) γ :=
  Classical.choose_spec hγ.lipschitz

/-- Multiplication by one coordinate of the outward normal density. -/
def h1BoundaryNormalMultiplier (i : Fin 2) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (boundaryNormalCoord γ i) (boundaryNormalCoord_measurable γ i).restrict
    (Eventually.of_forall (boundaryNormalCoord_bound (firstOrderBoundarySpeedBound_spec hγ) i))

theorem h1BoundaryNormalMultiplier_ae (i : Fin 2) (g : BoundaryL2) :
    (h1BoundaryNormalMultiplier hγ i g : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))]
      fun θ => boundaryNormalCoord γ i θ * g θ :=
  lpBoundedMultiplier_ae _ _ _ g

end

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (g0 g1 : NeumannH1 Ω)
include Ω hb hL γ hγ g0 g1

/-- The actual L² conormal density for two H¹ gradient representatives. -/
def h1GradientConormalDensity  : BoundaryL2 :=
  h1BoundaryNormalMultiplier hγ 0 (h1BoundaryTrace hb hL hγ g0) +
    h1BoundaryNormalMultiplier hγ 1 (h1BoundaryTrace hb hL hγ g1)

theorem h1GradientConormalDensity_ae  :
    (h1GradientConormalDensity hb hL hγ g0 g1 : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * π))]
      fun θ => ((deriv γ θ).im : ℂ) * h1BoundaryTrace hb hL hγ g0 θ +
        (-(deriv γ θ).re : ℂ) * h1BoundaryTrace hb hL hγ g1 θ := by
  filter_upwards [Lp.coeFn_add
      (h1BoundaryNormalMultiplier hγ 0 (h1BoundaryTrace hb hL hγ g0))
      (h1BoundaryNormalMultiplier hγ 1 (h1BoundaryTrace hb hL hγ g1)),
    h1BoundaryNormalMultiplier_ae hγ 0 (h1BoundaryTrace hb hL hγ g0),
    h1BoundaryNormalMultiplier_ae hγ 1 (h1BoundaryTrace hb hL hγ g1)] with θ ha hx hy
  change (_ + _ : BoundaryL2) θ = _
  simp_all [boundaryNormalCoord]

end

/-- The divergence is the sum of actual weak derivative components. -/
def h1GradientDivergence (Ω : Set ℂ) (g0 g1 : NeumannH1 Ω) : L2 Ω :=
  h1Gradient Ω 0 g0 + h1Gradient Ω 1 g1

/-- The genuine conormal Green identity for a vector with H¹ weak gradients.
The actual gradient traces form an L² boundary density, rather than an
unspecified conormal regularity premise. -/
theorem h1_conormal_green_compact_test {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (u g0 g1 : NeumannH1 Ω)
    (hg0 : h1Gradient Ω 0 u = h1Value Ω g0)
    (hg1 : h1Gradient Ω 1 u = h1Value Ω g1)
    {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) +
        (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * φ z) =
      ∫ θ in Ioc (0 : ℝ) (2 * π),
        h1GradientConormalDensity hb hL hγ g0 g1 θ * φ (γ θ) := by
  have hdiv : (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * φ z) =
      (∫ z in Ω, h1Gradient Ω 0 g0 z * φ z) +
        ∫ z in Ω, h1Gradient Ω 1 g1 z * φ z := by
    rw [← lpIntegralPair_apply (hφ.memLp' 2)]
    change lpIntegralPair (hφ.memLp' 2) (_ + _) = _
    rw [map_add, lpIntegralPair_apply, lpIntegralPair_apply]
  let p (i : Fin 2) (w : NeumannH1 Ω) (θ : ℝ) := h1BoundaryTrace hb hL hγ w θ *
    (φ (γ θ) * boundaryNormalCoord γ i θ)
  have hp (i : Fin 2) (w : NeumannH1 Ω) : IntegrableOn (p i w) (Ioc 0 (2 * π)) :=
    (Lp.memLp (h1BoundaryTrace hb hL hγ w)).integrable_mul
      (firstOrder_boundary_coefficient_memLp hγ hφ _ (boundaryNormalCoord_measurable γ i)
        (boundaryNormalCoord_bound (firstOrderBoundarySpeedBound_spec hγ) i))
  rw [show (∫ θ in Ioc (0 : ℝ) (2 * π), h1GradientConormalDensity hb hL hγ g0 g1 θ * φ (γ θ)) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), p 0 g0 θ + p 1 g1 θ from by
    apply integral_congr_ae
    filter_upwards [h1GradientConormalDensity_ae hb hL hγ g0 g1] with θ hθ
    rw [hθ]
    simp [p, boundaryNormalCoord]; ring]
  rw [integral_add (hp 0 g0) (hp 1 g1)]
  unfold p
  rw [← h1_coordinate_divergence hb hL hγ hφ g0 0, ← h1_coordinate_divergence hb hL hγ hφ g1 1,
    Fin.sum_univ_two, hg0, hg1, hdiv]
  ring

private theorem firstOrder_inner_toLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℂ 2 μ) {φ : α → ℂ} (hφ : MemLp φ 2 μ) :
    ⟪u, hφ.toLp φ⟫_ℂ = conj (∫ z, u z * conj (φ z) ∂μ) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with z hz
  simp  [hz, map_mul]
  ring

private theorem firstOrder_inner_conjugate_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u v : Lp ℂ 2 μ) :
    ⟪u, v⟫_ℂ = conj (∫ z, u z * conj (v z) ∂μ) := by grind [L2.inner_def, integral_conj, RCLike.inner_apply, map_mul, Complex.conj_conj, mul_comm]

/-- A bounded functional in the H¹ test input; its first argument is fixed. -/
def h1ConormalGreenInteriorFunctional (Ω : Set ℂ) (u g0 g1 : NeumannH1 Ω) :
    NeumannH1 Ω →L[ℂ] ℂ :=
  (∑ i : Fin 2, (innerSL ℂ (h1Gradient Ω i u)).comp (h1Gradient Ω i)) +
    (innerSL ℂ (h1GradientDivergence Ω g0 g1)).comp (h1Value Ω)

def h1ConormalGreenBoundaryFunctional {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (g0 g1 : NeumannH1 Ω) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (h1GradientConormalDensity hb hL hγ g0 g1)).comp (h1BoundaryTrace hb hL hγ)

theorem h1ConormalGreenInteriorFunctional_apply (Ω : Set ℂ)
    (u g0 g1 w : NeumannH1 Ω) :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 w =
      (∑ i : Fin 2, ⟪h1Gradient Ω i u, h1Gradient Ω i w⟫_ℂ) +
        ⟪h1GradientDivergence Ω g0 g1, h1Value Ω w⟫_ℂ := by rfl

theorem h1ConormalGreenBoundaryFunctional_apply {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (g0 g1 w : NeumannH1 Ω) :
    h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 w =
      ⟪h1GradientConormalDensity hb hL hγ g0 g1, h1BoundaryTrace hb hL hγ w⟫_ℂ := rfl

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (u g0 g1 : NeumannH1 Ω) (hg0 : h1Gradient Ω 0 u = h1Value Ω g0) (hg1 : h1Gradient Ω 1 u = h1Value Ω g1)
include Ω hb hL γ hγ u g0 g1 hg0 hg1

private theorem h1ConormalGreen_smooth  (f : smoothTraceTests) :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 (smoothTraceH1 Ω f) =
      h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 (smoothTraceH1 Ω f) := by
  have hi (i : Fin 2) :
      ⟪h1Gradient Ω i u, h1Gradient Ω i (smoothTraceH1 Ω f)⟫_ℂ =
        conj (∫ z in Ω, h1Gradient Ω i u z *
          dirD (fun w => conj (f w)) (coordDir i) z) := by
    rw [h1Gradient_smoothTraceH1, firstOrder_inner_toLp]
    apply congrArg conj
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    change h1Gradient Ω i u z * conj (dirD (f : ℂ → ℂ) (coordDir i) z) =
      h1Gradient Ω i u z * dirD (fun w => conj (f w)) (coordDir i) z
    rw [dirD_conj (f.property.1.of_le (by simp))]
  have hv : ⟪h1GradientDivergence Ω g0 g1, h1Value Ω (smoothTraceH1 Ω f)⟫_ℂ =
      conj (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * conj (f z)) := by
    rw [h1Value_smoothTraceH1, firstOrder_inner_toLp]
  have hbnd : ⟪h1GradientConormalDensity hb hL hγ g0 g1,
      h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f)⟫_ℂ =
      conj (∫ θ in Ioc (0 : ℝ) (2 * π),
        h1GradientConormalDensity hb hL hγ g0 g1 θ * conj (f (γ θ))) := by
    rw [firstOrder_inner_conjugate_integral]
    apply congrArg conj
    apply integral_congr_ae
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
    tauto
  have h := congrArg conj
    (h1_conormal_green_compact_test hb hL hγ u g0 g1 hg0 hg1 f.property.conj)
  simp only [map_add, map_sum] at h
  simpa only [h1ConormalGreenInteriorFunctional_apply,
    h1ConormalGreenBoundaryFunctional_apply, hi, hv, hbnd] using h

/-- Both sides are genuinely bounded functionals in the test input, so
the compact-smooth identity extends to every actual H¹ test vector. -/
theorem h1ConormalGreenInteriorFunctional_eq_boundary  :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 =
      h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1ConormalGreenInteriorFunctional Ω u g0 g1).continuous
    (h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1).continuous
  funext f
  rw [Function.comp_apply, smoothTraceH1Lin_apply]
  exact h1ConormalGreen_smooth hb hL hγ u g0 g1 hg0 hg1 f

/-- The true conormal Green formula against arbitrary H¹ tests, with the
same first-slot test convention as the physical Neumann form. -/
theorem h1_conormal_green  (w : NeumannH1 Ω) :
    (∑ i : Fin 2, ⟪h1Gradient Ω i w, h1Gradient Ω i u⟫_ℂ) +
        ⟪h1Value Ω w, h1GradientDivergence Ω g0 g1⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ w, h1GradientConormalDensity hb hL hγ g0 g1⟫_ℂ := by
  have h := congrArg (fun T : NeumannH1 Ω →L[ℂ] ℂ => T w)
    (h1ConormalGreenInteriorFunctional_eq_boundary hb hL hγ u g0 g1 hg0 hg1)
  change h1ConormalGreenInteriorFunctional Ω u g0 g1 w =
    h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 w at h
  rw [h1ConormalGreenInteriorFunctional_apply,
    h1ConormalGreenBoundaryFunctional_apply] at h
  simpa only [map_add, map_sum, inner_conj_symm] using congrArg conj h

end

end PolyaNeumann

end
