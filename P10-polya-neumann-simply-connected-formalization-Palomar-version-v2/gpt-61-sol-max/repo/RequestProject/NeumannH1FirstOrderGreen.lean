module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate



/-- Conjugation converts the bilinear boundary test into an inner-product
functional linear in the actual trace. -/
def firstOrderVelocityTestL2 {Ω } {γ }
    (hγ : IsBoundaryParam Ω γ) {φ } (hφ : TestFunction univ φ)  :=
  ((firstOrder_velocity_coefficient_memLp hγ hφ).star).toLp
    (fun θ => conj (φ (γ θ) * deriv γ θ))

def h1FirstOrderBoundaryTest {Ω : PlanarSet} (hL : IsLipschitzDomain Ω) {γ : ComplexCurve} (hγ : IsBoundaryParam Ω γ)
    {φ : PlaneMap} (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (firstOrderVelocityTestL2 hγ hφ)).comp (h1BoundaryTrace hL hγ)

def h1FirstOrderInteriorTest (Ω : PlanarSet) {φ : PlaneMap}
    (hφ : TestFunction univ φ) : NeumannH1 Ω →L[ℂ] ℂ :=
  Complex.I • ((smoothL2Pair Ω hφ).comp (h1Gradient Ω 0) +
      (smoothL2Pair Ω (hφ.dirD 1)).comp (h1Value Ω)) -
    ((smoothL2Pair Ω hφ).comp (h1Gradient Ω 1) +
      (smoothL2Pair Ω (hφ.dirD Complex.I)).comp (h1Value Ω))

theorem h1FirstOrderInteriorTest_apply Ω 
    (hφ : TestFunction univ φ) u :
    h1FirstOrderInteriorTest Ω hφ u =
      Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) := by
  simp only [h1FirstOrderInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, smoothL2Pair_apply]

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ)
include Ω hb hL γ hγ

theorem h1FirstOrderBoundaryTest_apply  (hφ : TestFunction univ φ)
    u :
    h1FirstOrderBoundaryTest hL hγ hφ u =
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ u θ *
        (φ (γ θ) * deriv γ θ) := by
  apply integral_congr_ae
  filter_upwards [((firstOrder_velocity_coefficient_memLp hγ hφ).star).coeFn_toLp]
    with θ hθ
  change firstOrderVelocityTestL2 hγ hφ θ = conj (φ (γ θ) * deriv γ θ) at hθ
  simp_all


end




section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ) {φ } (hφ : TestFunction univ φ)
local notation "h1BoundaryTraceFixed" => h1BoundaryTrace hL hγ


section
include Ω hb hL γ hγ φ hφ

private theorem h1FirstOrder_green_smooth
    f :
    h1FirstOrderBoundaryTest hL hγ hφ (smoothTraceH1 Ω f) =
      h1FirstOrderInteriorTest Ω hφ (smoothTraceH1 Ω f) := by
  let p  := fun z => f z * φ z
  have hp : TestFunction univ p :=
    ⟨f.property.1.mul hφ.1, f.property.2.1.mul_right, subset_univ _⟩
  have hleft : h1FirstOrderBoundaryTest hL hγ hφ (smoothTraceH1 Ω f) =
      ∫ θ in boundaryHalfOpenInterval, p (γ θ) * deriv γ θ := by
    rw [h1FirstOrderBoundaryTest_apply hb]
    apply integral_congr_ae
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
    rw [hθ]
    ring
  have hproduct_integral := integral_dirD_smooth_mul Ω f hφ
  rw [hleft, smooth_firstOrder_green hb hL hγ hp,
    hproduct_integral, hproduct_integral]
  have hdir0 : coordDir (0 : Coord) = (1 : ℂ) := rfl
  have hdir1 : coordDir (1 : Coord) = Complex.I := rfl
  simp only [h1FirstOrderInteriorTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, smoothL2Pair_smooth_gradient,
    smoothL2Pair_smooth_value, hdir0, hdir1]

theorem h1FirstOrderBoundaryTest_eq_interior :
    h1FirstOrderBoundaryTest hL hγ hφ = h1FirstOrderInteriorTest Ω hφ := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1FirstOrderBoundaryTest hL hγ hφ).continuous
    (h1FirstOrderInteriorTest Ω hφ).continuous
  ext <;> simp_all [h1FirstOrder_green_smooth]

/-- The genuine nonconjugate first-order Green identity on every H¹ input. -/
theorem h1_firstOrder_green
    u :
    Complex.I * ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
      ∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
      ((∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        ∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTraceFixed u θ *
        (φ (γ θ) * deriv γ θ) := by
  rw [← h1FirstOrderInteriorTest_apply Ω hφ u,
    ← h1FirstOrderBoundaryTest_eq_interior hb hL hγ hφ,
    h1FirstOrderBoundaryTest_apply hb]

end


private theorem firstOrder_normal_x z :
    (z.im : ℂ) = (-Complex.I / 2) * (z - conj z) := by
  rw [Complex.sub_conj]
  push_cast
  ring_nf; simp only [Complex.I_sq]; ring

private theorem firstOrder_normal_y z :
    -(z.re : ℂ) = (-1 / 2 : ℂ) * (z + conj z) := by
  rw [Complex.add_conj]
  push_cast
  ring

section
include Ω hb hL γ hγ φ hφ

/-- Divergence in the real x direction, with the actual outward normal density. -/
theorem h1_coordinate_divergence_x
    u :
    (∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
        (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) =
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTraceFixed u θ *
        (φ (γ θ) * ((deriv γ θ).im : ℂ)) := by
  have hp := h1_firstOrder_green hb hL hγ hφ u
  have hm := h1_firstOrder_conjugate_green hb hL hγ hφ u
  have hip := (Lp.memLp (h1BoundaryTraceFixed u)).integrable_mul
    (firstOrder_velocity_coefficient_memLp hγ hφ)
  have him := (Lp.memLp (h1BoundaryTraceFixed u)).integrable_mul
    (firstOrder_conjugate_velocity_coefficient_memLp hγ hφ)
  symm
  calc
    _ = ∫ θ in Ioc 0 circlePeriod, (-Complex.I / 2) *
        (h1BoundaryTraceFixed u θ * (φ (γ θ) * deriv γ θ) -
          h1BoundaryTraceFixed u θ * (φ (γ θ) * conj (deriv γ θ))) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro θ
      change h1BoundaryTraceFixed u θ * (φ (γ θ) * ((deriv γ θ).im)) =
        (-Complex.I / 2) *
          (h1BoundaryTraceFixed u θ * (φ (γ θ) * deriv γ θ) -
            h1BoundaryTraceFixed u θ * (φ (γ θ) * conj (deriv γ θ)))
      rw [firstOrder_normal_x]
      ring
    _ = (-Complex.I / 2) *
        ((∫ θ in Ioc 0 circlePeriod, h1BoundaryTraceFixed u θ *
          (φ (γ θ) * deriv γ θ)) -
        ∫ θ in Ioc 0 circlePeriod, h1BoundaryTraceFixed u θ *
          (φ (γ θ) * conj (deriv γ θ))) := by
      rw [integral_const_mul]
      exact congrArg (fun z : ℂ => (-Complex.I / 2) * z) (integral_sub hip him)
    _ = _ := by
      rw [← hp, ← hm]
      ring_nf; simp only [Complex.I_sq]; ring

/-- Divergence in the real y direction, with density `-Re γ′`. -/
theorem h1_coordinate_divergence_y
    u :
    (∫ z in Ω, h1Gradient Ω 1 u z * φ z) +
        (∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTraceFixed u θ *
        (φ (γ θ) * (-(deriv γ θ).re : ℂ)) := by
  have hp := h1_firstOrder_green hb hL hγ hφ u
  have hm := h1_firstOrder_conjugate_green hb hL hγ hφ u
  have hip := (Lp.memLp (h1BoundaryTraceFixed u)).integrable_mul
    (firstOrder_velocity_coefficient_memLp hγ hφ)
  have him := (Lp.memLp (h1BoundaryTraceFixed u)).integrable_mul
    (firstOrder_conjugate_velocity_coefficient_memLp hγ hφ)
  symm
  calc
    _ = ∫ θ in Ioc 0 circlePeriod, (-1 / 2) *
        (h1BoundaryTraceFixed u θ * (φ (γ θ) * deriv γ θ) +
          h1BoundaryTraceFixed u θ * (φ (γ θ) * conj (deriv γ θ))) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro θ
      change h1BoundaryTraceFixed u θ * (φ (γ θ) * (-(deriv γ θ).re)) =
        (-1 / 2) *
          (h1BoundaryTraceFixed u θ * (φ (γ θ) * deriv γ θ) +
            h1BoundaryTraceFixed u θ * (φ (γ θ) * conj (deriv γ θ)))
      rw [show (-(deriv γ θ).re : ℂ) = -((deriv γ θ).re : ℂ) from by simp,
        firstOrder_normal_y]
      ring
    _ = (-1 / 2) *
        ((∫ θ in Ioc 0 circlePeriod, h1BoundaryTraceFixed u θ *
          (φ (γ θ) * deriv γ θ)) +
        ∫ θ in Ioc 0 circlePeriod, h1BoundaryTraceFixed u θ *
          (φ (γ θ) * conj (deriv γ θ))) := by
      rw [integral_const_mul]
      exact congrArg (fun z : ℂ => (-1 / 2) * z) (integral_add hip him)
    _ = _ := by rw [← hp, ← hm]; ring

end


end


def firstOrderBoundarySpeedBound {Ω } {γ }
    (hγ : IsBoundaryParam Ω γ)  := Classical.choose hγ.lipschitz

section
variable {Ω } {γ } (hγ : IsBoundaryParam Ω γ)

include Ω γ hγ in
private theorem firstOrderBoundarySpeedBound_spec : LipschitzWith (firstOrderBoundarySpeedBound hγ) γ :=
  Classical.choose_spec hγ.lipschitz

theorem firstOrder_normalX_measurable (γ : ComplexCurve) :
    AEStronglyMeasurable (fun θ => ((deriv γ θ).im : ℂ)) volume :=
  Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
    (Complex.imCLM.continuous.comp_aestronglyMeasurable (measurable_deriv γ).aestronglyMeasurable)

theorem firstOrder_normalY_measurable (γ : ComplexCurve) :
    AEStronglyMeasurable (fun θ => (-(deriv γ θ).re : ℂ)) volume := (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Complex.continuous_re.comp_aestronglyMeasurable
        (measurable_deriv γ).aestronglyMeasurable)).neg

section
include Ω γ hγ

theorem firstOrder_normalX_bound θ :
    ‖((deriv γ θ).im : ℂ)‖ ≤ firstOrderBoundarySpeedBound hγ := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans
    (norm_deriv_le_of_lipschitz (firstOrderBoundarySpeedBound_spec hγ))

theorem firstOrder_normalY_bound θ :
    ‖(-(deriv γ θ).re : ℂ)‖ ≤ firstOrderBoundarySpeedBound hγ := by
  simp  
  exact (Complex.abs_re_le_norm _).trans
    (norm_deriv_le_of_lipschitz (firstOrderBoundarySpeedBound_spec hγ))

end


/-- Multiplication by the genuine x component of the outward normal density. -/
def h1BoundaryNormalXMultiplier {Ω } {γ }
    (hγ : IsBoundaryParam Ω γ) : ComplexEnd BoundaryL2 :=
  lpBoundedMultiplier (fun θ => ((deriv γ θ).im : ℂ))
    (firstOrder_normalX_measurable γ).restrict
    (Eventually.of_forall (firstOrder_normalX_bound hγ))

/-- Multiplication by the genuine y component of the outward normal density. -/
def h1BoundaryNormalYMultiplier {Ω } {γ }
    (hγ : IsBoundaryParam Ω γ) : ComplexEnd BoundaryL2 :=
  lpBoundedMultiplier (fun θ => (-(deriv γ θ).re : ℂ))
    (firstOrder_normalY_measurable γ).restrict
    (Eventually.of_forall (firstOrder_normalY_bound hγ))

section
include Ω γ hγ

theorem h1BoundaryNormalXMultiplier_ae g :
    (h1BoundaryNormalXMultiplier hγ g : ComplexCurve) =ᵐ[
      volume.restrict boundaryHalfOpenInterval]
      fun θ => ((deriv γ θ).im : ℂ) * g θ :=
  lpBoundedMultiplier_ae _ _ _ g

theorem h1BoundaryNormalYMultiplier_ae g :
    (h1BoundaryNormalYMultiplier hγ g : ComplexCurve) =ᵐ[
      volume.restrict boundaryHalfOpenInterval]
      fun θ => (-(deriv γ θ).re : ℂ) * g θ :=
  lpBoundedMultiplier_ae _ _ _ g

end


end


/-- The actual L² conormal density for two H¹ gradient representatives. -/
def h1GradientConormalDensity {Ω } hL {γ } (hγ : IsBoundaryParam Ω γ)
    g0 g1  :=
  h1BoundaryNormalXMultiplier hγ (h1BoundaryTrace hL hγ g0) +
    h1BoundaryNormalYMultiplier hγ (h1BoundaryTrace hL hγ g1)

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ)

include Ω hb hL γ hγ in
theorem h1GradientConormalDensity_ae
    g0 g1 :
    (h1GradientConormalDensity hL hγ g0 g1 : ComplexCurve) =ᵐ[
      volume.restrict boundaryHalfOpenInterval]
      fun θ => ((deriv γ θ).im : ℂ) * h1BoundaryTrace hL hγ g0 θ +
        (-(deriv γ θ).re : ℂ) * h1BoundaryTrace hL hγ g1 θ := by
  filter_upwards [Lp.coeFn_add
      (h1BoundaryNormalXMultiplier hγ (h1BoundaryTrace hL hγ g0))
      (h1BoundaryNormalYMultiplier hγ (h1BoundaryTrace hL hγ g1)),
    h1BoundaryNormalXMultiplier_ae hγ (h1BoundaryTrace hL hγ g0),
    h1BoundaryNormalYMultiplier_ae hγ (h1BoundaryTrace hL hγ g1)] with θ ha hx hy
  measurability

/-- The divergence is the sum of actual weak derivative components. -/
def h1GradientDivergence Ω g0 g1  :=
  h1Gradient Ω 0 g0 + h1Gradient Ω 1 g1

include Ω hb hL γ hγ in
/-- The genuine conormal Green identity for a vector with H¹ weak gradients.
The actual gradient traces form an L² boundary density, rather than an
unspecified conormal regularity premise. -/
theorem h1_conormal_green_compact_test u g0 g1
    (hg0 : h1Gradient Ω 0 u = h1Value Ω g0)
    (hg1 : h1Gradient Ω 1 u = h1Value Ω g1)
     (hφ : TestFunction univ φ) :
    (∑ i : Coord, ∫ z in Ω, h1Gradient Ω i u z * dirD φ (coordDir i) z) +
        (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * φ z) =
      ∫ θ in boundaryHalfOpenInterval,
        h1GradientConormalDensity hL hγ g0 g1 θ * φ (γ θ) := by
  have hx := h1_coordinate_divergence_x hb hL hγ hφ g0
  have hy := h1_coordinate_divergence_y hb hL hγ hφ g1
  have hdiv : (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * φ z) =
      (∫ z in Ω, h1Gradient Ω 0 g0 z * φ z) +
        ∫ z in Ω, h1Gradient Ω 1 g1 z * φ z := by
    rw [← smoothL2Pair_apply Ω hφ]
    change smoothL2Pair Ω hφ (_ + _) = _
    rw [map_add, smoothL2Pair_apply, smoothL2Pair_apply]
  have hix := (Lp.memLp (h1BoundaryTrace hL hγ g0)).integrable_mul
    (firstOrder_boundary_coefficient_memLp hγ hφ _ (firstOrder_normalX_measurable γ)
      (firstOrder_normalX_bound hγ))
  have hiy := (Lp.memLp (h1BoundaryTrace hL hγ g1)).integrable_mul
    (firstOrder_boundary_coefficient_memLp hγ hφ _ (firstOrder_normalY_measurable γ)
      (firstOrder_normalY_bound hγ))
  have hbd : (∫ θ in boundaryHalfOpenInterval,
      h1GradientConormalDensity hL hγ g0 g1 θ * φ (γ θ)) =
      (∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ g0 θ *
        (φ (γ θ) * ((deriv γ θ).im : ℂ))) +
      ∫ θ in boundaryHalfOpenInterval, h1BoundaryTrace hL hγ g1 θ *
        (φ (γ θ) * (-(deriv γ θ).re : ℂ)) := by
    calc
      _ = ∫ θ in Ioc 0 circlePeriod,
          h1BoundaryTrace hL hγ g0 θ * (φ (γ θ) * ((deriv γ θ).im)) +
          h1BoundaryTrace hL hγ g1 θ * (φ (γ θ) * (-(deriv γ θ).re)) := by
        apply integral_congr_ae
        filter_upwards [h1GradientConormalDensity_ae hb hL hγ g0 g1] with θ hθ
        rw [hθ]
        ring
      _ = _ := integral_add hix hiy
  rw [Fin.sum_univ_two]
  change (∫ z in Ω, h1Gradient Ω 0 u z * dirD φ 1 z) +
      (∫ z in Ω, h1Gradient Ω 1 u z * dirD φ Complex.I z) + _ = _
  rw [hg0, hg1, hdiv, hbd, ← hx, ← hy]
  ring

private theorem firstOrder_inner_toLp {α : Type*} [MeasurableSpace α]
    {μ } u {φ : α → ℂ} (hφ : MemLp φ 2 μ) :
    ⟪u, hφ.toLp φ⟫_ℂ = conj (∫ z, u z * conj (φ z) ∂μ) := by
  rw [L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with z hz
  simp  [hz]
  exact mul_comm _ _

private theorem firstOrder_inner_conjugate_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u v : Lp ℂ 2 μ) :
    ⟪u, v⟫_ℂ = conj (∫ z, u z * conj (v z) ∂μ) := by
  rw [L2.inner_def, ← integral_conj]
  simp  [mul_comm]

/-- A bounded functional in the H¹ test input; its first argument is fixed. -/
def h1ConormalGreenInteriorFunctional (Ω : PlanarSet) (u g0 g1 : NeumannH1 Ω) :
    NeumannH1 Ω →L[ℂ] ℂ :=
  (∑ i : Coord, (innerSL ℂ (h1Gradient Ω i u)).comp (h1Gradient Ω i)) +
    (innerSL ℂ (h1GradientDivergence Ω g0 g1)).comp (h1Value Ω)

def h1ConormalGreenBoundaryFunctional {Ω : PlanarSet} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ComplexCurve} (hγ : IsBoundaryParam Ω γ)
    (g0 g1 : NeumannH1 Ω) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (h1GradientConormalDensity hL hγ g0 g1)).comp (h1BoundaryTrace hL hγ)

theorem h1ConormalGreenInteriorFunctional_apply Ω
    u g0 g1 w :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 w =
      (∑ i : Coord, ⟪h1Gradient Ω i u, h1Gradient Ω i w⟫_ℂ) +
        ⟪h1GradientDivergence Ω g0 g1, h1Value Ω w⟫_ℂ := rfl

include Ω hb hL γ hγ in
theorem h1ConormalGreenBoundaryFunctional_apply g0 g1 w :
    h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 w =
      ⟪h1GradientConormalDensity hL hγ g0 g1, h1BoundaryTrace hL hγ w⟫_ℂ := rfl

end


section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ) (u g0 g1 ) (hg0 : h1Gradient Ω 0 u = h1Value Ω g0) (hg1 : h1Gradient Ω 1 u = h1Value Ω g1)
include Ω hb hL γ hγ u g0 g1 hg0 hg1

private theorem h1ConormalGreen_smooth f :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 (smoothTraceH1 Ω f) =
      h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 (smoothTraceH1 Ω f) := by
  have hi (i : Coord) :
      ⟪h1Gradient Ω i u, h1Gradient Ω i (smoothTraceH1 Ω f)⟫_ℂ =
        conj (∫ z in Ω, h1Gradient Ω i u z *
          dirD (fun w => conj (f w)) (coordDir i) z) := by
    rw [h1Gradient_smoothTraceH1, firstOrder_inner_toLp]
    apply congrArg conj
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    change h1Gradient Ω i u z * conj (dirD f (coordDir i) z) =
      h1Gradient Ω i u z * dirD (fun w => conj (f w)) (coordDir i) z
    rw [dirD_conj (f.property.1.of_le (by simp))]
  have hv : ⟪h1GradientDivergence Ω g0 g1, h1Value Ω (smoothTraceH1 Ω f)⟫_ℂ =
      conj (∫ z in Ω, h1GradientDivergence Ω g0 g1 z * conj (f z)) := by
    rw [h1Value_smoothTraceH1, firstOrder_inner_toLp]
  have hbnd : ⟪h1GradientConormalDensity hL hγ g0 g1,
      h1BoundaryTrace hL hγ (smoothTraceH1 Ω f)⟫_ℂ =
      conj (∫ θ in boundaryHalfOpenInterval,
        h1GradientConormalDensity hL hγ g0 g1 θ * conj (f (γ θ))) := by
    rw [firstOrder_inner_conjugate_integral]
    apply congrArg conj
    apply integral_congr_ae
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
    rw [hθ]
  have h := congrArg conj
    (h1_conormal_green_compact_test hb hL hγ u g0 g1 hg0 hg1 f.property.conj)
  simp only [map_add, map_sum] at h
  simp_all only [h1ConormalGreenInteriorFunctional_apply, h1ConormalGreenBoundaryFunctional_apply, PolyaNeumann.L2, PolyaNeumann.NeumannH1]

/-- Both sides are genuinely bounded functionals in the test input, so
the compact-smooth identity extends to every actual H¹ test vector. -/
theorem h1ConormalGreenInteriorFunctional_eq_boundary :
    h1ConormalGreenInteriorFunctional Ω u g0 g1 =
      h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1 := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothTraceH1Lin hb hL).equalizer
    (h1ConormalGreenInteriorFunctional Ω u g0 g1).continuous
    (h1ConormalGreenBoundaryFunctional hb hL hγ g0 g1).continuous
  funext f
  exact h1ConormalGreen_smooth hb hL hγ u g0 g1 hg0 hg1 f

/-- The true conormal Green formula against arbitrary H¹ tests, with the
same first-slot test convention as the physical Neumann form. -/
theorem h1_conormal_green w :
    (∑ i : Coord, ⟪h1Gradient Ω i w, h1Gradient Ω i u⟫_ℂ) +
        ⟪h1Value Ω w, h1GradientDivergence Ω g0 g1⟫_ℂ =
      ⟪h1BoundaryTrace hL hγ w, h1GradientConormalDensity hL hγ g0 g1⟫_ℂ := by
  have h := congrArg (fun T : NeumannH1 Ω →L[ℂ] ℂ => T w)
    (h1ConormalGreenInteriorFunctional_eq_boundary hb hL hγ u g0 g1 hg0 hg1)
  rw [h1ConormalGreenInteriorFunctional_apply,
    h1ConormalGreenBoundaryFunctional_apply] at h
  simpa only [map_add, map_sum, inner_conj_symm] using congrArg conj h

end


end PolyaNeumann

end
