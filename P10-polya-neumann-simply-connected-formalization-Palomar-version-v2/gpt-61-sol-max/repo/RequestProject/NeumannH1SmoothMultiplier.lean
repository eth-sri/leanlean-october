module

public import RequestProject.WeakProductRule

public import RequestProject.L2Pairing

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.TraceH1
public import RequestProject.LpBoundedMultiplier

/-!
# Multiplication in the actual weak-gradient H¹ space

A globally smooth coefficient with bounded value and first derivatives defines
a genuine bounded H¹ multiplication operator. The product rule is proved by
testing the original weak gradient against the compact product aφ. Smooth
compact coefficients supply the bounds, so this applies to actual cutoff
coordinate functions without an assumed weak product rule.
-/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter

/-- Bounds on an actual smooth coefficient and its two real derivatives. -/
structure SmoothH1Coefficient where
  toFun : ℂ → ℂ
  smooth : RealSmooth toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  value_bound : ∀ z, ‖toFun z‖ ≤ bound
  derivative_bound : ∀ (i : Coord) z, ‖fderiv ℝ toFun z (coordDir i)‖ ≤ bound

instance : CoeFun SmoothH1Coefficient (fun _ => PlaneMap) := ⟨SmoothH1Coefficient.toFun⟩

/-- Smooth compact coefficients have actual global value and derivative bounds. -/
theorem smoothTraceTests_exists_h1Coefficient_bound (a : smoothTraceTests) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ z, ‖a z‖ ≤ B) ∧
      ∀ (i : Coord) z, ‖fderiv ℝ (a : PlaneMap) z (coordDir i)‖ ≤ B := by
  obtain ⟨B, hB⟩ := a.property.2.1.exists_bound_of_continuous a.property.1.continuous
  obtain ⟨B₀, hB₀⟩ := (a.property.dirD (coordDir 0)).2.1.exists_bound_of_continuous
    (a.property.dirD (coordDir 0)).1.continuous
  obtain ⟨B₁, hB₁⟩ := (a.property.dirD (coordDir 1)).2.1.exists_bound_of_continuous
    (a.property.dirD (coordDir 1)).1.continuous
  refine ⟨max 0 (max B (max B₀ B₁)), le_max_left _ _, ?_, ?_⟩
  · simp_all
  · intro i z
    fin_cases i
    · exact (hB₀ z).trans ((le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (hB₁ z).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

/-- An actual compact smooth function as a bounded H¹ coefficient. -/
def smoothTraceTestsH1Coefficient (a : smoothTraceTests) : SmoothH1Coefficient where
  toFun := a
  smooth := a.property.1
  bound := Classical.choose (smoothTraceTests_exists_h1Coefficient_bound a)
  bound_nonneg := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).1
  value_bound := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.1
  derivative_bound := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.2



theorem coefficient_derivative_continuous (a : SmoothH1Coefficient) i :
    Continuous (fun z => fderiv ℝ (a : PlaneMap) z (coordDir i)) :=
  ((a.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous

def h1SmoothCoefficientL2 Ω (a : SmoothH1Coefficient) : L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (a : PlaneMap) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound)

def h1SmoothCoefficientDerivativeL2 (Ω : PlanarSet) (a : SmoothH1Coefficient) (i : Coord) :
    L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (fun z => fderiv ℝ (a : PlaneMap) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i))

section
variable (Ω : PlanarSet) (a : SmoothH1Coefficient)
include Ω a

theorem h1SmoothCoefficientL2_ae u :
    (h1SmoothCoefficientL2 Ω a u : PlaneMap) =ᵐ[volume.restrict Ω] fun z => a z * u z :=
  lpBoundedMultiplier_ae (a : PlaneMap) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound) u

theorem h1SmoothCoefficientDerivativeL2_ae
    i u :
    (h1SmoothCoefficientDerivativeL2 Ω a i u : PlaneMap) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (a : PlaneMap) z (coordDir i) * u z :=
  lpBoundedMultiplier_ae (fun z => fderiv ℝ (a : PlaneMap) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i)) u

theorem norm_h1SmoothCoefficientL2_apply_le
    u : ‖h1SmoothCoefficientL2 Ω a u‖ ≤ a.bound * ‖u‖ :=
  norm_lpBoundedMulLin_le (a : PlaneMap) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound) u

theorem norm_h1SmoothCoefficientDerivativeL2_apply_le i u :
    ‖h1SmoothCoefficientDerivativeL2 Ω a i u‖ ≤ a.bound * ‖u‖ :=
  norm_lpBoundedMulLin_le (fun z => fderiv ℝ (a : PlaneMap) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i)) u

end


theorem coefficient_test_mul  (a : SmoothH1Coefficient)
     (hφ : TestFunction Ω φ) : TestFunction Ω (fun z => a z * φ z) :=
  ⟨a.smooth.mul hφ.1, hφ.2.1.mul_left, tsupport_mul_subset_right.trans hφ.2.2⟩

/-- The genuine weak product rule, with both derivative terms in actual L². -/
theorem isWeakGradient_h1SmoothCoefficientL2  a
      (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (h1SmoothCoefficientL2 Ω a u)
      (fun i => h1SmoothCoefficientL2 Ω a (g i) +
        h1SmoothCoefficientDerivativeL2 Ω a i u) := by
  exact isWeakGradient_l2Multiplier a a.smooth (h1SmoothCoefficientL2 Ω a)
    (h1SmoothCoefficientDerivativeL2 Ω a) (h1SmoothCoefficientL2_ae Ω a)
    (h1SmoothCoefficientDerivativeL2_ae Ω a) hu

def smoothCoefficientH1Vector Ω a
    u  :=
  h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u))

section
variable (Ω ) (a : SmoothH1Coefficient) (u : NeumannH1 Ω)

section
include Ω a u

theorem smoothCoefficientH1Vector_value :
    h1Value Ω (smoothCoefficientH1Vector Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  h1Value_h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u))

theorem smoothCoefficientH1Vector_gradient i :
    h1Gradient Ω i (smoothCoefficientH1Vector Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  h1Gradient_h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u)) i

end


def smoothCoefficientH1Lin Ω (a : SmoothH1Coefficient) :
    NeumannH1 Ω →ₗ[ℂ] NeumannH1 Ω where
  toFun := smoothCoefficientH1Vector Ω a
  map_add' u v := by
    apply h1_ext
    · simp  [smoothCoefficientH1Vector_value]
    · intro i
      simp  [smoothCoefficientH1Vector_gradient]
      abel
  map_smul' c u := by
    apply h1_ext
    · simp  [smoothCoefficientH1Vector_value]
    · intro i
      simp  [smoothCoefficientH1Vector_gradient]

section
include Ω a u

theorem smoothCoefficientH1Lin_norm_le :
    ‖smoothCoefficientH1Lin Ω a u‖ ≤ (2 * Real.sqrt 3 * a.bound) * ‖u‖ := by
  have hv : ‖h1Value Ω (smoothCoefficientH1Lin Ω a u)‖ ≤ 2 * a.bound * ‖u‖ := by
    exact (norm_h1SmoothCoefficientL2_apply_le Ω a _).trans
      ((mul_le_mul_of_nonneg_left (h1Value_norm_le u) a.bound_nonneg).trans
        (by nlinarith [norm_nonneg u, a.bound_nonneg]))
  have hg (i : Coord) :
      ‖h1Gradient Ω i (smoothCoefficientH1Lin Ω a u)‖ ≤ 2 * a.bound * ‖u‖ := by
    calc
      _ ≤ ‖h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u)‖ +
          ‖h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u)‖ := norm_add_le _ _
      _ ≤ a.bound * ‖h1Gradient Ω i u‖ + a.bound * ‖h1Value Ω u‖ :=
        add_le_add (norm_h1SmoothCoefficientL2_apply_le Ω a _)
          (norm_h1SmoothCoefficientDerivativeL2_apply_le Ω a i _)
      _ ≤ a.bound * ‖u‖ + a.bound * ‖u‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (h1Gradient_norm_le u i) a.bound_nonneg)
          (mul_le_mul_of_nonneg_left (h1Value_norm_le u) a.bound_nonneg)
      _ = _ := by ring
  have hn := h1_norm_le_of_components (smoothCoefficientH1Lin Ω a u)
    hv hg
  convert hn using 1; ring

end


/-- Actual bounded multiplication in H¹, with no regularity premise on the input. -/
def neumannH1SmoothMultiplier (Ω : PlanarSet) (a : SmoothH1Coefficient) :
    ComplexEnd (NeumannH1 Ω) :=
  (smoothCoefficientH1Lin Ω a).mkContinuous (2 * Real.sqrt 3 * a.bound)
    (smoothCoefficientH1Lin_norm_le Ω a)

section
include Ω a u

theorem h1Value_neumannH1SmoothMultiplier :
    h1Value Ω (neumannH1SmoothMultiplier Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  smoothCoefficientH1Vector_value Ω a u

theorem h1Gradient_neumannH1SmoothMultiplier i :
    h1Gradient Ω i (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  smoothCoefficientH1Vector_gradient Ω a u i

end


end


def smoothCoefficientTestProduct (a : SmoothH1Coefficient) (f : smoothTraceTests) :
    smoothTraceTests :=
  ⟨fun z => a z * f z, coefficient_test_mul a f.property⟩



/-- The completed product agrees with the actual compact smooth product. -/
theorem neumannH1SmoothMultiplier_smooth  (hΩ : IsOpen Ω)
    a f :
    neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f) =
      smoothTraceH1 Ω (smoothCoefficientTestProduct a f) := by
  apply h1Value_injective hΩ
  simp  [h1Value_neumannH1SmoothMultiplier]
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientL2_ae Ω a (h1Value Ω (smoothTraceH1 Ω f)),
    (smoothTraceTests_memLp Ω f).coeFn_toLp,
    (smoothTraceTests_memLp Ω (smoothCoefficientTestProduct a f)).coeFn_toLp]
    with z hm hf hp
  simp   at hm
  rw [hm, hf, hp]
  rfl

/-- Multiplication by the actual boundary values of the same coefficient. -/
def h1SmoothBoundaryMultiplier {Ω : PlanarSet} {γ : ComplexCurve}
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) : ComplexEnd BoundaryL2 :=
  lpBoundedMultiplier (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ)))

theorem h1SmoothBoundaryMultiplier_ae  
    (hγ : IsBoundaryParam Ω γ) a g :
    (h1SmoothBoundaryMultiplier hγ a g : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval] fun θ => a (γ θ) * g θ :=
  lpBoundedMultiplier_ae (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ))) g

/-- The physical trace product rule for every actual H¹ vector follows from
the dense smooth restrictions and the two already bounded product operators. -/
theorem h1BoundaryTrace_neumannH1SmoothMultiplier 
    (hb : Bornology.IsBounded Ω) hL 
    (hγ : IsBoundaryParam Ω γ) a u :
    h1BoundaryTrace hL hγ (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hL hγ u) := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => h1BoundaryTrace hL hγ (neumannH1SmoothMultiplier Ω a v) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hL hγ v)) u ?_ ?_
  · exact isClosed_eq ((h1BoundaryTrace hL hγ).continuous.comp
      (neumannH1SmoothMultiplier Ω a).continuous)
      ((h1SmoothBoundaryMultiplier hγ a).continuous.comp (h1BoundaryTrace hL hγ).continuous)
  · intro f
    change h1BoundaryTrace hL hγ (neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f)) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hL hγ (smoothTraceH1 Ω f))
    rw [neumannH1SmoothMultiplier_smooth hL.1.1]
    apply Lp.ext
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ (smoothCoefficientTestProduct a f),
      h1SmoothBoundaryMultiplier_ae hγ a (h1BoundaryTrace hL hγ (smoothTraceH1 Ω f)),
      h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hp hm hf
    rw [hp, hm, hf]
    rfl

end PolyaNeumann

end
