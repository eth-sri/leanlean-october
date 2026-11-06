module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.Parabolic.LocalClassical
import HypoellipticAleksandrov.Statements.ParabolicHarnack
import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12

/-!
# The Harnack chain of the common terminal minorant (companion paper, Lemma 3.6)

* `normalized_six_step_harnack`: six translated applications of the unit-cylinder
  Harnack inequality `parabolic_harnack_unit_cylinder` join `(1, 0)` to `(4, v)`, `|v| < 1`,
  inside `(0, ∞) × B₄`, giving `𝔥⁶ u (1, 0) ≤ u (4, v)`.
* `normalized_minorant_comparison`: the Harnack inequality is applied to the time-reversed
  classical scalar solutions supplied by the parabolic marginal bundle; testing against smooth
  compactly supported data gives the measure inequality
  `h • P (T-1, T, 0) ≤ P (T-4, T, v)` for `|v| < 1`, with `h = 𝔥⁶`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal MatrixOrder Topology

/-! ### Calculus for the affine change of scalar variables -/

/- Spatial gradient under an affine change of variables. -/
theorem scalarSpatialGradient_comp_scalarAffine {d : ℕ} {V : TimeVelocity d → ℝ}
    {α a : ℝ} {c : PDE.Vec d} {e : ℝ} {z : TimeVelocity d}
    (hV : DifferentiableAt ℝ (fun y : PDE.Vec d => V (α + a * z.1, y)) (c + e • z.2)) :
    scalarSpatialGradient (fun p => V (scalarAffine α a c e p)) z =
      e • scalarSpatialGradient V (scalarAffine α a c e z) := by
  have hA : HasFDerivAt (fun y : PDE.Vec d => c + e • y)
      (e • ContinuousLinearMap.id ℝ (PDE.Vec d)) z.2 :=
    ((hasFDerivAt_id (𝕜 := ℝ) z.2).const_smul e).const_add c
  have hcomp := hV.hasFDerivAt.comp z.2 hA
  funext i
  change fderiv ℝ ((fun y : PDE.Vec d => V (α + a * z.1, y)) ∘ fun y => c + e • y) z.2
      (PDE.basisVec i) = e * fderiv ℝ (fun y : PDE.Vec d => V (α + a * z.1, y))
        (c + e • z.2) (PDE.basisVec i)
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/- The anisotropic `C^{1,2}` class is stable under affine changes of variables. -/
theorem isScalarC12On_comp_scalarAffine {d : ℕ} {u : TimeVelocity d → ℝ}
    {S S' : Set (TimeVelocity d)} {α a : ℝ} {c : PDE.Vec d} {e }
    (hu : IsScalarC12On u S') (hmaps : MapsTo (scalarAffine α a c e) S S') :
    IsScalarC12On (fun p => u (scalarAffine α a c e p)) S := by
  have hAff := contDiff_scalarAffine α a c e
  have hcont := hAff.continuous
  have hdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun r : ℝ => u (r, c + e • z.2)) (α + a * z.1) :=
    fun z hz => hu.timeSlice_differentiableAt (hmaps hz)
  have hspace : ∀ z ∈ S, ContDiffAt ℝ 2 (fun y : PDE.Vec d => u (α + a * z.1, y))
      (c + e • z.2) := fun z hz => hu.spatialSlice_contDiffAt (hmaps hz)
  refine ⟨hu.continuousOn.comp hcont.continuousOn hmaps, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h1 : DifferentiableAt ℝ (fun r : ℝ => α + a * r) z.1 := by fun_prop
    exact DifferentiableAt.comp (g := fun r : ℝ => u (r, c + e • z.2)) z.1 (hdiff z hz) h1
  · intro z hz
    have h1 : ContDiffAt ℝ 2 (fun y : PDE.Vec d => c + e • y) z.2 := by fun_prop
    exact ContDiffAt.comp (g := fun y : PDE.Vec d => u (α + a * z.1, y)) z.2 (hspace z hz) h1
  · refine ContinuousOn.congr (f := fun z => a * scalarTimeDerivative u (scalarAffine α a c e z))
      (continuousOn_const.mul
        (hu.continuousOn_scalarTimeDerivative.comp hcont.continuousOn hmaps)) ?_
    intro z hz
    exact scalarTimeDerivative_comp_scalarAffine (hdiff z hz)
  · refine ContinuousOn.congr (f := fun z => e • scalarSpatialGradient u (scalarAffine α a c e z))
      (ContinuousOn.const_smul
        (hu.continuousOn_scalarSpatialGradient.comp hcont.continuousOn hmaps) e) ?_
    intro z hz
    exact scalarSpatialGradient_comp_scalarAffine
      ((hspace z hz).differentiableAt (by norm_num))
  · refine ContinuousOn.congr
      (f := fun z => e ^ 2 • scalarSpatialHessian u (scalarAffine α a c e z))
      (ContinuousOn.const_smul
        (hu.continuousOn_scalarSpatialHessian.comp hcont.continuousOn hmaps) (e ^ 2)) ?_
    intro z hz
    exact scalarSpatialHessian_comp_scalarAffine (hspace z hz)

/-! ### The six-step Harnack chain -/

/- **Six-step Harnack chain** (companion paper, Lemma 3.6, analytic part).  Translated
applications of the unit-cylinder Harnack inequality along the points
`(1 + j/2, (j/6) v)`, `j = 0, ..., 6`, with cylinders in `(0, ∞) × B₄`. -/
abbrev timeReversal {d } (T : ℝ) : TimeVelocity d → TimeVelocity d :=
  scalarAffine T (-1) 0 1

theorem timeReversal_apply {d } (T θ : ℝ) (v : PDE.Vec d) :
    timeReversal T (θ, v) = (T - θ, v) := by
  simp [timeReversal, scalarAffine, sub_eq_add_neg]

theorem timeReversal_mapsTo {d } {Ω : Set (PDE.Vec d)} (T : ℝ) :
    MapsTo (timeReversal T) (Ioi (0 : ℝ) ×ˢ Ω)
      (ParabolicProbe.scalarPastOpenCylinder Ω stationary T) := by
  rintro ⟨θ, v⟩ ⟨hθ, hv⟩
  rw [mem_scalarPastOpenCylinder_stationary, timeReversal_apply]
  exact ⟨by simpa using hθ, hv⟩

/- The time-reversed classical scalar solution is `C^{1,2}` on `(0, ∞) × Ω`. -/
theorem timeReversed_isScalarC12On {d Ω} (hΩ : IsOpen Ω)
    {B T F} {V : TimeVelocity d → ℝ}
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary
      (zIndependentCoefficient B) T F V) :
    IsScalarC12On (fun p => V (timeReversal T p)) (Ioi (0 : ℝ) ×ˢ Ω) :=
  isScalarC12On_comp_scalarAffine
    (isScalarC12On_of_isOpen_contDiffOn_two (isOpen_scalarPastOpenCylinder_stationary hΩ T)
      (hV.2.2.1.of_le (by norm_num))) (timeReversal_mapsTo T)

/- The time-reversed classical scalar solution solves the forward equation with the
reversed coefficient. -/
theorem timeReversed_equation {d Ω} (hΩ : IsOpen Ω)
    {B T F} {V : TimeVelocity d → ℝ}
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary
      (zIndependentCoefficient B) T F V) :
    ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ω,
      scalarTimeDerivative (fun p => V (timeReversal T p)) p =
        matrixContraction (coefficientAt B (timeReversal T p))
          (scalarSpatialHessian (fun p => V (timeReversal T p)) p) := by
  intro p hp
  have hc12 := isScalarC12On_of_isOpen_contDiffOn_two
    (isOpen_scalarPastOpenCylinder_stationary hΩ T) (hV.2.2.1.of_le (by norm_num))
  have h1 := hc12.timeSlice_differentiableAt (timeReversal_mapsTo T hp)
  have h2 := hc12.spatialSlice_contDiffAt (timeReversal_mapsTo T hp)
  have hop := hV.2.2.2.1 _ (timeReversal_mapsTo T hp)
  have hgrad : PDE.vecDot ((0 : ℝ → PDE.Vec d → PDE.Vec d)
      (timeReversal T p).1 (timeReversal T p).2)
      (scalarSpatialGradient V (timeReversal T p)) = 0 := by
    simp [PDE.vecDot]
  rw [scalarParabolicOperator_apply, hgrad, add_zero] at hop
  rw [scalarTimeDerivative_comp_scalarAffine h1, scalarSpatialHessian_comp_scalarAffine h2,
    one_pow, one_smul]
  change -1 * scalarTimeDerivative V (timeReversal T p) = _
  have hop' : scalarTimeDerivative V (timeReversal T p) =
      -matrixContraction (coefficientAt B (timeReversal T p))
        (scalarSpatialHessian V (timeReversal T p)) := by
    have : zIndependentCoefficient B (timeReversal T p).1 (timeReversal T p).2 0 =
        coefficientAt B (timeReversal T p) := rfl
    rw [this] at hop
    linarith
  rw [hop']
  ring

/- Smooth coefficients are jointly continuous. -/
theorem continuous_coefficientAt_of_smooth {d } {B : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B)) :
    Continuous (coefficientAt B) := by
  refine continuous_matrix fun i j => ?_
  exact (hB i j).continuous.comp
    (continuous_fst.prodMk (continuous_snd.prodMk (continuous_const (y := (0 : PDE.Vec d)))))

/-! ### The measure comparison -/

end HypoellipticAleksandrov.KineticAleksandrov.Decay
