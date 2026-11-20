/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCFiniteCoordinateLimit
import Mathlib.MeasureTheory.Measure.Map

/-! The countable field-and-measure coordinate law obtained from the finite-coordinate limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω hX γ hM

/-- Measurable transformations of the limiting measure and shifts of the field give an
almost surely measurable joint coordinate path. -/
theorem aemeasurable_gmcTiltCoordinatePath_transform
    (shift : TestFn → ℝ) (F : Measure ℂ → Measure ℂ) (hF : Measurable F) :
    AEMeasurable (fun ω => gmcTiltCoordinatePath (fun f => X ω f + shift f) (F (M ω))) P := by
  have hXev : Measurable (fun ω (f : TestFn) => X ω f) := .of_eval fun f => (hX.2 f).1
  have hj (j : Option (ℚ × ℚ)) :
      AEMeasurable (fun ω => (F (M ω) (gmcTiltCoordinateSet j)).toReal) P := by
    have hs : MeasurableSet (gmcTiltCoordinateSet j) := by
      cases j with
      | none => exact MeasurableSet.univ
      | some i => exact gmcLowerBox_measurableSet i
    obtain ⟨g, hg, he⟩ := equatorGFF_GMC_function_field_proxy P X hX γ M hM
      (fun _ μ => F μ (gmcTiltCoordinateSet j))
      (((Measure.measurable_coe hs).comp hF).comp measurable_snd)
    exact ENNReal.measurable_toReal.comp_aemeasurable
      ((hg.comp hXev).aemeasurable.congr he.symm)
  obtain ⟨q, hq, hEq⟩ := AEMeasurable.of_eval hj
  refine ⟨fun ω => Sum.elim (fun f => X ω f + shift f) (q ω), .of_eval ?_, ?_⟩
  · rintro (f | i)
    · exact (hX.2 f).1.add measurable_const
    · exact hq.eval
  · filter_upwards [hEq] with ω hω
    funext i
    cases i with
    | inl f => rfl
    | inr j => exact congrFun hω j

theorem aemeasurable_gmcTiltCoordinatePath :
    AEMeasurable (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω)) P := by
  simpa using aemeasurable_gmcTiltCoordinatePath_transform P X hX γ M hM (fun _ => 0) id measurable_id

theorem aemeasurable_gmcTiltCoordinatePath_withDensity
    (shift : TestFn → ℝ) (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) :
    AEMeasurable (fun ω => gmcTiltCoordinatePath (fun f => X ω f + shift f) ((M ω).withDensity ρ)) P := by
  refine aemeasurable_gmcTiltCoordinatePath_transform P X hX γ M hM shift (fun μ => μ.withDensity ρ) ?_
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hρ.indicator hs)

/-- The complete product path of field evaluations and determining GMC masses has the tilted
law asserted by Cameron--Martin. -/
theorem equatorGFF_GMC_fullCoordinate_limit_law
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun (r : ℝ) (z : ℂ) => gaussianCovariance P (fun ω => Xc ω z r) L) c atTop) :
    Measure.map (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (L ω - gaussianVariance P L / 2)))) =
    Measure.map (fun ω => gmcTiltCoordinatePath
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))) P := by
  classical
  let density  := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q  := P.withDensity density
  let leftPath  := fun ω =>
    gmcTiltCoordinatePath (fun f => X ω f) (M ω)
  let shift  := fun f => gaussianCovariance P (fun ω => X ω f) L
  let rightPath  := fun ω =>
    gmcTiltCoordinatePath (fun f => X ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
  have hmass : ∫⁻ ω, density ω ∂P = 1 := by
    simpa [density] using
      @equatorGFF_gaussianL2_tilt_density_integral_eq_one Ω _ P hX.1 X hX Xc hXc L hL
  have hQprob : IsProbabilityMeasure Q := ⟨by simpa [Q] using hmass⟩
  have hleftAEMeas : AEMeasurable leftPath Q :=
    (aemeasurable_gmcTiltCoordinatePath P X hX γ M hM).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hrightAEMeas : AEMeasurable rightPath P :=
    aemeasurable_gmcTiltCoordinatePath_withDensity P X hX γ M hM shift _ (by fun_prop)
  let leftMeasure  := Measure.map leftPath Q
  let rightMeasure  := Measure.map rightPath P
  let C  :=
    MeasureTheory.measurableCylinders (fun _ : gmcTiltCoordinateIndex => ℝ)
  have hCylinder : ∀ A ∈ C, leftMeasure A = rightMeasure A := by
    intro A hA
    obtain ⟨s, S, hS, rfl⟩ :=
      (MeasureTheory.mem_measurableCylinders
        (α := fun _ : gmcTiltCoordinateIndex => ℝ) A).mp hA
    let leftFinite  := fun ω =>
      gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)
    let rightFinite  := fun ω =>
      gmcTiltFiniteCoordinatePath s
        (fun f => X ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
    have hRestr : Measurable
        (fun φ : gmcTiltCoordinateIndex → ℝ => fun i : {i // i ∈ s} => φ i.1) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_pi_apply i.1
    have hleftFiniteAEMeas : AEMeasurable leftFinite Q := hRestr.comp_aemeasurable hleftAEMeas
    have hrightFiniteAEMeas : AEMeasurable rightFinite P := hRestr.comp_aemeasurable hrightAEMeas
    have hFiniteLaw : Measure.map leftFinite Q = Measure.map rightFinite P := by
      apply equatorGFF_finiteGmcCoordinate_limit_law <;> assumption
    have hmap := congrArg (fun μ : Measure (∀ _i : {i // i ∈ s}, ℝ) => μ S) hFiniteLaw
    rw [Measure.map_apply_of_aemeasurable hleftFiniteAEMeas hS,
      Measure.map_apply_of_aemeasurable hrightFiniteAEMeas hS] at hmap
    rw [show leftMeasure = Measure.map leftPath Q by rfl,
      show rightMeasure = Measure.map rightPath P by rfl,
      Measure.map_apply_of_aemeasurable hleftAEMeas hS.cylinder,
      Measure.map_apply_of_aemeasurable hrightAEMeas hS.cylinder]
    exact hmap
  have hLeftUniv : leftMeasure Set.univ = 1 := by
    simp
  have hRightUniv : rightMeasure Set.univ = 1 := by
    dsimp [rightMeasure]
    rw [Measure.map_apply_of_aemeasurable hrightAEMeas MeasurableSet.univ]
    exact hX.1.measure_univ
  have hFiniteLeft : IsFiniteMeasure leftMeasure := ⟨by rw [hLeftUniv]; simp⟩
  exact @ext_of_generate_finite (gmcTiltCoordinateIndex → ℝ) _ leftMeasure rightMeasure C
    (by simpa [C] using
      (MeasureTheory.generateFrom_measurableCylinders
        (α := fun _ : gmcTiltCoordinateIndex => ℝ)).symm)
    MeasureTheory.isPiSystem_measurableCylinders hFiniteLeft hCylinder (by
    rw [hLeftUniv, hRightUniv])

end

end DOZZ.Proofs
