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
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
section
variable (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include hX hM

theorem exists_measurable_unweighted_fullPath_proxy
    :
    ∃ G : Ω → gmcTiltCoordinateIndex → ℝ,
      Measurable G ∧
      (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω)) =ᵐ[P] G := by
  obtain ⟨E, hE, hEae⟩ := equatorGFF_GMC_finiteEval_field_proxy P X hX γ M hM
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  have heval : Measurable eval := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  let G : Ω → gmcTiltCoordinateIndex → ℝ := fun ω i =>
    match i with
    | .inl f => eval ω f
    | .inr j => (E (eval ω) j).toReal
  have hG : Measurable G := by
    rw [measurable_pi_iff]
    intro i
    cases i with
    | inl f => exact (hX.2 f).1
    | inr j =>
      exact ENNReal.measurable_toReal.comp
        ((measurable_pi_apply j).comp (hE.comp heval))
  have hEq : (fun ω => gmcTiltCoordinatePath (eval ω) (M ω)) =ᵐ[P] G := by
    filter_upwards [hEae] with ω hω
    funext i
    cases i with
    | inl f => rfl
    | inr j =>
      exact congrArg ENNReal.toReal (congrFun hω j)
  tauto

theorem exists_measurable_weighted_fullPath_proxy
    (shift : TestFn → ℝ) (w : BoundedContinuousFunction ℂ ℝ) :
    ∃ G : Ω → gmcTiltCoordinateIndex → ℝ,
      Measurable G ∧
      (fun ω => gmcTiltCoordinatePath (fun f => X ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) =ᵐ[P] G := by
  have heval : Measurable (fun ω f => X ω f) := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hW :=
    ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hcoord : ∀ j : Option (ℚ × ℚ),
      ∃ g : (TestFn → ℝ) → ℝ, Measurable g ∧
        (fun ω => ((M ω).withDensity (fun z => ENNReal.ofReal (w z))
          (gmcTiltCoordinateSet j)).toReal) =ᵐ[P]
          fun ω => g (X ω) := by
    intro j
    let B := gmcTiltCoordinateSet j
    have hB : MeasurableSet B := by
      cases j with
      | none => exact MeasurableSet.univ
      | some i => exact gmcLowerBox_measurableSet i
    let H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun _ μ =>
      (μ.withDensity (fun z => ENNReal.ofReal (w z))) B
    have hH : Measurable (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2) := by
      have hEval : (fun μ : Measure ℂ =>
          (μ.withDensity (fun z => ENNReal.ofReal (w z))) B) =
          fun μ => ∫⁻ z, B.indicator (fun z => ENNReal.ofReal (w z)) z ∂μ := by
        simp_all
      rw [show (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2) =
          fun p => ∫⁻ z, B.indicator (fun z => ENNReal.ofReal (w z)) z ∂p.2 by
            aesop]
      fun_prop
    obtain ⟨gE, hgE, hEq⟩ :=
      equatorGFF_GMC_function_field_proxy P X hX γ M hM H hH
    let g : (TestFn → ℝ) → ℝ := fun q => (gE q).toReal
    refine ⟨g, (ENNReal.measurable_toReal.comp hgE), ?_⟩
    filter_upwards [hEq] with ω hω
    tauto
  choose g hg hEq using hcoord
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let G : Ω → gmcTiltCoordinateIndex → ℝ := fun ω i =>
    match i with
    | .inl f => eval ω f + shift f
    | .inr j => g j (eval ω)
  have hG : Measurable G := by
    rw [measurable_pi_iff]
    intro i
    cases i with
    | inl f => exact (hX.2 f).1.add measurable_const
    | inr j => exact (hg j).comp heval
  have hEqAll : (fun ω => gmcTiltCoordinatePath
      (fun f => X ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) =ᵐ[P] G := by
    have hpoint :=
      ae_all_iff.mpr hEq
    filter_upwards [hpoint] with ω hω
    funext i
    cases i with
    | inl f => rfl
    | inr j => exact hω j
  exact ⟨G, hG, hEqAll⟩

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
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q := P.withDensity density
  let leftPath : Ω → gmcTiltCoordinateIndex → ℝ := fun ω =>
    gmcTiltCoordinatePath (fun f => X ω f) (M ω)
  let shift : TestFn → ℝ := fun f => gaussianCovariance P (fun ω => X ω f) L
  let rightPath : Ω → gmcTiltCoordinateIndex → ℝ := fun ω =>
    gmcTiltCoordinatePath (fun f => X ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
  have hmass : ∫⁻ ω, density ω ∂P = 1 := by
    simpa [density] using
      @equatorGFF_gaussianL2_tilt_density_integral_eq_one Ω _ P hX.1 X hX Xc hXc L hL
  have hQprob : IsProbabilityMeasure Q := by
    refine ⟨?_⟩
    aesop
  obtain ⟨leftProxy, hleftProxyMeas, hleftProxyAE⟩ :=
    exists_measurable_unweighted_fullPath_proxy P X hX γ M hM
  have hdenAEMeas : AEMeasurable density P := by
    have hLmeas : AEMeasurable L P := hL.1.aestronglyMeasurable.aemeasurable
    fun_prop
  have hdenNe : ∀ᵐ ω ∂P, density ω ≠ 0 := by
    filter_upwards [] with ω
    positivity
  have hleftProxyQ : leftPath =ᵐ[Q] leftProxy := by
    exact (withDensity_ae_eq hdenAEMeas hdenNe).2 (by assumption)
  have hleftAEMeas : AEMeasurable leftPath Q :=
    hleftProxyMeas.aemeasurable.congr hleftProxyQ.symm
  obtain ⟨u, w, -, hw, hconv, heventual, -⟩ :=
    equatorGFF_expCovariance_finiteCoordinate_tendstoInMeasure
      P X hX Xc hXc γ M hM L hL c hc (∅ : Finset gmcTiltCoordinateIndex)
  have hwEq : ∀ z : ℂ, w z = Real.exp (γ * c z) := by
    intro z
    exact equatorGFF_expCovariance_weight_limit_value
      P Xc L γ c hc u w hconv heventual z
  obtain ⟨rightProxy, hrightProxyMeas, hrightProxyAE⟩ :=
    exists_measurable_weighted_fullPath_proxy P X hX γ M hM shift w
  have hrightWeightEq (ω : Ω) :
      (M ω).withDensity (fun z => ENNReal.ofReal (w z)) =
      (M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))) := by
    congr 1
    funext z
    rw [hwEq z]
  have hrightProxyEq : rightPath =ᵐ[P] rightProxy := by
    have hEq : (fun ω => gmcTiltCoordinatePath (fun f => X ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) = rightPath := by
      funext ω
      rw [hrightWeightEq ω]
    exact hEq.symm ▸ hrightProxyAE
  have hrightAEMeas : AEMeasurable rightPath P :=
    hrightProxyMeas.aemeasurable.congr hrightProxyEq.symm
  let leftMeasure := Measure.map leftPath Q
  let rightMeasure := Measure.map rightPath P
  let C :=
    MeasureTheory.measurableCylinders (fun _ : gmcTiltCoordinateIndex => ℝ)
  have hCylinder : ∀ A ∈ C, leftMeasure A = rightMeasure A := by
    intro A hA
    obtain ⟨s, S, hS, rfl⟩ :=
      (MeasureTheory.mem_measurableCylinders
        (α := fun _ : gmcTiltCoordinateIndex => ℝ) A).mp hA
    let leftFinite : Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun ω =>
      gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)
    let rightFinite : Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun ω =>
      gmcTiltFiniteCoordinatePath s
        (fun f => X ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
    have hRestr : Measurable
        (fun φ : gmcTiltCoordinateIndex → ℝ => fun i : {i // i ∈ s} => φ i.1) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_pi_apply i.1
    have hleftFiniteComp : leftFinite =
        (fun φ : gmcTiltCoordinateIndex → ℝ => fun i : {i // i ∈ s} => φ i.1) ∘ leftPath := by
      funext ω
      rfl
    have hrightFiniteComp : rightFinite =
        (fun φ : gmcTiltCoordinateIndex → ℝ => fun i : {i // i ∈ s} => φ i.1) ∘ rightPath := by
      funext ω
      rfl
    have hleftFiniteAEMeas : AEMeasurable leftFinite Q := by
      rw [hleftFiniteComp]
      exact hRestr.comp_aemeasurable hleftAEMeas
    have hrightFiniteAEMeas : AEMeasurable rightFinite P := by
      rw [hrightFiniteComp]
      exact hRestr.comp_aemeasurable hrightAEMeas
    have hFiniteLaw : Measure.map leftFinite Q = Measure.map rightFinite P := by
      simpa [leftFinite, rightFinite, Q, density, shift] using
        equatorGFF_finiteGmcCoordinate_limit_law P X hX Xc hXc γ M hM L hL c hc s
    have hmap := congrArg (fun μ : Measure (∀ _i : {i // i ∈ s}, ℝ) => μ S) hFiniteLaw
    rw [Measure.map_apply_of_aemeasurable hleftFiniteAEMeas hS,
      Measure.map_apply_of_aemeasurable hrightFiniteAEMeas hS] at hmap
    have hpreLeft : leftPath ⁻¹' MeasureTheory.cylinder s S = leftFinite ⁻¹' S := by
      ext ω
      simp
      rfl
    have hpreRight : rightPath ⁻¹' MeasureTheory.cylinder s S = rightFinite ⁻¹' S := by
      ext ω
      simp
      rfl
    calc
      leftMeasure _ = Q _ := by
        dsimp [leftMeasure]
        rw [Measure.map_apply_of_aemeasurable hleftAEMeas hS.cylinder]
      _ = Q _ := by rfl
      _ = P _ := hmap
      _ = P (rightPath ⁻¹' MeasureTheory.cylinder s S) := by rfl
      _ = rightMeasure _ := by
        dsimp [rightMeasure]
        rw [Measure.map_apply_of_aemeasurable hrightAEMeas hS.cylinder]
  have hUnivC : Set.univ ∈ C :=
    MeasureTheory.univ_mem_measurableCylinders (fun _ : gmcTiltCoordinateIndex => ℝ)
  have hLeftUniv : leftMeasure Set.univ = 1 := by
    dsimp [leftMeasure]
    rw [Measure.map_apply_of_aemeasurable hleftAEMeas MeasurableSet.univ]
    simp [hQprob.measure_univ]
  have hRightUniv : rightMeasure Set.univ = 1 := by
    rw [Measure.map_apply_of_aemeasurable hrightAEMeas MeasurableSet.univ]
    exact hX.1.measure_univ
  have hFiniteLeft : IsFiniteMeasure leftMeasure := ⟨by simp⟩
  have hUnivEq : leftMeasure Set.univ = rightMeasure Set.univ := by
    rw [hLeftUniv, hRightUniv]
  exact @ext_of_generate_finite _ _ leftMeasure rightMeasure C
    (by simpa [C] using
      (MeasureTheory.generateFrom_measurableCylinders
       ).symm)
    MeasureTheory.isPiSystem_measurableCylinders hFiniteLeft hCylinder hUnivEq

end

end

end DOZZ.Proofs
