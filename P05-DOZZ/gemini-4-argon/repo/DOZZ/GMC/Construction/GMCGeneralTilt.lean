/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GFFStructure.GaussianClosure
public import DOZZ.GMC.Construction.CircleAverageJointVersion
public import DOZZ.GMC.Construction.GMCUniqueAe
public import DOZZ.GMC.FiniteGaussianTilt
public import DOZZ.GMC.GaussianInputs
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-! Finite-coordinate Cameron--Martin transport for test evaluations and circle averages. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def testCircleCoordinate {Ω : Type*} (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (r : ℝ) : ℂ ⊕ TestFn → Ω → ℝ :=
  Sum.elim (fun x ω => Xc ω x r) (fun f ω => X ω f)


/-- Finite-dimensional tilt for any selected collection of test and circle-average coordinates.
The only nonzero tilt coefficient is on `L`; consequently all selected coordinates shift by their
covariance with `L`. -/
theorem equatorGFF_finite_test_circle_tilt
    {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc) r
    L (hL : IsGaussianL2Limit P X L)
    (coord : T → ℂ ⊕ TestFn) t
    (F : (Option T → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t * L ω - t ^ 2 / 2 * gaussianVariance P L)) *
      F (fun i => match i with
        | none => L ω
        | some j => testCircleCoordinate X Xc r (coord j) ω) ∂P) =
    ∫⁻ ω, F (fun i =>
      (match i with
        | none => L ω
        | some j => testCircleCoordinate X Xc r (coord j) ω) +
      match i with
        | none => t * gaussianVariance P L
        | some j => t * gaussianCovariance P
            (fun ω => testCircleCoordinate X Xc r (coord j) ω) L) ∂P := by
  have testCircleFamily_with_L_isGaussianProcess : IsGaussianProcess (fun i : Option T => fun ω => match i with | none => L ω | some t => testCircleCoordinate X Xc r (coord t) ω) P := by
    let _ : IsProbabilityMeasure P := hX.1
    obtain ⟨hLmem, fL, hLapprox⟩ := hL
    let Z : ℕ → Option T → Ω → ℝ := fun n i ω =>
      match i with
      | none => X ω (fL n)
      | some t => testCircleCoordinate X Xc r (coord t) ω
    let W : Option T → Ω → ℝ := fun i ω =>
      match i with
      | none => L ω
      | some t => testCircleCoordinate X Xc r (coord t) ω
    have hBaseCut : IsGaussianProcess
        (fun c => testCircleCoordinate X Xc r c) P := by
      convert (circleAverage_tests_isGaussianProcess X Xc hX hXc).comp_right (fun c =>
        Sum.elim (fun x => Sum.inl (x, r)) Sum.inr c) using 1
      funext c ω
      cases c <;> rfl
    have hW : ∀ i, MemLp (W i) 2 P := by
      intro i
      cases i with
      | none => exact hLmem
      | some t =>
          cases hcoord : coord t with
          | inl x =>
              simpa [W, testCircleCoordinate, hcoord] using hXc.2.1 x r
          | inr f =>
              simpa [W, testCircleCoordinate, hcoord] using equatorGFF_test_memLp X hX f
    have hApprox : ∀ i,
        Tendsto (fun n => eLpNorm (fun ω => Z n i ω - W i ω) 2 P)
          atTop (𝓝 0) := by
      intro i
      cases i with
      | none =>
          simpa only [Z, W, (show ∀ n, eLpNorm (fun ω => X ω (fL n) - L ω) 2 P = eLpNorm (fun ω => L ω - X ω (fL n)) 2 P by intro n; exact eLpNorm_sub_comm _ _ _ _)] using hLapprox
      | some t =>
          convert (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) using 1
          · funext n
            simp [Z, W]
    exact isGaussianProcess_of_eLpNorm_sub Z W (by intro n; simpa [Z] using (by convert (hBaseCut.comp_right (fun i => match i with | none => Sum.inr (fL n) | some t => coord t)) using 1; funext i ω; cases i <;> rfl)) hW hApprox
  let Z : Ω → Option T → ℝ := fun ω i =>
    match i with
    | none => L ω
    | some j => testCircleCoordinate X Xc r (coord j) ω
  let a : Option T → ℝ := fun i => if i.isNone then t else 0
  let _ : IsProbabilityMeasure P := hX.1
  have hMeanCoord j :
    (∫ ω, testCircleCoordinate X Xc r (coord j) ω ∂P) = 0 := by
    cases hcoord : coord j with
    | inl x =>
        change (∫ ω, Xc ω x r ∂P) = 0
        exact (circleAverage_isGaussianProcess P X Xc hX hXc).2 x r
    | inr f => exact equatorGFF_test_integral X hX f
  have hCentered : IsCenteredJointlyGaussian P Z := by
    apply centeredJointlyGaussian_of_isGaussianProcess P (fun i ω => Z ω i) ?_ ?_
    · simpa [Z] using (testCircleFamily_with_L_isGaussianProcess)
    · intro i
      cases i with
      | none => exact (show (∫ ω, L ω ∂P) = 0 by obtain ⟨hLmem, fL, hLapprox⟩ := hL; exact integral_eq_zero_of_eLpNorm_sub (fun n => equatorGFF_test_memLp X hX (fL n)) hLmem (fun n => equatorGFF_test_integral X hX (fL n)) (by simpa only [(show ∀ n, eLpNorm (fun ω => X ω (fL n) - L ω) 2 P = eLpNorm (fun ω => L ω - X ω (fL n)) 2 P by intro n; exact eLpNorm_sub_comm _ _ _ _)] using hLapprox))
      | some j => exact hMeanCoord j
  have hExponent (ω : Ω) :
      (∑ i, a i * Z ω i) -
        (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
          (fun ω => Z ω j) * a j) / 2 =
      t * L ω - t ^ 2 / 2 * gaussianVariance P L := by
    simp [a, Z, gaussianVariance, gaussianCovariance]
    ring
  have hShift (ω : Ω) i :
      Z ω i + ∑ j, gaussianCovariance P (fun ω => Z ω i)
        (fun ω => Z ω j) * a j =
      Z ω i + match i with
        | none => t * gaussianVariance P L
        | some j => t * gaussianCovariance P (fun ω => Z ω j) L := by
    cases i with
    | none =>
        simp [a, Z, gaussianVariance, gaussianCovariance]
        ring
    | some k =>
        simp [a, Z, gaussianCovariance]
        ring
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
            (fun ω => Z ω j) * a j) / 2)) * F (Z ω) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun ω => by
            change ENNReal.ofReal (Real.exp (t * L ω - t ^ 2 / 2 * gaussianVariance P L)) *
              F (Z ω) = ENNReal.ofReal (Real.exp
                ((∑ i, a i * Z ω i) -
                  (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
                    (fun ω => Z ω j) * a j) / 2)) * F (Z ω)
            rw [← hExponent ω])
    _ = ∫⁻ ω, F (fun i => Z ω i +
        ∑ j, gaussianCovariance P (fun ω => Z ω i)
          (fun ω => Z ω j) * a j) ∂P := (finite_gaussian_tilt P Z hCentered a F hF)
    _ = _ := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun ω => by
            change F (fun i => Z ω i + ∑ j, gaussianCovariance P
              (fun ω => Z ω i) (fun ω => Z ω j) * a j) =
              F (fun i => (match i with
                | none => L ω
                | some j => testCircleCoordinate X Xc r (coord j) ω) + match i with
                  | none => t * gaussianVariance P L
                  | some j => t * gaussianCovariance P
                    (fun ω => testCircleCoordinate X Xc r (coord j) ω) L)
            apply congrArg F
            funext i
            change Z ω i + ∑ j, gaussianCovariance P (fun ω => Z ω i)
              (fun ω => Z ω j) * a j = Z ω i + match i with
                | none => t * gaussianVariance P L
                | some j => t * gaussianCovariance P (fun ω => Z ω j) L
            exact hShift ω i)

/-- Cameron--Martin transport of the full product-sigma process of test evaluations together with
the fixed-radius circle averages. This is the law-level input before applying a measurable
cutoff-chaos map. -/
theorem equatorGFF_tilted_test_circle_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r t : ℝ)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) :
    Measure.map (fun ω (c : ℂ ⊕ TestFn) => testCircleCoordinate X Xc r c ω)
        (P.withDensity (fun ω => ENNReal.ofReal (Real.exp
          (t * L ω - t ^ 2 / 2 * gaussianVariance P L)))) =
      Measure.map (fun ω c => testCircleCoordinate X Xc r c ω +
        t * gaussianCovariance P (fun ω => testCircleCoordinate X Xc r c ω) L) P := by
  classical
  let eval : Ω → ℂ ⊕ TestFn → ℝ := fun ω c => testCircleCoordinate X Xc r c ω
  let evalShift : Ω → ℂ ⊕ TestFn → ℝ := fun ω c => eval ω c +
    t * gaussianCovariance P (fun ω => eval ω c) L
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp
    (t * L ω - t ^ 2 / 2 * gaussianVariance P L))
  let μ : Measure (ℂ ⊕ TestFn → ℝ) := Measure.map eval (P.withDensity density)
  let ν : Measure (ℂ ⊕ TestFn → ℝ) := Measure.map evalShift P
  have hEval : Measurable eval := by
    rw [measurable_pi_iff]
    intro c
    cases c with
    | inl x =>
        exact (hXc.1 r).comp (measurable_id.prodMk measurable_const)
    | inr f => exact (hX.2 f).1
  have hEvalShift : Measurable evalShift := by
    rw [measurable_pi_iff]
    intro c
    exact (measurable_pi_iff.mp hEval c).add measurable_const
  have hCylinder (s : Finset (ℂ ⊕ TestFn)) (S : Set (∀ i : s, ℝ))
      (hS : MeasurableSet S) :
      μ (MeasureTheory.cylinder s S) = ν (MeasureTheory.cylinder s S) := by
    let coord : s → ℂ ⊕ TestFn := fun i => i.val
    let family : Ω → Option s → ℝ := fun ω i =>
      match i with
      | none => L ω
      | some j => eval ω (coord j)
    let project : (Option s → ℝ) → (∀ i : s, ℝ) := fun y i => y (some i)
    let F : (Option s → ℝ) → ℝ≥0∞ := S.indicator (fun _ => 1) ∘ project
    have hFinite :
        (∫⁻ ω, density ω * F (family ω) ∂P) =
          ∫⁻ ω, F (fun i => family ω i + match i with
            | none => t * gaussianVariance P L
            | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) ∂P := by
      change (∫⁻ ω, ENNReal.ofReal (Real.exp
          (t * L ω - t ^ 2 / 2 * gaussianVariance P L)) *
          F (fun i => match i with
            | none => L ω
            | some j => testCircleCoordinate X Xc r (coord j) ω) ∂P) =
        ∫⁻ ω, F (fun i =>
          (match i with
            | none => L ω
            | some j => testCircleCoordinate X Xc r (coord j) ω) +
          match i with
            | none => t * gaussianVariance P L
            | some j => t * gaussianCovariance P
                (fun ω => testCircleCoordinate X Xc r (coord j) ω) L) ∂P
      exact (equatorGFF_finite_test_circle_tilt P X hX Xc hXc r L hL coord t F (by dsimp [F]; exact (measurable_const.indicator hS).comp (by fun_prop)))
    have hPreEval := (hS.cylinder).preimage hEval
    have hLeft : μ (MeasureTheory.cylinder s S) =
        ∫⁻ ω, density ω * F (family ω) ∂P := by
      dsimp [μ]
      rw [Measure.map_apply hEval (hS.cylinder), withDensity_apply density hPreEval,
        ← lintegral_indicator hPreEval]
      apply lintegral_congr_ae
      exact ae_of_all _ (fun ω => by
        have hproject : project (family ω) = s.restrict (eval ω) := by
          funext i
          simp [project, family, coord, eval]
        by_cases hx : eval ω ∈ MeasureTheory.cylinder s S
        · have hxS : s.restrict (eval ω) ∈ S := by simpa using hx
          simp [F, hproject, hx, hxS]
        · have hxS : s.restrict (eval ω) ∉ S := by simpa using hx
          simp [F, hproject, hx, hxS])
    have hRight : ν (MeasureTheory.cylinder s S) =
        ∫⁻ ω, F (fun i => family ω i + match i with
          | none => t * gaussianVariance P L
          | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) ∂P := by
      dsimp [ν]
      rw [Measure.map_apply hEvalShift (hS.cylinder)]
      calc
        P (evalShift ⁻¹' MeasureTheory.cylinder s S) =
            ∫⁻ ω, (evalShift ⁻¹' MeasureTheory.cylinder s S).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
                symm
                rw [lintegral_indicator_const ((hS.cylinder).preimage hEvalShift) 1]
                simp
        _ = ∫⁻ ω, F (fun i => family ω i + match i with
            | none => t * gaussianVariance P L
            | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by
                have hcoord (i : s) :
                    family ω (some i) + t * gaussianCovariance P
                      (fun ω => eval ω (coord i)) L = evalShift ω (coord i) := by
                  simp [family, evalShift, coord]
                have hproject : project (fun i => family ω i + match i with
                    | none => t * gaussianVariance P L
                    | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) =
                    s.restrict (evalShift ω) := by
                  funext i
                  exact hcoord i
                by_cases hx : evalShift ω ∈ MeasureTheory.cylinder s S
                · have hxS : s.restrict (evalShift ω) ∈ S := by simpa using hx
                  simp [F, hproject, hx, hxS]
                · have hxS : s.restrict (evalShift ω) ∉ S := by simpa using hx
                  simp [F, hproject, hx, hxS])
    exact hLeft.trans (hFinite.trans hRight.symm)
  let C := MeasureTheory.measurableCylinders (fun _ : ℂ ⊕ TestFn => ℝ)
  have hCylinders : ∀ A ∈ C, μ A = ν A := by
    intro A hA
    obtain ⟨s, S, hS, rfl⟩ :=
      (MeasureTheory.mem_measurableCylinders (α := fun _ : ℂ ⊕ TestFn => ℝ) A).mp hA
    exact hCylinder s S hS
  have hνUniv : ν Set.univ = 1 := by
    rw [Measure.map_apply hEvalShift MeasurableSet.univ]
    exact hX.1.measure_univ
  have hμUniv : μ Set.univ = 1 := by rw [hCylinders Set.univ (MeasureTheory.univ_mem_measurableCylinders (fun _ : ℂ ⊕ TestFn => ℝ)), hνUniv]
  have hFiniteμ : IsFiniteMeasure μ := ⟨by rw [hμUniv]; simp⟩
  exact @ext_of_generate_finite (ℂ ⊕ TestFn → ℝ) _ μ ν C
    (by simpa [C] using
      (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℂ ⊕ TestFn => ℝ)).symm)
    MeasureTheory.isPiSystem_measurableCylinders hFiniteμ hCylinders (by rw [hμUniv, hνUniv])

end DOZZ.Proofs
