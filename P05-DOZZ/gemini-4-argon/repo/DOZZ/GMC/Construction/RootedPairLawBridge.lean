/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedContinuousCutoff
public import DOZZ.GMC.Construction.RootedCutoffTransport
public import Mathlib.MeasureTheory.Constructions.Projective

/-! A law bridge from test evaluations and a measurable continuous circle profile to their
joint product law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MeasurableSpace
open scoped ENNReal

namespace DOZZ.Proofs

private theorem withDensity_withDensity_eq_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity f).withDensity g = μ.withDensity (f * g) := by
  ext s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs,
    setLIntegral_withDensity_eq_setLIntegral_mul μ hf hg hs]

abbrev RootedPair := (TestFn → ℝ) × C(ℂ, ℝ)

def rootedPairPath (q : RootedPair) : ℂ ⊕ TestFn → ℝ := fun i =>
  match i with
  | Sum.inl x => q.2 x
  | Sum.inr f => q.1 f

def continuousCircleProfileShift {Ω : Type*} (Z : Ω → C(ℂ, ℝ))
    (v : ℂ → ℝ) (hv : Continuous v) (t : ℝ) : Ω → C(ℂ, ℝ) := fun ω =>
  ⟨fun x => Z ω x + t * v x, (Z ω).continuous.add (continuous_const.mul hv)⟩

/-- The cutoff chaos associated with a continuous circle profile and a fixed variance function. -/
noncomputable def continuousCircleCutoffMeasure (V : ℂ → ℝ) (γ : ℝ)
    (F : C(ℂ, ℝ)) : Measure ℂ :=
  volume.withDensity (fun x => ENNReal.ofReal
    (Real.exp (γ * F x - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)))


/-- Fubini turns the coordinatewise-a.e. agreement of a continuous modification with the circle
witness into equality of their cutoff measures almost surely. -/
theorem continuousCircleCutoffMeasure_ae_eq_regularizedGMC
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (Z : Ω → C(ℂ, ℝ)) (hZ : Measurable Z)
    (hZae : ∀ x, (fun ω => Z ω x) =ᵐ[P] fun ω => Xc ω x r) :
    (fun ω => continuousCircleCutoffMeasure
      (fun x => ∫ ω', Xc ω' x r ^ 2 ∂P) γ (Z ω)) =ᵐ[P]
      fun ω => regularizedGMC P Xc γ r ω := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  let profileDensity : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Z p.1 p.2 - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  let rawDensity : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  have hProfileEval : Measurable (fun p : Ω × ℂ => Z p.1 p.2) := by
    exact (continuous_eval.measurable).comp (Measurable.prodMk (hZ.comp measurable_fst) measurable_snd)
  have hEqSet := measurableSet_eq_fun hProfileEval (hXc.1 r)
  have hCurr := (Measure.ae_ae_comm hEqSet).2 (ae_of_all volume hZae)
  filter_upwards [(Measure.ae_ae_of_ae_prod (show profileDensity =ᵐ[P.prod volume] rawDensity by filter_upwards [((Measure.ae_prod_iff_ae_ae hEqSet).2 hCurr)] with p hp; simp [profileDensity, rawDensity, V, hp]))] with ω hω
  simpa [continuousCircleCutoffMeasure, regularizedGMC, V,
    profileDensity, rawDensity] using (withDensity_congr_ae hω)

/-- A continuous profile shift multiplies its cutoff measure by the exponential of the shifted
profile. The equality is stated against the original circle witness and uses Fubini for the
coordinatewise-a.e. profile agreement. -/
theorem continuousCircleCutoffMeasure_shift_ae_eq_regularizedGMC_withDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r t : ℝ) (Z : Ω → C(ℂ, ℝ)) (hZ : Measurable Z)
    (hZae : ∀ x, (fun ω => Z ω x) =ᵐ[P] fun ω => Xc ω x r)
    (v : ℂ → ℝ) (hv : Continuous v) :
    (fun ω => continuousCircleCutoffMeasure
      (fun x => ∫ ω', Xc ω' x r ^ 2 ∂P) γ
      (continuousCircleProfileShift Z v hv t ω)) =ᵐ[P]
      fun ω => (regularizedGMC P Xc γ r ω).withDensity
        (fun x => ENNReal.ofReal (Real.exp (γ * t * v x))) := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  let Zshift := continuousCircleProfileShift Z v hv t
  let shiftDensity : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Zshift p.1 p.2 - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  let rawDensity : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  let insertWeight : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (γ * t * v x))
  have hProfileEval : Measurable (fun p : Ω × ℂ => Z p.1 p.2) := (continuous_eval.measurable).comp
      (Measurable.prodMk (hZ.comp measurable_fst) measurable_snd)
  have hRawEval := hXc.1 r
  have hEqSet := measurableSet_eq_fun hProfileEval hRawEval
  have hEach := ae_of_all volume hZae
  have hDensityProd : shiftDensity =ᵐ[P.prod volume]
      fun p => rawDensity p * insertWeight p.2 := by
    filter_upwards [((Measure.ae_prod_iff_ae_ae hEqSet).2 ((Measure.ae_ae_comm hEqSet).2 hEach))] with p hp
    have hExp : Real.exp (γ * Zshift p.1 p.2 - γ ^ 2 / 2 * V p.2) =
        Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) *
          Real.exp (γ * t * v p.2) := by
      have hlinear : γ * Zshift p.1 p.2 - γ ^ 2 / 2 * V p.2 =
          (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) + γ * t * v p.2 := by
        rw [show Zshift p.1 p.2 = Z p.1 p.2 + t * v p.2 by
          rfl, hp]
        ring
      rw [hlinear, Real.exp_add]
    dsimp [shiftDensity, rawDensity, insertWeight]
    rw [hExp]
    calc
      ENNReal.ofReal (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) *
          Real.exp (γ * t * v p.2) * normPlus p.2 ^ (-4 : ℝ)) =
        ENNReal.ofReal ((Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) *
          normPlus p.2 ^ (-4 : ℝ)) * Real.exp (γ * t * v p.2)) := by
            congr 1
            ring
      _ = ENNReal.ofReal (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) *
          normPlus p.2 ^ (-4 : ℝ)) * ENNReal.ofReal (Real.exp (γ * t * v p.2)) :=
        ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (le_of_lt (by unfold normPlus; positivity)) _))
  have hV : Measurable V := by
    let q : ℂ → Ω → ℝ := fun x ω' => Xc ω' x r ^ 2
    have hq : Measurable (Function.uncurry q) := by
      have hbase := (hXc.1 r).comp measurable_swap
      change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
      rw [(show (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) = fun p => Xc p.2 p.1 r * Xc p.2 p.1 r by funext p; ring)]
      exact hbase.mul hbase
    change Measurable (fun x => ∫ ω', q x ω' ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  have hrawMeas (ω : Ω) : Measurable (fun x : ℂ => rawDensity (ω, x)) := by
    have : Measurable (fun x : ℂ => Xc ω x r) :=
      (hXc.1 r).comp (Measurable.prodMk measurable_const measurable_id)
    have := hV
    have : Measurable (fun x : ℂ => normPlus x) := by
      unfold normPlus
      exact measurable_const.max measurable_norm
    dsimp [rawDensity]
    fun_prop
  filter_upwards [(Measure.ae_ae_of_ae_prod hDensityProd)] with ω hω
  rw [continuousCircleCutoffMeasure, (show regularizedGMC P Xc γ r ω = volume.withDensity (fun x => rawDensity (ω, x)) by simp [regularizedGMC, rawDensity, V]), (withDensity_withDensity_eq_mul volume (fun x => rawDensity (ω, x)) insertWeight (hrawMeas ω) (by dsimp [insertWeight]; fun_prop))]
  exact (withDensity_congr_ae hω)






/-- Applying the continuous-profile law to the cutoff-measure map transports every measurable
nonnegative observable of the test field and cutoff chaos. The cutoff is represented using the
continuous modification; the preceding pair-law theorem allows its coordinates to agree only
almost surely, separately at each spatial point. -/
theorem equatorGFF_tilted_test_continuousCircle_cutoff_lintegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (r t γ : ℝ) L (hL : IsGaussianL2Limit P X L)
    (Z : Ω → C(ℂ, ℝ)) (hZ : Measurable Z)
    (hZae : ∀ x, (fun ω => Z ω x) =ᵐ[P] fun ω => Xc ω x r)
    (hcovCont : Continuous (fun x =>
      gaussianCovariance P (fun ω => Xc ω x r) L))
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, H (fun f => X ω f)
      (continuousCircleCutoffMeasure (fun x => ∫ ω', Xc ω' x r ^ 2 ∂P) γ (Z ω))
      ∂P.withDensity (fun ω => ENNReal.ofReal (Real.exp
        (t * L ω - t ^ 2 / 2 * gaussianVariance P L)))) =
    ∫⁻ ω, H (fun f => X ω f + t * gaussianCovariance P (fun ω' => X ω' f) L)
      (continuousCircleCutoffMeasure (fun x => ∫ ω', Xc ω' x r ^ 2 ∂P) γ
        (continuousCircleProfileShift Z
          (fun x => gaussianCovariance P (fun ω' => Xc ω' x r) L) hcovCont t ω)) ∂P := by
  classical
  have equatorGFF_tilted_test_continuousCircle_pair_law : Measure.map (fun ω => ((fun f => X ω f), Z ω)) (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (t * L ω - t ^ 2 / 2 * gaussianVariance P L))) : Measure Ω) = Measure.map (fun ω => ((fun f => X ω f + t * gaussianCovariance P (fun ω' => X ω' f) L), continuousCircleProfileShift Z (fun x => gaussianCovariance P (fun ω' => Xc ω' x r) L) hcovCont t ω)) P := by
    classical
    have rootedPair_cylinders_piSystem : IsPiSystem (Set.image (fun s : Set (ℂ ⊕ TestFn → ℝ) => rootedPairPath ⁻¹' s) (MeasureTheory.measurableCylinders (fun _ : ℂ ⊕ TestFn => ℝ))) := by
      rintro A ⟨A', hA', rfl⟩ B ⟨B', hB', rfl⟩ hne
      have hne' : (A' ∩ B').Nonempty := by
        obtain ⟨q, hq⟩ := hne
        change rootedPairPath q ∈ A' ∧ rootedPairPath q ∈ B' at hq
        exact ⟨rootedPairPath q, hq⟩
      refine ⟨A' ∩ B',
        (MeasureTheory.isPiSystem_measurableCylinders
          (α := fun _ => ℝ)) A' hA' B' hB' hne', ?_⟩
      change rootedPairPath ⁻¹' (A' ∩ B') =
        rootedPairPath ⁻¹' A' ∩ rootedPairPath ⁻¹' B'
      rw [Set.preimage_inter]
    have rootedPair_cylinder_generates : MeasurableSpace.generateFrom (Set.image (fun s : Set (ℂ ⊕ TestFn → ℝ) => rootedPairPath ⁻¹' s) (MeasureTheory.measurableCylinders (fun _ : ℂ ⊕ TestFn => ℝ))) = (inferInstance : MeasurableSpace RootedPair) := by
      have rootedPairPath_measurableSpace_comap : MeasurableSpace.comap rootedPairPath MeasurableSpace.pi = MeasurableSpace.prod (inferInstance : MeasurableSpace (TestFn → ℝ)) (borel C(ℂ, ℝ)) := by
        rw [MeasurableSpace.comap_process_pi, iSup_sum]
        change _ = MeasurableSpace.comap Prod.fst
            (inferInstance : MeasurableSpace (TestFn → ℝ)) ⊔
          MeasurableSpace.comap Prod.snd (borel C(ℂ, ℝ))
        simp only [rootedPairPath]
        rw [← (inferInstance : BorelSpace C(ℂ, ℝ)).measurable_eq, MeasurableSpace.pi, ContinuousMap.measurableSpace_eq_iSup_comap_eval]
        simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
          Function.comp_def]
        rw [sup_comm]
      rw [← MeasurableSpace.comap_generateFrom,
        MeasureTheory.generateFrom_measurableCylinders,
        rootedPairPath_measurableSpace_comap]
      rfl
    have measurable_rootedPairPath : Measurable rootedPairPath := by
      rw [measurable_pi_iff]
      intro i
      cases i with
      | inl x => exact (ContinuousMap.measurable_eval x).comp measurable_snd
      | inr f => exact (measurable_pi_apply f).comp measurable_fst
    let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp
      (t * L ω - t ^ 2 / 2 * gaussianVariance P L))
    let field : Ω → TestFn → ℝ := fun ω f => X ω f
    let covField : TestFn → ℝ := fun f =>
      gaussianCovariance P (fun ω => X ω f) L
    let covCircle : ℂ → ℝ := fun x =>
      gaussianCovariance P (fun ω => Xc ω x r) L
    let Zshift := continuousCircleProfileShift Z covCircle hcovCont t
    let fieldShift : Ω → TestFn → ℝ := fun ω f => X ω f + t * covField f
    let pairLeft : Ω → RootedPair := fun ω => (field ω, Z ω)
    let pairRight : Ω → RootedPair := fun ω => (fieldShift ω, Zshift ω)
    let evalOrig : Ω → ℂ ⊕ TestFn → ℝ := fun ω c =>
      testCircleCoordinate X Xc r c ω
    let evalShift : Ω → ℂ ⊕ TestFn → ℝ := fun ω c => evalOrig ω c +
      t * gaussianCovariance P (fun ω' => evalOrig ω' c) L
    let evalProfile : Ω → ℂ ⊕ TestFn → ℝ := fun ω => rootedPairPath (pairLeft ω)
    let evalProfileShift : Ω → ℂ ⊕ TestFn → ℝ := fun ω => rootedPairPath (pairRight ω)
    have hfieldShift : Measurable fieldShift := by
      rw [measurable_pi_iff]
      intro f
      exact ((hX.2 f).1).add measurable_const
    have hZshift : Measurable Zshift := by
      apply ContinuousMap.measurable_iff_eval.mpr
      intro x
      exact ((ContinuousMap.measurable_eval x).comp hZ).add measurable_const
    have hpairLeft := Measurable.prodMk (show Measurable field by rw [measurable_pi_iff]; exact fun f => (hX.2 f).1) hZ
    have hpairRight := Measurable.prodMk hfieldShift hZshift
    have hEvalOrig : Measurable evalOrig := by
      rw [measurable_pi_iff]
      intro c
      cases c with
      | inl x => exact (hXc.1 r).comp (measurable_id.prodMk measurable_const)
      | inr f => exact (hX.2 f).1
    have hEvalShift : Measurable evalShift := by
      rw [measurable_pi_iff]
      intro c
      exact ((measurable_pi_iff.mp hEvalOrig c).add measurable_const)
    have hLaw : Measure.map evalOrig (P.withDensity density) = Measure.map evalShift P := by
      simpa [evalOrig, evalShift, density] using
        equatorGFF_tilted_test_circle_law P X hX Xc hXc r t L hL
    let μ : Measure RootedPair := Measure.map pairLeft (P.withDensity density)
    let ν : Measure RootedPair := Measure.map pairRight P
    have hCylinder (s : Finset (ℂ ⊕ TestFn)) (S : Set (∀ i : s, ℝ))
        (hS : MeasurableSet S) :
        μ (rootedPairPath ⁻¹' MeasureTheory.cylinder s S) =
          ν (rootedPairPath ⁻¹' MeasureTheory.cylinder s S) := by
      have hA := (hS.cylinder).preimage measurable_rootedPairPath
      have hVectorLeft :
          (fun (ω : Ω) => fun (i : s) => evalProfile ω i) =ᵐ[P]
            fun (ω : Ω) => fun (i : s) => evalOrig ω i := by
        change ∀ᵐ ω ∂P,
          (fun i : s => evalProfile ω i) = (fun i : s => evalOrig ω i)
        simp only [funext_iff]
        rw [ae_all_iff]
        intro i
        cases i with
        | mk i hi =>
            cases i with
            | inl x =>
                change (fun ω => Z ω x) =ᵐ[P] fun ω => Xc ω x r
                exact hZae x
            | inr f => exact ae_of_all P (fun _ => rfl)
      have hVectorRight :
          (fun (ω : Ω) => fun (i : s) => evalProfileShift ω i) =ᵐ[P]
            fun (ω : Ω) => fun (i : s) => evalShift ω i := by
        change ∀ᵐ ω ∂P,
          (fun i : s => evalProfileShift ω i) = (fun i : s => evalShift ω i)
        simp only [funext_iff]
        rw [ae_all_iff]
        intro i
        cases i with
        | mk i hi =>
            cases i with
            | inl x =>
                filter_upwards [hZae x] with ω hω
                change Z ω x + t * covCircle x = Xc ω x r + t * covCircle x
                rw [hω]
            | inr f =>
                exact ae_of_all P (fun ω => by
                  simp [evalProfileShift, pairRight, Zshift, fieldShift, covField,
                    rootedPairPath, evalShift, evalOrig, testCircleCoordinate])
      calc
        μ (rootedPairPath ⁻¹' MeasureTheory.cylinder s S) =
            (P.withDensity density) (evalProfile ⁻¹' MeasureTheory.cylinder s S) := by
              dsimp [μ]
              rw [Measure.map_apply hpairLeft hA]
              rfl
        _ = (P.withDensity density) (evalOrig ⁻¹' MeasureTheory.cylinder s S) :=
              measure_congr ((withDensity_absolutelyContinuous P density).ae_le (by filter_upwards [hVectorLeft] with ω hω; simp only [Set.mem_preimage, MeasureTheory.mem_cylinder]; rw [(show s.restrict (evalProfile ω) = s.restrict (evalOrig ω) by funext i; exact congrFun hω i)]))
        _ = P (evalShift ⁻¹' MeasureTheory.cylinder s S) := by
              have h := congrArg (fun m : Measure (ℂ ⊕ TestFn → ℝ) =>
                m (MeasureTheory.cylinder s S)) hLaw
              rw [Measure.map_apply hEvalOrig hS.cylinder,
                Measure.map_apply hEvalShift hS.cylinder] at h
              exact h
        _ = P (evalProfileShift ⁻¹' MeasureTheory.cylinder s S) :=
              (measure_congr (by filter_upwards [hVectorRight] with ω hω; simp only [Set.mem_preimage, MeasureTheory.mem_cylinder]; rw [(show s.restrict (evalProfileShift ω) = s.restrict (evalShift ω) by funext i; exact congrFun hω i)])).symm
        _ = ν (rootedPairPath ⁻¹' MeasureTheory.cylinder s S) := by
              dsimp [ν]
              rw [Measure.map_apply hpairRight hA]
              rfl
    have hνUniv : ν Set.univ = 1 := by
      dsimp [ν]
      rw [Measure.map_apply hpairRight MeasurableSet.univ]
      exact hX.1.measure_univ
    have hμUniv : μ Set.univ = 1 := by
      have hMass : (P.withDensity density) Set.univ = P Set.univ := by
        have h := congrArg (fun m : Measure (ℂ ⊕ TestFn → ℝ) => m Set.univ) hLaw
        rw [Measure.map_apply hEvalOrig MeasurableSet.univ,
          Measure.map_apply hEvalShift MeasurableSet.univ] at h
        exact h
      calc
        μ Set.univ = (P.withDensity density) (pairLeft ⁻¹' Set.univ) := by
          change Measure.map pairLeft (P.withDensity density) Set.univ = _
          exact Measure.map_apply hpairLeft MeasurableSet.univ
        _ = (P.withDensity density) Set.univ :=
          congrArg (fun A : Set Ω => (P.withDensity density) A) Set.preimage_univ
        _ = P Set.univ := hMass
        _ = 1 := hX.1.measure_univ
    have hFiniteμ : IsFiniteMeasure μ := ⟨by rw [hμUniv]; simp⟩
    exact @ext_of_generate_finite RootedPair _ μ ν (Set.image (fun A => rootedPairPath ⁻¹' A) (MeasureTheory.measurableCylinders (fun _ : ℂ ⊕ TestFn => ℝ)))
      rootedPair_cylinder_generates.symm
      rootedPair_cylinders_piSystem hFiniteμ (by intro A hA; obtain ⟨B, hB, rfl⟩ := hA; obtain ⟨s, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders B).mp hB; exact hCylinder s S hS) (by rw [hμUniv, hνUniv])
  let _ : IsProbabilityMeasure P := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  have hV : Measurable V := by
    let q : ℂ → Ω → ℝ := fun x ω' => Xc ω' x r ^ 2
    have hq : Measurable (Function.uncurry q) := by
      have hbase := (hXc.1 r).comp measurable_swap
      change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
      rw [(show (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) = fun p => Xc p.2 p.1 r * Xc p.2 p.1 r by funext p; ring)]
      exact hbase.mul hbase
    change Measurable (fun x => ∫ ω', q x ω' ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  let cutoff : C(ℂ, ℝ) → Measure ℂ := continuousCircleCutoffMeasure V γ
  have hObs : Measurable (fun q : RootedPair => H q.1 (cutoff q.2)) :=
    hH.comp (Measurable.prodMk measurable_fst (((fun V hV γ => continuousCircleCutoffMeasure_measurable V hV γ) V hV γ).comp measurable_snd))
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp
    (t * L ω - t ^ 2 / 2 * gaussianVariance P L))
  let field : Ω → TestFn → ℝ := fun ω f => X ω f
  let covField : TestFn → ℝ := fun f =>
    gaussianCovariance P (fun ω => X ω f) L
  let covCircle : ℂ → ℝ := fun x =>
    gaussianCovariance P (fun ω => Xc ω x r) L
  let Zshift : Ω → C(ℂ, ℝ) := continuousCircleProfileShift Z covCircle hcovCont t
  let fieldShift : Ω → TestFn → ℝ := fun ω f => X ω f + t * covField f
  let pairLeft : Ω → RootedPair := fun ω => (field ω, Z ω)
  let pairRight : Ω → RootedPair := fun ω => (fieldShift ω, Zshift ω)
  have hpairLeft : Measurable pairLeft := by
    exact Measurable.prodMk (by
      rw [measurable_pi_iff]
      exact fun f => (hX.2 f).1) hZ
  have hpairRight : Measurable pairRight := by
    have hZshift : Measurable Zshift := by
      apply ContinuousMap.measurable_iff_eval.mpr
      intro x
      exact ((ContinuousMap.measurable_eval x).comp hZ).add measurable_const
    exact Measurable.prodMk (by rw [measurable_pi_iff]; intro f; exact ((hX.2 f).1).add measurable_const) hZshift
  have hIntegral := congrArg (fun μ : Measure RootedPair =>
    ∫⁻ q, H q.1 (cutoff q.2) ∂μ) (equatorGFF_tilted_test_continuousCircle_pair_law)
  rw [lintegral_map hObs hpairLeft, lintegral_map hObs hpairRight] at hIntegral
  simpa [field, fieldShift, covField, cutoff, V, pairLeft, pairRight, Zshift,
    density, covCircle, continuousCircleProfileShift] using hIntegral

end DOZZ.Proofs
