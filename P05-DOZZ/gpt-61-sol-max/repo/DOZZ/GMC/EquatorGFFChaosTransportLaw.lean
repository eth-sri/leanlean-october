/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.EquatorGFFChaosTransport
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.GMC.Construction.FiniteMeasureTotalize
public import DOZZ.GMC.Moments.ChaosLawFDD
import Mathlib.Tactic

/-! Measurable-law transport for the equator field and its GMC. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private abbrev GMCOpen := {U : Set ℂ // IsOpen U}
private abbrev FiniteComplexMeasure := {μ : Measure ℂ // IsFiniteMeasure μ}
private abbrev GMCTransportOutput := (TestFn → ℝ) × FiniteComplexMeasure

private def gmcOutputCode (q : GMCTransportOutput) :
    (TestFn → ℝ) × (GMCOpen → ℝ≥0∞) :=
  (q.1, fun U => q.2.1 U.1)

/-- Open-set masses of a finite chaos are measurable, by approximation with bounded continuous
distance cutoffs. -/
theorem gmc_open_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (U : Set ℂ) (hU : IsOpen U) :
    AEMeasurable (fun ω => M ω U) P := by
  classical
  rcases hM with ⟨hfinite, Xc, hXc, hconv⟩
  let f  := fun n => gmcOpenApprox U hU n
  have hf : ∀ n, AEMeasurable (fun ω => ∫ x, f n x ∂M ω) P := by
    intro n
    exact gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M ⟨hfinite, Xc, hXc, hconv⟩ (f n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ x, f n x ∂M ω) atTop
      (𝓝 ((M ω U).toReal)) := by
    filter_upwards [] with ω
    exact gmcOpenApprox_integral_tendsto (M ω) U hU
  have hreal : AEMeasurable (fun ω => (M ω U).toReal) P := aemeasurable_of_tendsto_metrizable_ae atTop hf hlim

  have hEq : (fun ω => M ω U) = fun ω => ENNReal.ofReal (M ω U).toReal := by
    simp_all
  rw [hEq]
  exact ENNReal.measurable_ofReal.aemeasurable.comp_aemeasurable hreal

variable {Ω Ω' : Type*} [_inst1 : MeasurableSpace Ω] [_inst2 : MeasurableSpace Ω'] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X') (γ : ℝ)

include Ω Ω' _inst1 _inst2 P X hX P' X' hX' γ in
/-- The open-mass finite-dimensional law extends from `Fin` to arbitrary finite index types. -/
theorem equatorGFF_GMC_open_mass_test_fintype_law
     (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (tests : ι → TestFn) (U : κ → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) P =
      Measure.map (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P' := by
  classical
  let eι  := (Fintype.equivFin ι).symm
  let eκ  := (Fintype.equivFin κ).symm
  let baseX  := fun ω =>
    (fun i => X ω (tests (eι i)), fun j => (M ω (U (eκ j))).toReal)
  let baseY  := fun ω =>
    (fun i => X' ω (tests (eι i)), fun j => (M' ω (U (eκ j))).toReal)
  let reindex : ((Fin (Fintype.card ι) → ℝ) × (Fin (Fintype.card κ) → ℝ)) →
      (ι → ℝ) × (κ → ℝ≥0∞) := fun q =>
        (fun i => q.1 (eι.symm i), fun j => ENNReal.ofReal (q.2 (eκ.symm j)))
  have hbase : Measure.map baseX P = Measure.map baseY P' := by
    have h := equatorGFF_GMC_open_mass_test_vector_law P X hX P' X' hX' γ M hM M' hM'
      (fun i => tests (eι i)) (fun j => U (eκ j)) (fun j => hU (eκ j))
    let toReal : ((Fin (Fintype.card ι) → ℝ) ×
        (Fin (Fintype.card κ) → ℝ≥0∞)) →
        (Fin (Fintype.card ι) → ℝ) × (Fin (Fintype.card κ) → ℝ) := fun q =>
          (q.1, fun j => (q.2 j).toReal)
    have htoReal : Measurable toReal := by fun_prop
    let rawX  := fun ω =>
          (fun i => X ω (tests (eι i)), fun j => M ω (U (eκ j)))
    let rawY  := fun ω =>
          (fun i => X' ω (tests (eι i)), fun j => M' ω (U (eκ j)))
    have hrawX : AEMeasurable rawX P := by
      apply (measurable_pi_iff.mpr fun i => (hX.2 (tests (eι i))).1).aemeasurable.prodMk
      apply AEMeasurable.of_eval
      intro j
      exact gmc_open_mass_aemeasurable P X hX γ M hM (U (eκ j)) (hU (eκ j))
    have hrawY : AEMeasurable rawY P' := by
      apply (measurable_pi_iff.mpr fun i => (hX'.2 (tests (eι i))).1).aemeasurable.prodMk
      apply AEMeasurable.of_eval
      intro j
      exact gmc_open_mass_aemeasurable P' X' hX' γ M' hM' (U (eκ j)) (hU (eκ j))
    calc
      Measure.map baseX P = (Measure.map rawX P).map toReal := (AEMeasurable.map_map_of_aemeasurable htoReal.aemeasurable hrawX).symm
      _ = (Measure.map rawY P').map toReal :=
        congrArg (Measure.map toReal) h
      _ = Measure.map baseY P' := AEMeasurable.map_map_of_aemeasurable htoReal.aemeasurable hrawY
  have hmassX : ∀ ω j, ENNReal.ofReal (M ω (U j)).toReal = M ω (U j) := by
    intro ω j
    let  := hM.1 ω
    simp_all
  have hmassY : ∀ ω j, ENNReal.ofReal (M' ω (U j)).toReal = M' ω (U j) := by
    intro ω j
    let  := hM'.1 ω
    simp_all
  have hbaseXmeas : AEMeasurable baseX P := by
    apply (measurable_pi_iff.mpr fun i => (hX.2 (tests (eι i))).1).aemeasurable.prodMk
    apply AEMeasurable.of_eval
    intro j
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_open_mass_aemeasurable P X hX γ M hM (U (eκ j)) (hU (eκ j)))
  have hbaseYmeas : AEMeasurable baseY P' := by
    apply (measurable_pi_iff.mpr fun i => (hX'.2 (tests (eι i))).1).aemeasurable.prodMk
    apply AEMeasurable.of_eval
    intro j
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_open_mass_aemeasurable P' X' hX' γ M' hM' (U (eκ j)) (hU (eκ j)))
  have hpost : Measurable reindex := by fun_prop
  have hmapX : Measure.map (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) P =
      (Measure.map baseX P).map reindex := by
    have hEq : (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) = reindex ∘ baseX := by
      grind
    rw [hEq]
    exact (AEMeasurable.map_map_of_aemeasurable hpost.aemeasurable hbaseXmeas).symm
  have hmapY : Measure.map (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P' =
      (Measure.map baseY P').map reindex := by
    have hEq : (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) = reindex ∘ baseY := by
      grind
    rw [hEq]
    exact (AEMeasurable.map_map_of_aemeasurable hpost.aemeasurable hbaseYmeas).symm
  rw [hmapX, hbase, hmapY]

include Ω Ω' _inst1 _inst2 P X hX P' X' hX' γ in
/-- The joint law of the distribution-valued field and its finite GMC is determined by the
finite-dimensional laws of test evaluations and open-set masses. -/
theorem equatorGFF_GMC_law_transport
     (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P =
      ∫⁻ ω', H (fun f => X' ω' f) (M' ω') ∂P' := by
  classical
  rcases equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM with
    ⟨N, hNmeas, hNfinite, hNM⟩
  rcases equatorGFF_GMC_measurable_version P' X' hX' γ hγ hγ2 M' hM' with
    ⟨N', hN'meas, hN'finite, hN'M'⟩
  have hN : IsGMCOf P X γ N := by
    rcases hM with ⟨_, Xc, hXc, hconv⟩
    refine ⟨hNfinite, Xc, hXc, fun f => ?_⟩
    have hNM'  := hNM.mono fun _ h => h.symm
    exact tendstoInMeasure_integral_after_ae_measure_change
      (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) M N f hNM' (hconv f)
  have hN' : IsGMCOf P' X' γ N' := by
    rcases hM' with ⟨_, Xc, hXc, hconv⟩
    refine ⟨hN'finite, Xc, hXc, fun f => ?_⟩
    have hN'M''  := hN'M'.mono fun _ h => h.symm
    exact tendstoInMeasure_integral_after_ae_measure_change
      (fun r ω => ∫ x, f x ∂regularizedGMC P' Xc γ r ω) M' N' f hN'M'' (hconv f)
  let Cfield  :=
    measurableCylinders (fun _ : TestFn => ℝ)
  let Cmass  :=
    measurableCylinders (fun _ : GMCOpen => ℝ≥0∞)
  let Crect  :=
    Set.image2 (· ×ˢ ·) Cfield Cmass
  let mTarget : MeasurableSpace ((TestFn → ℝ) × (GMCOpen → ℝ≥0∞)) :=
    MeasurableSpace.pi.prod MeasurableSpace.pi
  let mOutput  :=
    mTarget.comap gmcOutputCode
  let  := mOutput
  let outX : Ω → GMCTransportOutput := fun ω =>
    (fun f => X ω f, ⟨N ω, hNfinite ω⟩)
  let outY : Ω' → GMCTransportOutput := fun ω =>
    (fun f => X' ω f, ⟨N' ω, hN'finite ω⟩)
  have hCfield : MeasurableSpace.generateFrom Cfield = MeasurableSpace.pi := generateFrom_measurableCylinders
  have hCmass : MeasurableSpace.generateFrom Cmass = MeasurableSpace.pi := generateFrom_measurableCylinders
  have hCfieldSpan : IsCountablySpanning Cfield := by
    refine ⟨fun _ => Set.univ, ?_, ?_⟩
    · intro n
      exact univ_mem_measurableCylinders _
    · ext x
      simp
  have hCmassSpan : IsCountablySpanning Cmass := by
    refine ⟨fun _ => Set.univ, ?_, ?_⟩
    · intro n
      exact univ_mem_measurableCylinders _
    · ext x
      simp
  have hCrectGen : MeasurableSpace.generateFrom Crect = mTarget := id (generateFrom_eq_prod hCfield hCmass hCfieldSpan hCmassSpan)
  have hCrectPi : IsPiSystem Crect := id (IsPiSystem.prod isPiSystem_measurableCylinders isPiSystem_measurableCylinders)
  let Coutput  :=
    Set.preimage gmcOutputCode '' Crect
  have hOutputGen : mOutput = MeasurableSpace.generateFrom Coutput := by
    dsimp [mOutput, Coutput]
    rw [← hCrectGen, MeasurableSpace.comap_generateFrom]
  have hOutputPi : IsPiSystem Coutput := by
    change IsPiSystem (Set.preimage gmcOutputCode '' Crect)
    intro A hA B hB hAB
    rcases hA with ⟨A', hA', rfl⟩
    rcases hB with ⟨B', hB', rfl⟩
    refine ⟨A' ∩ B', hCrectPi A' hA' B' hB' ?_, ?_⟩
    · rcases hAB with ⟨q, hq⟩
      exact ⟨gmcOutputCode q, hq⟩
    · rw [← Set.preimage_inter]
  have hcode : Measurable gmcOutputCode := Measurable.of_comap_le le_rfl
  have hcodeX : Measurable (gmcOutputCode ∘ outX) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr fun f => (hX.2 f).1
    · apply measurable_pi_iff.mpr
      intro U
      exact (Measure.measurable_coe U.2.measurableSet).comp hNmeas
  have hcodeY : Measurable (gmcOutputCode ∘ outY) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr fun f => (hX'.2 f).1
    · apply measurable_pi_iff.mpr
      intro U
      exact (Measure.measurable_coe U.2.measurableSet).comp hN'meas
  have houtX : Measurable outX := by
    rw [measurable_iff_comap_le]
    change mOutput.comap outX ≤ ‹MeasurableSpace Ω›
    rw [show mOutput = mTarget.comap gmcOutputCode by rfl,
      MeasurableSpace.comap_comp]
    exact hcodeX.comap_le
  have houtY : Measurable outY := by
    rw [measurable_iff_comap_le]
    change mOutput.comap outY ≤ ‹MeasurableSpace Ω'›
    rw [show mOutput = mTarget.comap gmcOutputCode by rfl,
      MeasurableSpace.comap_comp]
    exact hcodeY.comap_le
  let forget : GMCTransportOutput → (TestFn → ℝ) × Measure ℂ :=
    fun q => (q.1, q.2.1)
  have hOpenGen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom
      {s : Set ℂ | IsOpen s} := by
    aesop
  have hforgetMeasure : Measurable (fun q : GMCTransportOutput => (q.2.1 : Measure ℂ)) := by
    let : ∀ q : GMCTransportOutput, IsFiniteMeasure q.2.1 := fun q => q.2.2
    apply Measurable.measure_of_isPiSystem hOpenGen isPiSystem_isOpen
    · intro s hs
      have heval : Measurable (fun q : GMCTransportOutput =>
          (gmcOutputCode q).2 ⟨s, hs⟩) := by
        have h := (measurable_pi_iff.mp (measurable_snd.comp hcode)) ⟨s, hs⟩
        exact h
      exact heval
    · have heval : Measurable (fun q : GMCTransportOutput =>
          (gmcOutputCode q).2 ⟨Set.univ, isOpen_univ⟩) := by
        have h := (measurable_pi_iff.mp (measurable_snd.comp hcode))
          ⟨Set.univ, isOpen_univ⟩
        exact h
      exact heval
  have hforget : Measurable forget := by
    apply Measurable.prodMk
    · change Measurable (fun q : GMCTransportOutput => (gmcOutputCode q).1)
      exact measurable_fst.comp hcode
    · exact hforgetMeasure
  have hHout : Measurable (fun q : GMCTransportOutput => H q.1 q.2.1) := hH.comp hforget
  have hLaw : Measure.map outX P = Measure.map outY P' := by
    let  := hX.1
    let  := hX'.1
    apply MeasureTheory.ext_of_generate_finite Coutput hOutputGen hOutputPi
    · intro S hS
      rcases hS with ⟨R, hR, rfl⟩
      rcases hR with ⟨A, hA, B, hB, rfl⟩
      rcases (mem_measurableCylinders A).1 hA with ⟨s, As, hAs, rfl⟩
      rcases (mem_measurableCylinders B).1 hB with ⟨t, Bs, hBs, rfl⟩
      let vX : Ω → (s → ℝ) × (t → ℝ≥0∞) := fun ω =>
        (fun i => X ω i.1, fun j => N ω j.1.1)
      let vY : Ω' → (s → ℝ) × (t → ℝ≥0∞) := fun ω =>
        (fun i => X' ω i.1, fun j => N' ω j.1.1)
      have hv  :=
        equatorGFF_GMC_open_mass_test_fintype_law P X hX P' X' hX' γ N hN N' hN'
          (fun i : s => i.1) (fun j : t => j.1.1) (fun j => j.1.2)
      have hvXmeas : AEMeasurable vX P := by
        change AEMeasurable (fun ω =>
          (fun i : s => X ω (i : TestFn), fun j : t => N ω j.1.1)) P
        apply (measurable_pi_iff.mpr fun i : s => (hX.2 (i : TestFn)).1).aemeasurable.prodMk
        apply AEMeasurable.of_eval
        intro j
        exact gmc_open_mass_aemeasurable P X hX γ N hN j.1.1 j.1.2
      have hvYmeas : AEMeasurable vY P' := by
        change AEMeasurable (fun ω =>
          (fun i : s => X' ω (i : TestFn), fun j : t => N' ω j.1.1)) P'
        apply (measurable_pi_iff.mpr fun i : s => (hX'.2 (i : TestFn)).1).aemeasurable.prodMk
        apply AEMeasurable.of_eval
        intro j
        exact gmc_open_mass_aemeasurable P' X' hX' γ N' hN' j.1.1 j.1.2
      have hAB  := hAs.prod hBs
      have hprob : P (vX ⁻¹' (As ×ˢ Bs)) = P' (vY ⁻¹' (As ×ˢ Bs)) := by
        have h := congrArg (fun μ : Measure ((s → ℝ) × (t → ℝ≥0∞)) => μ (As ×ˢ Bs)) hv
        rw [Measure.map_apply_of_aemeasurable hvXmeas hAB,
          Measure.map_apply_of_aemeasurable hvYmeas hAB] at h
        exact h
      have hSmeas : @MeasurableSet GMCTransportOutput mOutput
          (gmcOutputCode ⁻¹' (cylinder s As ×ˢ cylinder t Bs)) := by
        have hCA : cylinder s As ∈ Cfield := by
          simp_all
        have hCB : cylinder t Bs ∈ Cmass := by
          simp_all
        have hSmem : gmcOutputCode ⁻¹' (cylinder s As ×ˢ cylinder t Bs) ∈ Coutput :=
          ⟨cylinder s As ×ˢ cylinder t Bs,
            Set.mem_image2_of_mem hCA hCB, rfl⟩
        rw [hOutputGen]
        exact MeasurableSpace.measurableSet_generateFrom hSmem
      have hpreX : outX ⁻¹' (gmcOutputCode ⁻¹'
          (cylinder s As ×ˢ cylinder t Bs)) = vX ⁻¹' (As ×ˢ Bs) := by
        bound
      have hpreY : outY ⁻¹' (gmcOutputCode ⁻¹'
          (cylinder s As ×ˢ cylinder t Bs)) = vY ⁻¹' (As ×ˢ Bs) := by
        bound
      simp_all
    simp_all
  calc
    ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P =
        ∫⁻ ω, H (fun f => X ω f) (N ω) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [hNM] with ω hω
          rw [hω]
    _ = ∫⁻ q, H q.1 q.2.1 ∂(Measure.map outX P) := by
      symm
      rw [lintegral_map hHout houtX]
    _ = ∫⁻ q, H q.1 q.2.1 ∂(Measure.map outY P') := by rw [hLaw]
    _ = ∫⁻ ω', H (fun f => X' ω' f) (N' ω') ∂P' := by
      rw [lintegral_map hHout houtY]
    _ = ∫⁻ ω', H (fun f => X' ω' f) (M' ω') ∂P' := by
      apply lintegral_congr_ae
      filter_upwards [hN'M'] with ω hω
      rw [hω]


end DOZZ.Proofs
