/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import DOZZ.GMC.Moments.ChaosLawFDD
public import DOZZ.GMC.ConvergenceInMeasure

/-! Passage from cutoff chaos laws to laws of arbitrary limits in measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Equality in law of finite-cutoff approximants passes to limits in measure. Separate
subsequences on the two probability spaces are synchronized by taking a further subsequence of the
first one; bounded continuous tests then pass by dominated convergence. -/
theorem map_eq_of_seq_map_eq_of_tendstoInMeasure
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [PseudoEMetricSpace E] [BorelSpace E]
    [SecondCountableTopology E] [HasOuterApproxClosed E]
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (f : ℕ → Ω → E) (g : ℕ → Ω' → E) (fLimit : Ω → E) (gLimit : Ω' → E)
    (hf : ∀ n, AEMeasurable (f n) P) (hg : ∀ n, AEMeasurable (g n) P')
    (hflimit : AEMeasurable fLimit P) (hglimit : AEMeasurable gLimit P')
    (hmap : ∀ n, Measure.map (f n) P = Measure.map (g n) P')
    (hfconv : TendstoInMeasure P f atTop fLimit)
    (hgconv : TendstoInMeasure P' g atTop gLimit) :
    Measure.map fLimit P = Measure.map gLimit P' := by
  have htest : ∀ φ : BoundedContinuousFunction E ℝ,
      (∫ ω, φ (fLimit ω) ∂P) = ∫ ω, φ (gLimit ω) ∂P' := by
    intro φ
    obtain ⟨ns, hns, hfae⟩ := hfconv.exists_seq_tendsto_ae
    have hgsub  :=
      hgconv.comp hns.tendsto_atTop
    obtain ⟨ms, hms, hgae⟩ := hgsub.exists_seq_tendsto_ae
    let fs  := fun n => f (ns (ms n))
    let gs  := fun n => g (ns (ms n))
    have hfs : ∀ n, AEMeasurable (fs n) P := fun n => hf _
    have hgs : ∀ n, AEMeasurable (gs n) P' := fun n => hg _
    have hmaps : ∀ n, Measure.map (fs n) P = Measure.map (gs n) P' := by
      intro n
      exact hmap (ns (ms n))
    have hfseq : ∀ᵐ ω ∂P, Tendsto (fun n => fs n ω) atTop (𝓝 (fLimit ω)) := by
      filter_upwards [hfae] with ω hω
      have hcomp := hω.comp hms.tendsto_atTop
      assumption
    apply integral_bcf_eq_of_map_eq_of_ae_tendsto <;> assumption
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  exact fun φ =>
    Trans.trans
      (Trans.trans
        (integral_map hflimit
          (Measurable.aestronglyMeasurable (Continuous.measurable (BoundedContinuousFunction.continuous φ))))
        (htest φ))
      (Eq.symm
        (integral_map hglimit
          (Measurable.aestronglyMeasurable (Continuous.measurable (BoundedContinuousFunction.continuous φ)))))

/-- Finite-cutoff equality of all test-vector laws passes to arbitrary chaos limits specified by
test-integral convergence in measure. This is the limit transfer needed for `IsGMCOf`; it does not
construct a preferred GMC version. -/
theorem gmc_limit_test_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {m : ℕ} (cutoffX : ℕ → Ω → Fin m → ℝ)
    (cutoffY : ℕ → Ω' → Fin m → ℝ) (limitX : Ω → Fin m → ℝ)
    (limitY : Ω' → Fin m → ℝ)
    (hcutoffX : ∀ n, AEMeasurable (cutoffX n) P)
    (hcutoffY : ∀ n, AEMeasurable (cutoffY n) P')
    (hlimitX : AEMeasurable limitX P) (hlimitY : AEMeasurable limitY P')
    (hcutoffLaw : ∀ n, Measure.map (cutoffX n) P = Measure.map (cutoffY n) P')
    (hconvX : ∀ j, TendstoInMeasure P (fun n ω => cutoffX n ω j) atTop
      (fun ω => limitX ω j))
    (hconvY : ∀ j, TendstoInMeasure P' (fun n ω => cutoffY n ω j) atTop
      (fun ω => limitY ω j)) :
    Measure.map limitX P = Measure.map limitY P' := map_eq_of_seq_map_eq_of_tendstoInMeasure cutoffX cutoffY limitX limitY
    hcutoffX hcutoffY hlimitX hlimitY hcutoffLaw
    (tendstoInMeasure_pi_finite P cutoffX limitX hconvX)
    (tendstoInMeasure_pi_finite P' cutoffY limitY hconvY)

/-- Appending a fixed random coordinate preserves convergence in measure exactly. -/
theorem tendstoInMeasure_pair_with_fixed
    {Ω E F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : Measure Ω) (V : Ω → E) (f : ℕ → Ω → F) (g : Ω → F)
    (h : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n ω => (V ω, f n ω)) atTop (fun ω => (V ω, g ω)) := by
  rw [tendstoInMeasure_iff_norm] at h ⊢
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
    max_eq_right (norm_nonneg _)] using h

section
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Passing finite chaos test laws to the limit preserves their coupling to fixed
auxiliary coordinates on each probability space. -/
theorem gmc_limit_joint_test_vector_law
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {E κ : Type*} [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [Fintype κ] (V : Ω → E) (V' : Ω' → E)
    (hV : AEMeasurable V P) (hV' : AEMeasurable V' P')
    (cutoffX : ℕ → Ω → κ → ℝ) (cutoffY : ℕ → Ω' → κ → ℝ)
    (limitX : Ω → κ → ℝ) (limitY : Ω' → κ → ℝ)
    (hcutoffX : ∀ n, AEMeasurable (cutoffX n) P)
    (hcutoffY : ∀ n, AEMeasurable (cutoffY n) P')
    (hlimitX : AEMeasurable limitX P) (hlimitY : AEMeasurable limitY P')
    (hlaw : ∀ n, P.map (fun ω => (V ω, cutoffX n ω)) =
      P'.map (fun ω => (V' ω, cutoffY n ω)))
    (hconvX : ∀ j, TendstoInMeasure P (fun n ω => cutoffX n ω j) atTop (fun ω => limitX ω j))
    (hconvY : ∀ j, TendstoInMeasure P' (fun n ω => cutoffY n ω j) atTop (fun ω => limitY ω j)) :
    P.map (fun ω => (V ω, limitX ω)) = P'.map (fun ω => (V' ω, limitY ω)) := by
  apply map_eq_of_seq_map_eq_of_tendstoInMeasure
    (fun n ω => (V ω, cutoffX n ω)) (fun n ω => (V' ω, cutoffY n ω))
    (fun ω => (V ω, limitX ω)) (fun ω => (V' ω, limitY ω))
  · exact fun n => hV.prodMk (hcutoffX n)
  · exact fun n => hV'.prodMk (hcutoffY n)
  · exact hV.prodMk hlimitX
  · exact hV'.prodMk hlimitY
  · exact hlaw
  · exact tendstoInMeasure_pair_with_fixed P V cutoffX limitX
      (tendstoInMeasure_pi_finite P cutoffX limitX hconvX)
  · exact tendstoInMeasure_pair_with_fixed P' V' cutoffY limitY
      (tendstoInMeasure_pi_finite P' cutoffY limitY hconvY)

end

end DOZZ.Proofs
