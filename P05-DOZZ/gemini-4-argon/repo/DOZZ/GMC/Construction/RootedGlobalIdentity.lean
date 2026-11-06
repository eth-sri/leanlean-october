/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedBoundedIdentity
public import DOZZ.GMC.Construction.GMCMeasurableVersion

/-! Whole-plane exhaustion of the measurable rooted identity. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal

namespace DOZZ.Proofs


/-- For every GMC version, the whole-plane rooted identity is reduced to point-insertion
finiteness for reference-almost every root. No measurability assumption on the version remains. -/
theorem rooted_GMC_identity_of_ae_root_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M)
    (hRoot : ∀ᵐ u ∂gmcReferenceMeasure,
      ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)))
    (H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) => H q.1 q.2.1 q.2.2)) :
    (∫⁻ ω, ∫⁻ u, H u (fun f => X ω f) (M ω) ∂M ω ∂P) =
      ∫⁻ u, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f)
        (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure := by
  have rooted_GMC_identity_of_ae_root_finite_measurable (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMmeas : Measurable M) (hRoot : ∀ᵐ u ∂gmcReferenceMeasure, ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω))) (H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞) (hH : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) => H q.1 q.2.1 q.2.2)) : (∫⁻ ω, ∫⁻ u, H u (fun f => X ω f) (M ω) ∂M ω ∂P) = ∫⁻ u, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f) (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure := by
    obtain ⟨Xc, hXc, _⟩ := hM.2
    let B : ℕ → Set ℂ := fun n => Metric.closedBall (0 : ℂ) (n : ℝ)
    have hB n : MeasurableSet (B n) := measurableSet_closedBall
    have hmono : Monotone B := fun i j hij => Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
    have hcover : ⋃ n, B n = Set.univ := Metric.iUnion_closedBall_nat _
    have hmeas n : Measurable (fun ω => ∫⁻ u in B n, H u (fun f => X ω f) (M ω) ∂M ω) := by
      rw [(show (fun ω => ∫⁻ u in B n, H u (fun f => X ω f) (M ω) ∂M ω) = fun ω => ∫⁻ u, (B n).indicator (fun u => H u (fun f => X ω f) (M ω)) u ∂M ω by funext ω; exact (lintegral_indicator (hB n) _).symm)]
      exact measurable_lintegral_finite_family M hMmeas hM.1
        (fun q : Ω × ℂ => (B n).indicator (fun u => H u (fun f => X q.1 f) (M q.1)) q.2)
        ((hH.comp (measurable_snd.prodMk (((measurable_pi_iff.mpr fun f => (hX.2 f).1).comp measurable_fst).prodMk (hMmeas.comp measurable_fst)))).indicator ((hB n).preimage measurable_snd))
    have hleft ω : (∫⁻ u, H u (fun f => X ω f) (M ω) ∂M ω) =
        ⨆ n, ∫⁻ u in B n, H u (fun f => X ω f) (M ω) ∂M ω := by
      simpa only [hcover, Measure.restrict_univ] using
        (setLIntegral_iUnion_of_directed (μ := M ω)
          (fun u => H u (fun f => X ω f) (M ω)) hmono.directed_le)
    simp_rw [hleft]
    rw [lintegral_iSup hmeas, (show (∫⁻ u, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f) (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure) = ⨆ n, ∫⁻ u in B n, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f) (gmcRootedMeasure γ u (M ω)) ∂P ∂gmcReferenceMeasure by simpa only [hcover, Measure.restrict_univ] using (setLIntegral_iUnion_of_directed (μ := gmcReferenceMeasure) (fun u => ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f) (gmcRootedMeasure γ u (M ω)) ∂P) hmono.directed_le))]
    · apply congrArg
      funext n
      exact rooted_GMC_identity_on_bounded_set P X hX γ hγ hγ2 M hM hMmeas
        Xc hXc (B n) (hB n) (n : ℝ) Set.Subset.rfl (ae_restrict_of_ae hRoot) H hH
    · intro i j hij ω
      exact lintegral_mono' (Measure.restrict_mono (hmono hij) le_rfl) le_rfl
  obtain ⟨N, hNmeas, hNfinite, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hN : IsGMCOf P X γ N := by
    obtain ⟨Xc, hXc, hconv⟩ := hM.2
    refine ⟨hNfinite, Xc, hXc, fun f => ?_⟩
    apply TendstoInMeasure.congr_right _ (hconv f)
    filter_upwards [hMN] with ω hω
    rw [hω]
  have hRootN : ∀ᵐ u ∂gmcReferenceMeasure,
      ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (N ω)) := by
    filter_upwards [hRoot] with u hu
    filter_upwards [hu, hMN] with ω hω heq
    rwa [← heq]
  calc
    _ = ∫⁻ ω, ∫⁻ u, H u (fun f => X ω f) (N ω) ∂N ω ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hMN] with ω hω
      rw [hω]
    _ = ∫⁻ u, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f)
        (gmcRootedMeasure γ u (N ω)) ∂P ∂gmcReferenceMeasure :=
      rooted_GMC_identity_of_ae_root_finite_measurable N hN hNmeas hRootN H hH
    _ = _ := by
      apply lintegral_congr
      intro u
      apply lintegral_congr_ae
      filter_upwards [hMN] with ω hω
      rw [hω]

end DOZZ.Proofs
