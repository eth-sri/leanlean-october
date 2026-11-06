module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierDomination
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierEvolved
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierMarginal

/-!
# The Fourier marginal has a density `k^ξ`, dominated by the shifted occupation density

* `ae_enorm_le_of_setIntegral_enorm_le`: `‖∫_E k‖ ≤ ∫_E G` for all `E` gives `‖k‖ ≤ G` a.e.
* `slab_fourier_ae_bound` (Lemma 5.1): any density `k` of the complex
  measure `E ↦ ∫_{(τ,w)∈E, T<τ<2T} e^{-iξ·z} dΓ` on `(T,2T) × ℝ^d` satisfies
  `‖k(τ,w)‖ ≤ g^ξ(τ - T/2, w)` a.e., where `g^ξ` is the occupation density of `|η_T^ξ|`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

/- A density `k` with `‖∫_E k‖ ≤ ∫_E ĝ` for all measurable `E` satisfies `‖k‖ ≤ ĝ` a.e. -/
theorem ae_enorm_le_of_setIntegral_enorm_le {α : Type*} [MeasurableSpace α] (m : Measure α)
    [SigmaFinite m] (k : α → ℂ) (hk : Integrable k m) (G : α → ℝ≥0∞)
    (h : ∀ E, MeasurableSet E → ‖∫ y in E, k y ∂m‖ₑ ≤ ∫⁻ y in E, G y ∂m) :
    ∀ᵐ y ∂m, ‖k y‖ₑ ≤ G y := by
  have hv : (m.withDensityᵥ k).variation = m.withDensity (fun y => ‖k y‖ₑ) :=
    Measure.variation_withDensityᵥ hk
  have hle : (m.withDensityᵥ k).variation ≤ m.withDensity G := by
    refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
    rw [withDensityᵥ_apply hk hE, withDensity_apply _ hE]
    exact h E hE
  rw [hv] at hle
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hk.aestronglyMeasurable.enorm
    (fun E hE _ => ?_)
  have := Measure.le_iff.1 hle E hE
  rwa [withDensity_apply _ hE, withDensity_apply _ hE] at this


variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))

/- **Lemma 5.1: pointwise domination of any density `k^ξ`.**
`gξ` is the occupation density of `|η_T^ξ|` (start time `σ₀ + T/2`, horizon `3T/2`); `k` is any
integrable density of the Fourier marginal. -/
theorem slab_fourier_ae_bound
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ ) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T } (hT : 0 < T) (ξ : PDE.Vec d) (gξ : ℝ × PDE.Vec d → ℝ)
    (hgξ : SlabOccupationDensity K (σ₀ + T / 2) (3 * T / 2)
      (halfMeasure K σ₀ T hT.le μ ξ).variation gξ)
    (hint : Integrable gξ (volume.restrict (Ioo (0 : ℝ) (3 * T / 2) ×ˢ (univ : Set (PDE.Vec d)))))
    (k : SlabBase d → ℂ) (hk : Integrable k (slabBase d T))
    (hkE : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) :
    ∀ᵐ y ∂slabBase d T, ‖k y‖ₑ ≤ ENNReal.ofReal (gξ (slabShift d (T / 2) y)) := by
  have hρfin : IsFiniteMeasure (halfMeasure K σ₀ T hT.le μ ξ).variation :=
    evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
  refine ae_enorm_le_of_setIntegral_enorm_le (slabBase d T) k hk _ (fun E hE => ?_)
  rw [hkE E hE]
  have _h_xinl_0 : ‖∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}, greenPhase d ξ p ∂Γ‖ₑ ≤ ∫⁻ v, (∫⁻ τ in slabTimeSet T, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v {w | (τ, w) ∈ E} ∂elapsedVolume ⊤) ∂(halfMeasure K σ₀ T hT.le μ ξ).variation := by
    set ρ := (halfMeasure K σ₀ T hT.le μ ξ).variation with hρ
    have hρfin : IsFiniteMeasure ρ :=
      evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
    have hSEm := measurableSet_slabPreimage T hE
    set SE : Set (GreenCarrier d) := {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} with hSE
    have hSEsub : SE ⊆ slabSet T := by
      intro p hp; exact ⟨hp.2.1, hp.2.2⟩
    have hf1m : Measurable (SE.indicator (greenPhase d ξ)) :=
      (measurable_greenPhase ξ).indicator hSEm
    have hf1b : ∀ p, ‖SE.indicator (greenPhase d ξ) p‖ ≤ 1 := by
      intro p
      by_cases hp : p ∈ SE
      · rw [Set.indicator_of_mem hp, norm_greenPhase]
      · rw [Set.indicator_of_notMem hp, norm_zero]; exact zero_le_one
    have hf1s : ∀ p, p ∉ slabSet T → SE.indicator (greenPhase d ξ) p = 0 :=
      fun p hp => Set.indicator_of_notMem (fun h => hp (hSEsub h)) _
    rw [← integral_indicator hSEm,
      green_integral K σ₀ μ Γ hΓ hT _ hf1m hf1b hf1s]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hmeas : Measurable (fun x : ElapsedTime ⊤ × PDE.Vec d =>
        occupationKernel K (σ₀ + T / 2) (x.1.1 - T / 2) x.2 {w | (x.1, w) ∈ E}) := by
      have hE' : MeasurableSet {z : (ElapsedTime ⊤ × PDE.Vec d) × PDE.Vec d | (z.1.1, z.2) ∈ E} :=
        hE.preimage (by fun_prop)
      exact measurable_occupationKernel_sectionGen K (σ₀ + T / 2)
        (f := fun x : ElapsedTime ⊤ × PDE.Vec d => x.1.1 - T / 2) (u := fun x => x.2)
        (by fun_prop) (by fun_prop) hE'
    calc ∫⁻ τ, ‖∫ p, ∫ w, SE.indicator (greenPhase d ξ) (τ, w) ∂K.master (elapsedQuery σ₀ p τ) ∂μ‖ₑ
          ∂elapsedVolume ⊤
        ≤ ∫⁻ τ, (slabTimeSet T).indicator (fun τ => ∫⁻ v, occupationKernel K (σ₀ + T / 2)
            (τ.1 - T / 2) v {w | (τ, w) ∈ E} ∂ρ) τ ∂elapsedVolume ⊤ := by
          refine lintegral_mono (fun τ => ?_)
          by_cases hτ : τ ∈ slabTimeSet T
          · rw [Set.indicator_of_mem hτ]
            have hsec : MeasurableSet {w' : PDE.Vec d | (τ, w') ∈ E} := measurable_prodMk_left hE
            have hfun : ∀ w : EvolutionAmbientState d, SE.indicator (greenPhase d ξ) (τ, w) =
                phaseSection d ξ {w' : PDE.Vec d | (τ, w') ∈ E} w := by
              intro w
              unfold phaseSection
              by_cases hw : (τ, w.1) ∈ E
              · have h1 : (τ, w) ∈ SE := ⟨hw, hτ.1, hτ.2⟩
                have h2 : w ∈ ({w' : PDE.Vec d | (τ, w') ∈ E} ×ˢ (univ : Set (PDE.Vec d))) :=
                  ⟨hw, mem_univ _⟩
                rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, greenPhase_eq]
              · have h1 : (τ, w) ∉ SE := fun h => hw h.1
                have h2 : w ∉ ({w' : PDE.Vec d | (τ, w') ∈ E} ×ˢ (univ : Set (PDE.Vec d))) :=
                  fun h => hw h.1
                rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
            simp_rw [hfun]
            exact slab_section_bound K hcov hcomp σ₀ μ hT ξ τ hτ.1 hsec
          · rw [Set.indicator_of_notMem hτ]
            have hz : ∀ w : EvolutionAmbientState d, SE.indicator (greenPhase d ξ) (τ, w) = 0 :=
              fun w => Set.indicator_of_notMem (fun h => hτ ⟨h.2.1, h.2.2⟩) _
            simp [hz]
      _ = ∫⁻ τ in slabTimeSet T, ∫⁻ v, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v
            {w | (τ, w) ∈ E} ∂ρ ∂elapsedVolume ⊤ :=
          lintegral_indicator (measurableSet_slabTimeSet T) _
      _ = _ := by
          refine lintegral_lintegral_swap ?_
          exact hmeas.aemeasurable
  refine _h_xinl_0.trans (le_of_eq ?_)
  exact (slab_occupation_identity K (σ₀ + T / 2) (T / 2) T (3 * T / 2) (by linarith) hT
    (by linarith) (by linarith) _ gξ hgξ hint hE).symm

end HypoellipticAleksandrov.KineticAleksandrov.Green
