module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Duhamel
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelGreen
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Absolute-time Green representation of the kinetic Duhamel potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Occupation
open scoped ENNReal ProbabilityTheory

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
  (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (T : ℝ) (g : KineticPoint d → ℝ)
include hΩ hγ

/-- The Green action at a point is the composition product of elapsed time
and the master kernel at the corresponding queries. Thus the Duhamel identity
holds for signed bounded measurable sources, without any smoothness assumption. -/
theorem duhamelPotential_eq_green_of_bounded
    (hgm : Measurable g) (C : ℝ) (hC : ∀ q, ‖g q‖ ≤ C)
    (s : ℝ) (hs : s < T) (p : EvolutionState Ω γ s)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K s (ENNReal.ofReal (T - s)) (Measure.dirac p) Γ) :
    duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂Γ := by
  let L := ENNReal.ofReal (T - s)
  let κ := K.master.comap (fun τ : ElapsedTime L => elapsedQuery s p τ)
    ((measurable_elapsedQuery s L).comp (measurable_const.prodMk measurable_id))
  let : ProbabilityTheory.IsFiniteKernel κ := by dsimp [κ]; infer_instance
  have hL := sub_pos.mpr hs
  let : IsFiniteMeasure (elapsedVolume L) := ⟨by
    dsimp [L]
    rw [elapsedVolume_univ _ hL]
    exact ENNReal.ofReal_lt_top⟩
  have hΓeq : Γ = (elapsedVolume L).compProd κ := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [hΓ F hF, lintegral_dirac, Measure.lintegral_compProd hF]
    rfl
  let F := fun q : ElapsedTime L × EvolutionAmbientState d => g ⟨s + q.1.1, q.2.1, q.2.2⟩
  have hFm : Measurable F := hgm.comp ((KineticPoint.measurable_equivProd_symm d).comp
    ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd))
  have hFi : Integrable F ((elapsedVolume L).compProd κ) :=
    (integrable_const C).mono' hFm.aestronglyMeasurable (.of_forall fun q => hC _)
  rw [hΓeq, Measure.integral_compProd hFi]
  let f := duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩
  have heq (τ : ElapsedTime L) : (∫ w, F (τ, w) ∂κ τ) = f (s + τ.1) := by
    unfold f duhamelIntegrand
    rw [dite_eq_left ⟨le_add_of_nonneg_right τ.2.1.le, p.2.1⟩]
    rfl
  have hfm : Measurable (fun r : ℝ => f (s + r)) :=
    (measurable_duhamelIntegrand K hΩ hγ g hgm).comp
      (measurable_const.prodMk (measurable_const.add measurable_id))
  simp_rw [heq]
  rw [integral_elapsed_eq (T - s) hL _ hfm, integral_Ioo_shift f s (T - s) hL.le]
  simp [duhamelPotential, f]

/-- The kinetic Duhamel potential equals the supplied Green integral in absolute time. -/
theorem duhamelPotential_eq_green
    (hgcont : Continuous g) (hgc : HasCompactSupport g)
    (s : ℝ) (hs : s < T) (p : EvolutionState Ω γ s)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K s (ENNReal.ofReal (T - s)) (Measure.dirac p) Γ) :
    duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂Γ := by
  obtain ⟨C, hC⟩ := hgcont.bounded_above_of_compact_support hgc
  exact duhamelPotential_eq_green_of_bounded K hΩ hγ T g hgcont.measurable C hC s hs p Γ hΓ

end

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
