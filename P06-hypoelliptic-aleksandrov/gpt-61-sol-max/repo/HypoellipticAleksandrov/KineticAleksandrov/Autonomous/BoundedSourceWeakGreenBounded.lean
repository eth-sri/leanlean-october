module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeak
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelGreen

/-! # Bounded Borel Green representation with the exact finite elapsed-time measure -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Filter
open SectionTwo Occupation
open scoped ENNReal ProbabilityTheory

/-- The nonnegative bounded Borel potential equals its unique native Green integral.
This uses boundedness and measurability, without a compact-support or smoothness premise. -/
theorem duhamelPotential_eq_green_bounded_nonneg (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (hg0 : ∀ q, 0 ≤ g q)
    (s : ℝ) (hs : s < T) (p : EvolutionState (intervalDomain H) (fun _ => 0) s)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState 1))
    (hΓ : IsGreenMeasure K s _ (Measure.dirac p) Γ) :
    duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂Γ := by
  let sharedTerm_04beedb006 := ((ENNReal.ofReal (T - s)))
  have hΩ := intervalDomain_measurable H
  have hγ : Continuous (fun _ : ℝ => (0 : PDE.Vec 1)) := continuous_const
  have hgm  := g.measurable
  obtain ⟨C, _, hC⟩ := g.exists_bound
  have hgb  := fun p => (le_abs_self _).trans (by exact hC p)
  have hLpos  := sub_pos.2 hs
  have hC0  := (hg0 ⟨0, 0, 0⟩).trans (hgb _)
  let p0 := p
  let F : ElapsedTime sharedTerm_04beedb006 × EvolutionAmbientState 1 → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (g ⟨s + q.1.1, q.2.1, q.2.2⟩)
  have hFm : Measurable (fun q : ElapsedTime sharedTerm_04beedb006 ×
      EvolutionAmbientState 1 => g ⟨s + q.1.1, q.2.1, q.2.2⟩) := by
    apply hgm.comp
    exact (KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
        measurable_snd)
  have hF  := ENNReal.measurable_ofReal.comp hFm
  have hΓF := hΓ F hF
  rw [lintegral_dirac] at hΓF
  have hin : ∀ τ : ElapsedTime sharedTerm_04beedb006,
      ∫⁻ w, F (τ, w) ∂K.master (elapsedQuery s p0 τ) =
        ENNReal.ofReal (duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + τ.1)) := by
    intro τ
    have hsr : s ≤ s + τ.1 := le_add_of_nonneg_right τ.2.1.le
    have hint : Integrable (fun w : EvolutionAmbientState 1 => g ⟨s + τ.1, w.1, w.2⟩)
        (K.master (elapsedQuery s p0 τ)) := by
      refine Integrable.mono' (integrable_const (max C 0))
        ((hgm.comp ((KineticPoint.measurable_equivProd_symm 1).comp
          (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
        (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact (hgb _).trans (le_max_left _ _)
    have h2  :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => hg0 _)).symm
    rw [h2]
    congr 1
    unfold duhamelIntegrand
    rw [dite_eq_left (show s ≤ s + τ.1 ∧
      p.1.1 ∈ movingDomain (intervalDomain H) (fun _ => 0) s from ⟨hsr, p.2.1⟩)]
    rfl
  have hfm : Measurable (fun x  => duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + x)) := by
    have := measurable_duhamelIntegrand K hΩ hγ g hgm
    exact this.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  have hfin : IsFiniteMeasure (elapsedVolume sharedTerm_04beedb006) :=
    ⟨by rw [elapsedVolume_univ _ hLpos]; exact ENNReal.ofReal_lt_top⟩
  have hnn : ∀ x, 0 ≤ duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + x) := fun x =>
    duhamelIntegrand_nonneg K g hg0 _ _
  have hfi : Integrable (fun τ : ElapsedTime sharedTerm_04beedb006 =>
      duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + τ.1))
      (elapsedVolume sharedTerm_04beedb006) := by
    refine Integrable.mono' (integrable_const (max C 0))
      (hfm.comp measurable_subtype_coe).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
    exact (duhamelIntegrand_le K g hg0 C hC0 hgb _ _).trans (le_max_left _ _)
  have hlint : ∫⁻ q, F q ∂Γ = ENNReal.ofReal
      (duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩) := by
    rw [hΓF, lintegral_congr hin]
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun τ => hnn τ.1)]
    congr 1
    rw [integral_elapsed_eq (T - s) hLpos _ hfm, integral_Ioo_shift ((duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩)) s (T - s) hLpos.le]
    unfold duhamelPotential
    simp
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => hg0 _)
    hFm.aestronglyMeasurable]
  change _ = (∫⁻ q, F q ∂Γ).toReal
  have hn : 0 ≤ duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ :=
    integral_nonneg (fun r => duhamelIntegrand_nonneg K g hg0 _ r)
  rw [hlint, ENNReal.toReal_ofReal hn]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
