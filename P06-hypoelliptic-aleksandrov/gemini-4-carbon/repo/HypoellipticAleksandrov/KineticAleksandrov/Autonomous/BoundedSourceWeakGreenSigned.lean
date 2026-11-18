module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimits
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelGreen

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory SectionTwo Evolution Set Filter
open scoped ENNReal

/-- Every bounded Borel source has the actual weak Duhamel forcing equation on the strip. -/
theorem strip_duhamel_weak {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (T : ℝ) (g : BoundedBorel Point) :
    IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T)
      (duhamelPotential E.2 T g) (fun p => -g p) := by
  obtain ⟨C, hC, hg⟩ := g.exists_bound
  exact duhamel_bounded_isKineticWeakTransportedSolution (intervalDomain_admissible H)
    (intervalDomain_measurable H) continuous_const (evolutionCoefficient A.a)
    (identityDrift 1) E.1 E.2 hE (evolutionCoefficient_smooth A)
    (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1)
    g g.measurable C hC hg T



/-- The actual finite-horizon Duhamel potential is linear under bounded-source subtraction. -/
theorem strip_duhamel_sub (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (g f : BoundedBorel Point)
    (p : Point) (T : ℝ) :
    duhamelPotential K T (g - f : BoundedBorel Point) p =
      duhamelPotential K T g p - duhamelPotential K T f p  := by
  have sourceSlice_integrable (g : BoundedBorel Point) (q : EvolutionQuery (intervalDomain H) (fun _ => 0)) :
      Integrable (fun w => g ⟨q.1.2.1, w.1, w.2⟩) (K.master q) := by
    obtain ⟨C, -, hg⟩ := g.exists_bound
    apply integrable_bounded_real (K.master q) _ _ C (fun w => hg _)
    exact g.measurable.comp ((KineticPoint.measurable_equivProd_symm 1).comp
      (measurable_const.prodMk measurable_id))
  have hi : duhamelIntegrand K (g - f : BoundedBorel Point) p = fun r =>
      duhamelIntegrand K g p r - duhamelIntegrand K f p r := by
    funext r
    unfold duhamelIntegrand
    split
    · unfold duhamelSourceIntegral
      exact integral_sub (sourceSlice_integrable g _) (sourceSlice_integrable f _)
    · simp
  obtain ⟨Cg, hCg, hg⟩ := g.exists_bound
  obtain ⟨Cf, hCf, hf⟩ := f.exists_bound
  unfold duhamelPotential
  rw [hi]
  exact integral_sub
    (integrableOn_duhamelIntegrand_bounded K (intervalDomain_measurable H)
      continuous_const g g.measurable Cg hCg hg p T)
    (integrableOn_duhamelIntegrand_bounded K (intervalDomain_measurable H)
      continuous_const f f.measurable Cf hCf hf p T)

/-- Every bounded signed Borel source has the exact actual Green representation. -/
theorem duhamelPotential_eq_green_bounded (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (s : ℝ) (hs : s < T)
    (p : EvolutionState (intervalDomain H) (fun _ => 0) s)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState 1))
    (hΓ : IsGreenMeasure K s (ENNReal.ofReal (T - s)) (Measure.dirac p) Γ) :
    duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂Γ  := by
  have duhamelPotential_eq_green_bounded_nonneg (g : BoundedBorel Point) (hg0 : ∀ q, 0 ≤ g q) (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState 1)) (hΓ : IsGreenMeasure K s (ENNReal.ofReal (T - s)) (Measure.dirac p) Γ) :
      duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂Γ := open Occupation in by
    have hΩ := intervalDomain_measurable H
    have hγ : Continuous (fun _ : ℝ => (0 : PDE.Vec 1)) := continuous_const
    have hgm := g.measurable
    obtain ⟨C, _, hC⟩ := g.exists_bound
    have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
    have hLpos := sub_pos.2 hs
    have hC0 := (hg0 ⟨0, 0, 0⟩).trans (hgb _)
    let p0 := p
    let F : ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState 1 → ℝ≥0∞ := fun q =>
      ENNReal.ofReal (g ⟨s + q.1.1, q.2.1, q.2.2⟩)
    have hFm : Measurable (fun q : ElapsedTime (ENNReal.ofReal (T - s)) ×
        EvolutionAmbientState 1 => g ⟨s + q.1.1, q.2.1, q.2.2⟩) := by
      apply hgm.comp
      exact (KineticPoint.measurable_equivProd_symm 1).comp
        ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
          measurable_snd)
    have hΓF := hΓ F (ENNReal.measurable_ofReal.comp hFm)
    rw [lintegral_dirac] at hΓF
    have hin : ∀ τ : ElapsedTime (ENNReal.ofReal (T - s)),
        ∫⁻ w, F (τ, w) ∂K.master (elapsedQuery s p0 τ) =
          ENNReal.ofReal (duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + τ.1)) := by
      intro τ
      have hsr : s ≤ s + τ.1 := le_add_of_nonneg_right τ.2.1.le
      have hint : Integrable (fun w => g ⟨s + τ.1, w.1, w.2⟩)
          (K.master (elapsedQuery s p0 τ)) := by
        refine Integrable.mono' (integrable_const (max C 0))
          ((hgm.comp ((KineticPoint.measurable_equivProd_symm 1).comp
            (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
          (Eventually.of_forall fun w => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
        exact (hgb _).trans (le_max_left _ _)
      have h2 :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => hg0 _)).symm
      rw [h2]
      congr 1
      unfold duhamelIntegrand
      rw [dite_eq_left (show s ≤ s + τ.1 ∧
        p.1.1 ∈ movingDomain (intervalDomain H) (fun _ => 0) s from ⟨hsr, p.2.1⟩)]
      rfl
    have hfm : Measurable (fun x => duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + x)) := by
      have := measurable_duhamelIntegrand K hΩ hγ g hgm
      exact this.comp (measurable_const.prodMk (measurable_const.add measurable_id))
    have hfin : IsFiniteMeasure (elapsedVolume (ENNReal.ofReal (T - s))) :=
      ⟨by rw [elapsedVolume_univ _ hLpos]; exact ENNReal.ofReal_lt_top⟩
    have hnn : ∀ x, 0 ≤ duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + x) := fun x =>
      duhamelIntegrand_nonneg K g hg0 _ _
    have hfi : Integrable (fun τ : ElapsedTime (ENNReal.ofReal (T - s)) =>
        duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ (s + τ.1))
        (elapsedVolume (ENNReal.ofReal (T - s))) := by
      refine Integrable.mono' (integrable_const (max C 0))
        (hfm.comp measurable_subtype_coe).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
      exact (duhamelIntegrand_le K g hg0 C hC0 hgb _ _).trans (le_max_left _ _)
    have hlint : ∫⁻ q, F q ∂Γ = ENNReal.ofReal
        (duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩) := by
      rw [hΓF, lintegral_congr hin]
      rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun τ => hnn τ.1)]
      congr 1
      rw [integral_elapsed_eq (T - s) hLpos _ hfm, integral_Ioo_shift (fun r =>
        duhamelIntegrand K g ⟨s, p.1.1, p.1.2⟩ r) s (T - s) hLpos.le]
      unfold duhamelPotential
      simp
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => hg0 _)
      hFm.aestronglyMeasurable]
    have hn : 0 ≤ duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ :=
      integral_nonneg (fun r => duhamelIntegrand_nonneg K g hg0 ⟨s, p.1.1, p.1.2⟩ r)
    rw [hlint, ENNReal.toReal_ofReal hn]
  obtain ⟨C, hC, hg⟩ := g.exists_bound
  let c : BoundedBorel Point := BoundedBorel.const C
  have hp0 : ∀ q, 0 ≤ (g + c) q := by
    intro q
    change 0 ≤ g q + C
    linarith [neg_abs_le (g q), hg q]
  have : IsFiniteMeasure Γ := ⟨lt_of_le_of_lt (greenMeasure_mass_le K s (T - s) (sub_pos.mpr hs) (Measure.dirac p) Γ hΓ) (by simp)⟩
  have hi (f : BoundedBorel Point) :
      Integrable (fun q => f ⟨s + q.1.1, q.2.1, q.2.2⟩) Γ := by
    obtain ⟨B, -, hb⟩ := f.exists_bound
    apply integrable_bounded_real Γ _ _ B (fun q => hb _)
    exact f.measurable.comp ((KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd))
  have hsub := strip_duhamel_sub H K (g + c) c ⟨s, p.1.1, p.1.2⟩ T
  rw [add_sub_cancel_right] at hsub
  rw [hsub, (duhamelPotential_eq_green_bounded_nonneg (g + c) hp0 Γ hΓ), (duhamelPotential_eq_green_bounded_nonneg c (fun _ => hC) Γ hΓ), ← integral_sub (hi (g + c)) (hi c)]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    change (g _ + C) - C = g _
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

