module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeak
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelGreen

/-! # Signed bounded-source Green representation

The signed representation is the real-valued composition-product identity for
the elapsed-time Green measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo
open scoped ENNReal

section
variable (H : Interval) (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))

private theorem sourceSlice_integrable (g : BoundedBorel Point)
    (q : EvolutionQuery (intervalDomain H) (fun _ => 0)) :
    Integrable (fun w => g ⟨q.1.2.1, w.1, w.2⟩) (K.master q) := by
  obtain ⟨C, -, hg⟩ := g.exists_bound
  apply integrable_bounded_real (K.master q) _ _ C (fun w => hg _)
  exact g.measurable.comp ((KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk measurable_id))

/-- The actual finite-horizon Duhamel potential is linear under bounded-source subtraction. -/
theorem strip_duhamel_sub (g f : BoundedBorel Point)
    (p : Point) (T : ℝ) :
    duhamelPotential K T (g - f : BoundedBorel Point) p =
      duhamelPotential K T g p - duhamelPotential K T f p := by
  have hi : duhamelIntegrand K (g - f : BoundedBorel Point) p = fun r =>
      duhamelIntegrand K g p r - duhamelIntegrand K f p r := by
    funext r
    unfold duhamelIntegrand
    split
    · exact integral_sub (sourceSlice_integrable H K g _) (sourceSlice_integrable H K f _)
    · simp only [sub_self]
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
theorem duhamelPotential_eq_green_bounded (T : ℝ)
    (g : BoundedBorel Point) (s : ℝ) (hs : s < T)
    (p : EvolutionState (intervalDomain H) (fun _ => 0) s)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState 1))
    (hΓ : IsGreenMeasure K s (ENNReal.ofReal (T - s)) (Measure.dirac p) Γ) :
    duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂Γ := by
  obtain ⟨C, -, hC⟩ := g.exists_bound
  exact duhamelPotential_eq_green_of_bounded K (intervalDomain_measurable H)
    continuous_const T g g.measurable C hC s hs p Γ hΓ

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
