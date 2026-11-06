module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly

/-! # Bounded Borel source integrals at finite and infinite terminal horizons -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo
open scoped ENNReal
section
variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ) (e : StripPole H T)

/-- Quadratic mass makes the unique Green measure finite at every horizon. -/
instance stripGreen_isFiniteMeasure
     :
    IsFiniteMeasure (stripGreen hH hLE hlam hLam A H T e) :=
  ⟨lt_of_le_of_lt (stripGreen_quadratic_mass hH hLE hlam hLam A H T e)
    ENNReal.ofReal_lt_top⟩

/-- Every bounded Borel source is integrable against the same finite or infinite Green measure. -/
theorem stripGreen_integrable
    
    (g : BoundedBorel Point) : Integrable g (stripGreen hH hLE hlam hLam A H T e) := by
  obtain ⟨C, -, hg⟩ := g.exists_bound
  exact integrable_bounded_real _ g g.measurable C hg
end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
