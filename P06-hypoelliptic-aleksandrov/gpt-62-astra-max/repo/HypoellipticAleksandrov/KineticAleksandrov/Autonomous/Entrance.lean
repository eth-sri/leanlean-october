module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceDensity

/-! # The literal source entrance lemma

Source: companion paper, Lemma 8.6. This theorem assembles the actual
clipped-cylinder count, the mass, time and domination estimates and the proved
time-bin density estimate.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The exact source entrance proposition holds relative to the PDE classical inputs. -/
theorem entranceStatement_holds :
    EntranceStatement := by
  intro lam Lam hlam hLam
  constructor
  · obtain ⟨B, hB, hb⟩ := exists_visitStartsQ_mass_constant hlam hLam
    obtain ⟨M, hM, hm⟩ := visit_short_time_mass hlam hLam
    refine ⟨B + M, add_pos hB hM, ?_⟩
    intro A c Z0 R hR P hP _hcore
    refine ⟨visitStartsQ_isFiniteMeasure hlam hLam A c Z0 R hR P hP,
      entrance_visitStartsQ_ae_closedEntrance hlam hLam A c Z0 R hR P hP,
      ?_, ?_, ?_⟩
    · apply (hb A c Z0 R hR P hP).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM.le)
      exact add_nonneg zero_le_one (div_nonneg hR.le c.positive.le)
    · intro a
      exact (hm A c Z0 R hR P hP a).trans
        (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hB.le))
    · exact (core_green_le_visitGreen hlam hLam A c Z0 R hR P hP).trans_eq
        (congrArg (fun rho : Measure Point => rho.restrict {p | p.velocity 0 ∈ c.core})
          (entrance_coreAllTimeGreen_eq hlam hLam A c (visitStartsQ hlam hLam A c Z0 R hR P hP)))
  · apply entrance_density

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
