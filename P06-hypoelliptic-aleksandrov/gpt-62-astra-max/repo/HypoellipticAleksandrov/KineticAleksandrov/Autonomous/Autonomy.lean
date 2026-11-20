module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyTimeShift
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Conservation

/-! # Time autonomy of the full-space kernel

Time translation is proved on classical solutions and then transferred by smooth tests.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Full-space state membership has no spatial restriction. -/
theorem autonomous_stateSet (t : ℝ) :
    evolutionStateSet autonomousWholeDomain (fun _ => 0) t = univ := by
  change movingDomain (wholeSpace 1) (fun _ => 0) t ×ˢ univ = univ
  rw [movingDomain_wholeSpace, univ_prod_univ]

variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution)
    (hE : IsFullSpaceEvolution A E) (h : ℝ)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0))

include h q in
/-- An ordered query after translating both times by the same amount. -/
def autonomousQueryShift :
    EvolutionQuery autonomousWholeDomain (fun _ => 0) :=
  ⟨(q.1.1 + h, q.1.2.1 + h, q.1.2.2),
    by linarith [q.2.1], by rw [autonomous_stateSet]; trivial⟩

include hE in
/-- Time translation leaves the entire full-space terminal measure unchanged. -/
theorem fullspace_kernel_timeShift :
    E.2.master (autonomousQueryShift h q) = E.2.master q := by
  have : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (E.2.master (autonomousQueryShift h q)) :=
    ⟨(E.2.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  apply measure_eq_of_smooth_integral_eq isOpen_univ (by simp) (by simp)
  intro φ hφ hφc _hφU hφr
  let F := smoothTestDatum φ hφ hφr
  have hF (τ : ℝ) :
      IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) τ F :=
    ⟨hφ, hφc, by rw [autonomous_stateSet]; apply subset_univ⟩
  obtain ⟨u, hu, hru, _⟩ := hE.1 (q.1.2.1 + h) F (hF _)
  obtain ⟨v, hv, hrv, hvuniq⟩ := hE.1 q.1.2.1 F (hF _)
  have hp : (⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩) ∈
      evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) q.1.2.1 :=
    ⟨q.2.1, subset_closure q.2.2.1⟩
  have heq := hvuniq _ (fullspace_classical_timeShift h q.1.2.1 F u hu) hp
  let p : EvolutionState autonomousWholeDomain (fun _ => 0) q.1.1 :=
    ⟨q.1.2.2, q.2.2⟩
  let ph : EvolutionState autonomousWholeDomain (fun _ => 0) (q.1.1 + h) :=
    ⟨q.1.2.2, by rw [autonomous_stateSet]; trivial⟩
  have hrep (σ τ : ℝ) (hστ : σ ≤ τ)
      (s : EvolutionState autonomousWholeDomain (fun _ => 0) σ) :
      E.1 σ τ hστ (terminalStateDatum F) s =
        ∫ x, F x ∂E.2.master (evolutionQueryOfState _ _ σ τ hστ s) :=
    (hE.2.1 σ τ hστ s (terminalStateDatum F)).trans
      (integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
        σ τ hστ s F F.measurable).symm
  exact ((hru (q.1.1 + h) (autonomousQueryShift h q).2.1 ph).trans (hrep _ _ _ ph)).symm.trans (heq.trans ((hrv q.1.1 q.2.1 p).trans (hrep _ _ _ p)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
