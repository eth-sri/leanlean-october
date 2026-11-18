module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullSpaceIdentification
import Mathlib.Analysis.Calculus.Deriv.Comp
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Conservation

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set HypoellipticAleksandrov.KineticAleksandrov.SectionTwo MeasureTheory

/-- Translate time while keeping physical position and velocity fixed. -/
def autonomousTimeShift (h : ℝ) (p : KineticPoint 1) : KineticPoint 1 :=
  ⟨p.time + h, p.position, p.velocity⟩

/-- The time translation is continuous. -/
theorem continuous_autonomousTimeShift (h : ℝ) : Continuous (autonomousTimeShift h) :=
  KineticPoint.continuous_mk (continuous_time.add continuous_const)
    continuous_position continuous_velocity

/-- The forward autonomous operator commutes with time translation. -/
theorem autonomous_operator_timeShift (a : ℝ → ℝ → ℝ) (h : ℝ)
    (u : KineticPoint 1 → ℝ) (p : KineticPoint 1) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (fun q => u (autonomousTimeShift h q)) p =
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1) u
      (autonomousTimeShift h p) := by
  rw [transportedForwardOperator_apply, transportedForwardOperator_apply]
  have ht : kineticTimeDerivative (fun q => u (autonomousTimeShift h q)) p =
      kineticTimeDerivative u (autonomousTimeShift h p) :=
    deriv_comp_add_const (fun r => u ⟨r, p.position, p.velocity⟩) h p.time
  rw [ht]
  rfl

/-- Time translation carries an actual full-space terminal solution to an actual solution. -/
theorem fullspace_classical_timeShift {a : ℝ → ℝ → ℝ} (h τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState 1)) (u : KineticPoint 1 → ℝ)
    (hu : IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient a) (identityDrift 1) (τ + h) F u) :
    IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient a) (identityDrift 1) τ F
      (fun p => u (autonomousTimeShift h p)) := by
  have hd (t : ℝ) : movingDomain autonomousWholeDomain (fun _ => 0) t = univ :=
    movingDomain_wholeSpace 1 t
  have hclosed (p : KineticPoint 1)
      (hp : p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ) :
      autonomousTimeShift h p ∈
        evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) (τ + h) :=
    ⟨by change p.time + h ≤ τ + h; linarith [hp.1], by rw [hd, closure_univ]; trivial⟩
  obtain ⟨⟨C, hC0, hC⟩, hc, hs, hop, ht, _⟩ := hu
  refine ⟨⟨C, hC0, fun p hp => hC _ (hclosed p hp)⟩,
    hc.comp (continuous_autonomousTimeShift h).continuousOn hclosed, ?_, ?_, ?_, ?_⟩
  · exact hs.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨by change q.1 + h < τ + h; linarith [hq.1], by rw [hd]; trivial⟩)
  · intro p hp
    rw [autonomous_operator_timeShift]
    exact hop _ ⟨by change p.time + h < τ + h; linarith [hp.1], by rw [hd]; trivial⟩
  · intro p hp
    exact ht _ ⟨congrArg (fun r => r + h) hp.1,
      by rw [hd, closure_univ]; trivial⟩
  · intro p hp
    have hf := hp.2
    rw [hd, frontier_univ] at hf
    exact False.elim hf


/-- Full-space state membership has no spatial restriction. -/
theorem autonomous_stateSet (t : ℝ) :
    evolutionStateSet autonomousWholeDomain (fun _ => 0) t = univ := by
  change movingDomain (wholeSpace 1) (fun _ => 0) t ×ˢ univ = univ
  rw [movingDomain_wholeSpace, univ_prod_univ]

/-- An ordered query after translating both times by the same amount. -/
def autonomousQueryShift (h : ℝ)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) :
    EvolutionQuery autonomousWholeDomain (fun _ => 0) :=
  ⟨(q.1.1 + h, q.1.2.1 + h, q.1.2.2),
    by linarith [q.2.1], by rw [autonomous_stateSet]; trivial⟩

/-- Time translation leaves the entire full-space terminal measure unchanged. -/
theorem fullspace_kernel_timeShift {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (h : ℝ)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) :
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
    ⟨hφ, hφc, by rw [autonomous_stateSet]; exact subset_univ _⟩
  obtain ⟨u, hu, hru, _⟩ := hE.1 (q.1.2.1 + h) F (hF _)
  obtain ⟨v, hv, hrv, hvuniq⟩ := hE.1 q.1.2.1 F (hF _)
  have hp : (⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ : KineticPoint 1) ∈
      evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) q.1.2.1 :=
    ⟨q.2.1, subset_closure q.2.2.1⟩
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
  have h1 := (hru (q.1.1 + h) (autonomousQueryShift h q).2.1 ph).trans
    (hrep _ _ _ ph)
  have h2 := (hrv q.1.1 q.2.1 p).trans (hrep _ _ _ p)
  exact h1.symm.trans ((hvuniq _ (fullspace_classical_timeShift h q.1.2.1 F u hu) hp).trans h2)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

