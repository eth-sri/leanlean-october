module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ConservationCutoff
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Mass conservation for every realizing full-space autonomous kernel

The constant classical solution is compared with actual compact terminal solutions.
The quadratic-tail coefficient tends to zero, forcing the sub-Markov mass to equal one.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology ENNReal

/-- The supplied whole-space kernel conserves mass for every ordered query. -/
theorem fullspace_mass_one {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) : E.2.master q univ = 1 := by
  let σ := q.1.1
  let τ := q.1.2.1
  let p : Point := ⟨σ, q.1.2.2.1, q.1.2.2.2⟩
  have hp : p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ :=
    ⟨q.2.1, subset_closure q.2.2.1⟩
  have : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  obtain ⟨C, _hC0, hcmp⟩ := classical_sub_le_growthBarrier
    (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
    continuous_const hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
  have hbd (N : ℕ) : 1 - (E.2.master q univ).toReal ≤
      ((N : ℝ) + 1)⁻¹ ^ 2 * growthBarrier C τ p := by
    obtain ⟨u, hu, hrep, _huniq⟩ := hE.1 τ (conservationDatum N)
      (conservationDatum_smoothCompact N τ)
    have hc := hcmp τ (BoundedBorel.const 1) (conservationDatum N) (fun _ => 1) u
      (((N : ℝ) + 1)⁻¹ ^ 2) (sq_nonneg _)
      (fullspace_constant_solution _ _ τ 1) hu
      (fun x _ => conservationDatum_deficit N x) p hp
    let state : EvolutionState autonomousWholeDomain (fun _ => 0) σ :=
      ⟨q.1.2.2, q.2.2⟩
    have hi := hE.2.1 σ τ q.2.1 state (terminalStateDatum (conservationDatum N))
    have huq : u p = ∫ x, conservationDatum N x ∂E.2.master q :=
      (hrep σ q.2.1 state).trans (hi.trans (integral_master_eq_fiber E.2 autonomousWholeDomain_measurable σ τ q.2.1 state (conservationDatum N) (conservationDatum N).measurable).symm)
    have hmass : (∫ x, conservationDatum N x ∂E.2.master q) ≤
        (E.2.master q univ).toReal := by
      have hint : Integrable (conservationDatum N) (E.2.master q) := by
        apply Integrable.mono' (integrable_const 1) (conservationDatum
          N).measurable.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_of_nonneg (conservationDatum_bounds N x).1]
        exact (conservationDatum_bounds N x).2
      simpa [integral_const, Measure.real] using (integral_mono hint (integrable_const 1) (fun x => (conservationDatum_bounds N x).2))
    rw [huq] at hc
    linarith only [hc, hmass]
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ ^ 2 * growthBarrier C τ p)
      atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul_const (growthBarrier C τ p)
  have hle : 1 ≤ (E.2.master q univ).toReal := by
    have hz := ge_of_tendsto hzero (Filter.Eventually.of_forall hbd)
    linarith
  apply le_antisymm (E.2.mass_le_one q)
  rw [← ENNReal.ofReal_toReal (measure_ne_top (E.2.master q) univ),
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hle

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
