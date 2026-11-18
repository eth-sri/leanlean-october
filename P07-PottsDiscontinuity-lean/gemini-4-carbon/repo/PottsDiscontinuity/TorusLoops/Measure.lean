module

public import PottsDiscontinuity.TorusRC.MeasureFacts

/-!
# The finite critical random-cluster law on the diamond torus

This module re-exports the normalization of the indexed `torusRCWeight` built in `TorusRC/`
as the paper's torus law `φ_T`. The finite sample space retains indexed edges,
including multiplicities at small periods.
-/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}


/-- Real-valued probability of an event under `φ_T`. -/
noncomputable abbrev phi_T_probability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) : ℝ :=
  PottsDiscontinuity.TorusRC.torusRCProbability hN hM q E



theorem phi_T_probability_eq_sum (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    phi_T_probability hN hM q E =
      ∑ A, E.indicator (PottsDiscontinuity.TorusRC.torusRCMass hN hM q) A :=
  PottsDiscontinuity.TorusRC.torusRCProbability_eq_sum hN hM q E

end PottsDiscontinuity.TorusLoops
