module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Extension
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Shell
import Mathlib.Tactic.Positivity

/-! # Fixed compact geometry for the profile sublevel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set

/- The closed unit profile sublevel is compact, with the native Euclidean gauge. -/
theorem isCompact_profile_unit_sublevel {d alpha} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) : IsCompact {q | profileFunction h q ≤ 1} := by
  obtain ⟨_, _, hc, _, _, _, hH, _, _, hcomp, _⟩ := selectedProfile_spec h
  exact (isCompact_rho_sublevel d
    (Real.rpow (1 / profileLowerComparison h) alpha⁻¹)).of_isClosed_subset
    (isClosed_le hH continuous_const)
    (profile_sublevel_subset_rho _ alpha _ 1 ha hc zero_lt_one (fun q => (hcomp q).1))

/- One fixed radius strictly bounds every velocity in the closed profile domain. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
