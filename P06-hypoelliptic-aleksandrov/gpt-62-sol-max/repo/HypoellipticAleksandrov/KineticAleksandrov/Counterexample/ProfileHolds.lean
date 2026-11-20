module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoBridge
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SourceNorm

/-! # The internally constructed shared profile and its unconditional flattening consequences -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The scalar and higher-dimensional constructions supply the complete shared profile. -/
theorem counterProfile_holds (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) : CounterProfileStatement d alpha := by
  by_cases h : d = 1
  · subst d
    exact counterProfileOne_exists alpha ha ha1
  · have hd2 : 2 ≤ d := by omega
    exact counterProfile_ge_two d hd2 alpha ha ha1 (counterProfileGeTwo_holds d hd2 alpha ha ha1)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
