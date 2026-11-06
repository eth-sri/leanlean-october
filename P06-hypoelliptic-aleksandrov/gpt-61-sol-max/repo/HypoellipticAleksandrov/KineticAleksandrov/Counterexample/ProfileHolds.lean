module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoBridge
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProperties
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SourceNorm

/-! # The internally constructed shared profile and its unconditional flattening consequences -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample



/-- The scalar and higher-dimensional constructions supply the complete shared profile. -/
theorem counterProfile_holds (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) : CounterProfileStatement d alpha :=
  counterProfile_of_branches d hd alpha ha ha1
    (fun _ => counterProfileOne_exists alpha ha ha1)
    (fun hd2 => counterProfileGeTwo_holds d hd2 alpha ha ha1)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
