module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakSource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningGeTwo
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity

/-! # The complete conditional flattened-profile source theorem

All representatives are explicit functions of the same jointly selected profile
witnesses. Their weak identities and source equation are proved here, rather than
assumed as an additional profile field.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set Filter

/- The literal flattening has the complete selected weak-jet and source interface. -/
theorem flatProfile_source {d } (hd : 1 ≤ d) {alpha }
    (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    FlatProfileSourceStatement h r := by
  obtain ⟨hmx, hmv, hmh⟩ := measurable_flatProfile_jets h r
  obtain ⟨hx, hv, hh⟩ := flatProfile_jets_locallyIntegrable_of_profile h r hr
  have _h_xinl_0 : ∀ᵐ q ∂volume, statOp (profileMatrix h) (selectedFlatProfile h r) q = flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
    filter_upwards [flatProfile_jets_ae_of_profile h r hr,
      flatProfile_representatives_source h r] with q hj hs
    unfold statOp
    rw [← hj.1, ← hj.2.2]
    exact hs
  exact ⟨continuous_selectedFlatProfile h r, hmx, hmv, hmh,
    flatProfile_jets_compact_bound_of_profile h r hr, hx, hv, hh,
    flatProfile_jets_ae_of_profile h r hr, flatProfile_weak_of_profile hd h r hr,
    flatProfile_representatives_source h r, _h_xinl_0⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
