/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.ReceivingCatalogueFibres

/-! # Owner factorization followed by LOW/HIGH catalogue repair

The old source is a catalogue state, not the arbitrary physical ambient. Its
actual chart and a lawful private prescription construct the repaired source,
the same-grade fibre, canonical insertion, and outgoing bounded decoder.
No new source rows are added to the catalogue.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PrivateCatalogueRepair
open Transform Value ExtOrd CappedDonor CappedDonor.Ref CanonicalPairedInverse
open SharpWitnessComposition ReceivingSupportedRepair
noncomputable section

variable {I : Type*} [Fintype I] {nP N J K j : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  {L : R.LowRef K}

/-- Numerical readback at every actual present private occurrence. -/
theorem profile_private (S : R.TState j) (d : C.scheme.below (effC J j)) :
    S.profile (.field (.priv d.1)) = S.st.v d := by
  change S.st.sourceProfile (.priv d.1) = _
  rw [State.sourceProfile_of_present _ ((present_priv_iff j d.1).mp d.2)]
  rfl

namespace Result
variable {S : R.TState j} {p : C.scheme.below (effC J j) → ExtOrd}
  {σ : ExtOrd → ExtOrd} {γ M : ExtOrd}

end Result

end
end VaughtConjecture.Knight.PrivateCatalogueRepair
