/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.OrbitPrefixSupport

/-! # LOW/HIGH catalogue insertion with a protected-grid terminal inverse

The repaired receiving state may contain literal top. Retarget its terminal
block above the protected source cut, normalize the complete field inventory,
then compose the supported inverse with whole-block collapse. The resulting
catalogue member is admissible, and the decoder fixes retained grid endpoints
and supported low orbits. No identity on unhosted invisible points is asserted.
This is a source-family producer, not a physical guarded-carrier construction.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingSupportedRepair
open Transform Value ExtOrd CappedDonor CappedDonor.Ref
open CanonicalPairedInverse
noncomputable section

variable {I : Type*} [Fintype I] {nP N J K j B : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  (L : R.LowRef K)

/-- The receiving catalogue uses the entire field vector, cutoff included. -/
def Catalogue : Set (TField P C → ExtOrd) :=
  {a | a ∈ CanonicalPairedProfiles.inventory (TField P C) j ∧
    ∃ S : R.TState j, L.TAdmissible S ∧ Synchronized S.st ∧ S.profile = a}

theorem catalogue_finite : (Catalogue (j := j) L).Finite :=
  (CanonicalPairedProfiles.inventory_finite (TField P C) j).subset (fun _ h => h.1)

/-- Constructed insertion data; this record is an output, not a completion premise. -/
structure Repair (a : TField P C → ExtOrd) (S : R.TState j) (B : ℕ) where
  encoded : R.TState j
  admissible : L.TAdmissible encoded
  synchronized : Synchronized encoded.st
  canonical : encoded.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j
  prefix_eq : ∀ d, min (encoded.profile d) (grid j B) = min (a d) (grid j B)
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (encoded.profile d) = S.profile d
  grid_fixed : ∀ b < B, decoder (grid j b) = grid j b
  reaches : grid j B ≤ decoder (grid j B)
  boundary_fixed : ∀ d, a d < grid j B → decoder (a d) = a d

variable {L}

namespace Repair
variable {a : TField P C → ExtOrd} {S : R.TState j} (r : Repair L a S B)

end Repair
end
end VaughtConjecture.Knight.ReceivingSupportedRepair
