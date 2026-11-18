module

public import GS.UnitaryCS.Angles
public import GS.UnitaryCS.Bridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Complete unitary cosine-sine decomposition and exact scalar GS exhaustion

All existence statements are unconditional. The proof constructs a Hermitian
spectral basis, completes every prescribed normalized nonzero column, and
recovers the complementary columns using unitarity. Zero and unit singular
values, repeated singular values, and dimension zero are included.
-/

noncomputable section
open Matrix GS.UnitaryGeometry
namespace GS.Results.UnitaryCosineSine

/-- The original three-factor scalar GS family with block sizes p,2,p
equals the full unitary group in dimension 2p, for the specified shuffle. -/
theorem scalar_exhaustion {p : ℕ} {M : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ M ↔ Unitary M :=
  UnitaryCS.inA3Unitary_scalar_two_iff

end GS.Results.UnitaryCosineSine
