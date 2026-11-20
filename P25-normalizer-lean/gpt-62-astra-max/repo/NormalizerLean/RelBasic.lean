module

public import NormalizerLean.AtkinLehner

@[expose] public section

/-!
# Infrastructure for the relations: Fricke elements, transfer between representatives, (14)
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### h at prime powers -/

/-! ### The Fricke element -/

/-! ### Transfer between representatives -/

/-! ### The local generator assignment and the image of r -/

/-- w ↦ wg, s ↦ S_k. -/
def locF (wg : SL(2, ℝ)) (k : ℕ) : LGen → SL(2, ℝ)
  | .w => wg
  | .s => S k

/-! ### (14): [r, s] for m = n h² -/

end

end NormalizerLean
