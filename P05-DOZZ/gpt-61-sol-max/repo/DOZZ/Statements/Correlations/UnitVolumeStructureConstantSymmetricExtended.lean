/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
import DOZZ.Correlations.Symmetry.SymmetricExtended
import Batteries.Tactic.Alias

/-! The statement `DOZZ.unitVolumeStructureConstant_symmetric_extended`,
proved by `DOZZ.Proofs.unitVolumeStructureConstant_symmetric_extended`. -/

public section


namespace DOZZ

/-- Extended-domain permutation symmetry, required where the three-to-two residue bridge
(`DOZZ.structureConstant_threeToTwo_residue_bridge`,
`DOZZ.unitVolumeStructureConstant_threeToTwo_residue_bridge`) is used in the second slot. -/
alias unitVolumeStructureConstant_symmetric_extended := DOZZ.Proofs.unitVolumeStructureConstant_symmetric_extended

end DOZZ
