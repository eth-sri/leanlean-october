module

public import Chazelle.Core.SweepEvStopH

/-!
# The sweep (WP-D), stage 3: the genuineness check, RAM blocks

* `gSetL`: the inputs of the local hit (`gSet_val`);
* `gHgt`: normalise the arrival position, then fix a vertex position (`hHgt_irs`): the position
  gets a positive height code naming its height, with the same parameter and point.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The inputs of the local hit -/

/-- The inputs of the local hit: the descriptors and the normal form of `C₁`, the arrival
position, the reverse direction, the walk length, the tag `0`, the empty accumulator. -/
def gSetL : List Instr :=
  [.copyN lMD MD₁, .copyN lCD CD₁, .copyN lNF (sw 3), .copyN lE (eA + 1), .copyN lH (eA + 2),
    .subN lD K1 oD, .copyN lN cN1, .constN lT 0, .constN accA 0]

theorem gSet_val (m f : ℕ → ℕ) :
    regB m gSetL f lMD = f MD₁ ∧ regB m gSetL f lCD = f CD₁ ∧ regB m gSetL f lNF = f (sw 3) ∧
    regB m gSetL f lE = f (eA + 1) ∧ regB m gSetL f lH = f (eA + 2) ∧
    regB m gSetL f lD = f K1 - f oD ∧ regB m gSetL f lN = f cN1 ∧ regB m gSetL f lT = 0 ∧
    regB m gSetL f accA = 0 ∧
    (∀ q, (q < 241100 ∨ 241107 < q) → q ≠ accA → regB m gSetL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq hq' => regB_other _ _ _ (fun i hi => by
    fin_cases hi <;>
      simp only [dstI, lMD, lCD, lNF, lE, lH, lD, lN, lT, sw] <;>
      first | omega)⟩ <;>
  rfl

theorem gSet_ok (m f : ℕ → ℕ) (hW : 0 ≤ W) : okB W m gSetL f := by
  simp only [gSetL, reg_check]
  exact ⟨iscr_sw (by reg_omega) (by reg_omega),
    iscr_sw (by reg_omega) (by reg_omega),
    iscr_sw (by reg_omega) (by reg_omega),
    iscr_sw (by reg_omega) (by reg_omega),
    iscr_sw (by reg_omega) (by reg_omega),
    iscr_sw (by reg_omega) (by reg_omega),
    iscr_sw (by reg_omega) (by reg_omega),
    ⟨iscr_sw (by reg_omega) (by reg_omega), hW⟩,
    ⟨iscr_sw (by reg_omega) (by reg_omega), hW⟩, trivial⟩

/-- The shared height correction for the arrival position on the left chain. -/
def gHgt : Stmt := hHgt CD₁ cN1

end
end SweepEv
end Chazelle.Core
