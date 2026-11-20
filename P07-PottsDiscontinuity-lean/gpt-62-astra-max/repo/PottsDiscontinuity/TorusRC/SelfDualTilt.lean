module

public import PottsDiscontinuity.Torus.DualLoopTransport
public import PottsDiscontinuity.Torus.RCWeight

/-! # The self-dual torus weight used in the crossing argument -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (A : RCConfig N M)
include hN hM q A

/-- The source's self-dual weight: the standard RC loop weight with the
`q^s` net correction removed. Its normalized law is the measure denoted
`\widetilde φ_T` in the proof of (3.15). -/
noncomputable def torusRCTiltWeight : ℝ :=
  torusNormalization q N M * Real.sqrt q.val ^ rcLoopCount hN hM A

theorem torusRCTiltWeight_eq_standard_div_net :
    torusRCTiltWeight hN hM q A =
      torusRCWeight hN hM q A / q.val ^ rcNetIndicator hN hM A := by
  have hq : q.val = (Real.sqrt q.val) ^ 2 := by
    grind
  have hpow : q.val ^ rcNetIndicator hN hM A =
      Real.sqrt q.val ^ (2 * rcNetIndicator hN hM A) := by
    grind [pow_mul]
  have hroot :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.property)
  have hden : Real.sqrt q.val ^ (2 * rcNetIndicator hN hM A) ≠ 0 :=
    pow_ne_zero _ hroot.ne'
  rw [torusRCTiltWeight, torusRCWeight_eq_loopWeight hN hM q A, hpow]
  grind

/-- The tilted weight is invariant under the translated complementary duality. -/
theorem torusRCTiltWeight_translatedDual :
    torusRCTiltWeight hN hM q A =
      torusRCTiltWeight hN hM q (translatedDualConfig A) := congrArg (fun k => torusNormalization q N M * Real.sqrt q.val ^ k)
    (rcLoopCount_translatedDual hN hM A)

end PottsDiscontinuity.TorusRC
