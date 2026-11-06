module
public import Mathlib

public import PottsDiscontinuity.Torus.DualLoopTransport
public import PottsDiscontinuity.Torus.RCWeight

/-! # The self-dual torus weight used in the crossing argument -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

/-- The source's self-dual weight: the standard RC loop weight with the
`q^s` net correction removed. Its normalized law is the measure denoted
`\widetilde φ_T` in the proof of (3.15). -/
noncomputable def torusRCTiltWeight (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M)  :=
  torusNormalization q N M * Real.sqrt q.val ^ rcLoopCount hN hM A

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (A : RCConfig N M)


theorem torusRCTiltWeight_eq_standard_div_net  :
    torusRCTiltWeight hN hM q A =
      torusRCWeight hN hM q A / q.val ^ rcNetIndicator hN hM A := by
  have hq : q.val =  Real.sqrt q.val  ^ 2 := by
    grind
  have hpow : q.val ^ rcNetIndicator hN hM A =
      Real.sqrt q.val ^ (2 * rcNetIndicator hN hM A) := by
    calc
      q.val ^ rcNetIndicator hN hM A =
          ( Real.sqrt q.val  ^ 2) ^ rcNetIndicator hN hM A :=
        congrArg (fun t  => t ^ rcNetIndicator hN hM A) hq
      _ = Real.sqrt q.val ^ (2 * rcNetIndicator hN hM A) := by rw [pow_mul]
  have hroot  :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.property)
  
  rw [torusRCTiltWeight, torusRCWeight_eq_loopWeight hN hM q A, hpow]
  rw [pow_add]
  field_simp 

/-- The tilted weight is invariant under the translated complementary duality. -/
theorem torusRCTiltWeight_translatedDual  :
    torusRCTiltWeight hN hM q A =
      torusRCTiltWeight hN hM q (translatedDualConfig A) := congrArg (fun k => torusNormalization q N M * √↑q ^ k) (rcLoopCount_translatedDual hN hM A)

end

end PottsDiscontinuity.TorusRC
