module

public import ImprovedExponents.Pipeline.HostBound
public import ImprovedExponents.ParamRoutines.Spec

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec ParamRoutines

/-- Theorem 17 at rational exponents, charging each call at the true middle-part size. -/
def MidHostRat (M : DetTimeModel) : Prop :=
  ∀ a b c d : ℕ, 1 ≤ b → 1 ≤ d → a ≤ 2 * b → c ≤ 3 * d →
    HostBound M strassen (paramDRat a b) (paramGRatOf a b c d)
      (fun n => pieceSizeNat (paramDRat a b n) (paramGRatOf a b c d n)
        * Nat.sqrt (paramDRat a b n))

end ImprovedExponents
