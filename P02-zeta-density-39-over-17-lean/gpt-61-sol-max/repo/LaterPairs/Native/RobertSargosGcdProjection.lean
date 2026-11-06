module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosNormalizationCoordinates

@[expose] public section
set_option maxHeartbeats 0


                                                                         

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosGcdKey (p : RobertSargosPoint) : ℕ × ℕ :=
  (robertSargosCoefficientGcd p,robertSargosFrequencyGcd p)


