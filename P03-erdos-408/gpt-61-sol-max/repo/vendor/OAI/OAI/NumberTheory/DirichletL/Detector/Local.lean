module
public import Mathlib.Tactic

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

def localFactor (V W Pstar : ℂ)  := 1 / (1 - V) + W / (1 - W) + Pstar

def localCorrection (V W D Pstar : ℂ)  :=
  localFactor V W Pstar * ((1 - V) * (1 - W)) / (1 - D)

def continuedCorrection (V W D Pstar : ℂ)  :=
  (1 - V * W + (1 - V) * (1 - W) * Pstar) / (1 - D)

theorem continuedCorrection_eq_raw  V W D Pstar 
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar = localCorrection V W D Pstar := by
  unfold continuedCorrection localCorrection localFactor
  field_simp
  ring

def compensatedReplacement (V W D Pstar B q : ℂ)  :=
  ((B - q) * (1 - V) * (1 - W) * Pstar - q * (1 - V * W)) / (1 - D)

section
variable (V W D Pstar B q vInv : ℂ) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)

include hV hW hD in
theorem compensatedReplacement_eq_raw  
         
    (hP : localFactor V W Pstar ≠ 0) :
    compensatedReplacement V W D Pstar B q =
      localCorrection V W D Pstar * (B * Pstar / localFactor V W Pstar - q) := by
  unfold localCorrection compensatedReplacement
  field_simp
  unfold localFactor
  field_simp
  ring

include hD in
theorem continuedCorrection_defect     :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

include hV hD in
theorem continued_normalized_cancellation  
       
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  grind

theorem continued_ramified_compensation   :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * continuedCorrection V 0 0 Pstar := by
  grind [compensatedReplacement, continuedCorrection]

end

end
end SevenEighths.ProbeLocal

end OAI
