module

public import PottsDiscontinuity.SixVertex.InfinityEndpointOrder
public import PottsDiscontinuity.SixVertex.InfinitySorting

/-! # The finite canonical weight equals the labelled lifted weight -/

public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N k : ℕ}

section
variable (hN : 0 < N)
include hN
theorem sineLiftWeight_canonical_cyclic (s : Finset (Fin N)) (hs : s.card = k) (u : Fin k → ℤ) (hu : StrictMono u)
    (f : Fin k → Fin N) (hmem : ∀ a, f a ∈ s)
    (hf : ∀ a, ((f a).val : ℤ) = if u a < 0 then u a + N
      else if (N : ℤ) ≤ u a then u a - N else u a)
    (hlo : ∀ a, -1 ≤ u a) (hhi : ∀ a, u a ≤ N)
    (hspan : ∀ a b, u b - u a < N) :
    sineLiftWeight ((N : ℝ) + k) (orderedSiteLift s hs) =
      sineLiftWeight ((N : ℝ) + k) (fun a => u a + a.val) := by
  cases k with
  | zero => rfl
  | succ k =>
    by_cases hleft : u 0 < 0
    · have h0 : u 0 = -1 := by have := hlo 0; omega
      have hb : ∀ a : Fin k, u a.succ < (N : ℤ) - 1 := by
        intro a
        have hh := hspan 0 a.succ
        omega
      have hlow : ∀ a : Fin k, 0 ≤ u a.succ := by
        intro a
        have hh := hu (show (0 : Fin (k + 1)) < a.succ by simp)
        omega
      apply sineLiftWeight_canonical_left_wrap hN s hs u hu h0 f hmem
      · grind
      · intro a
        have hh := hf a.succ
        have h1 := hlow a
        have h2 := hb a
        omega
      omega
    · by_cases hright : (N : ℤ) ≤ u (Fin.last k)
      · have hl : u (Fin.last k) = N := by grind
        have hb : ∀ a : Fin k, 0 < u a.castSucc := by
          intro a
          have hh := hspan a.castSucc (Fin.last k)
          omega
        have hup : ∀ a : Fin k, u a.castSucc < N := by
          intro a
          have hh := hu (Fin.castSucc_lt_last a)
          omega
        apply sineLiftWeight_canonical_right_wrap hN s hs u hu hl f hmem
        · simp_all
        · intro a
          have hh := hf a.castSucc
          have h1 := hb a
          have h2 := hup a
          omega
        omega
      · apply sineLiftWeight_canonical_no_wrap s hs u hu f hmem
        intro a
        have hlow := hu.monotone (show (0 : Fin (k + 1)) ≤ a from Fin.zero_le a)
        have hupp := hu.monotone (Fin.le_last a)
        grind

/-- Exact equality of the actual upper state's canonical weight and the labelled
step weight. This includes both possible seam crossings. -/
theorem defectGroundWeight_upper_eq_lift {x : Finset (Fin N)}
    (hx : NoConsecutiveUp x) (d : Fin (defects x).card → Bool)
    (ha : AdmissibleDefectChoice x (indexedDefectChoice x d)) :
    defectGroundWeight (upperOfHorizontal (horizontalOfDefectChoice x (indexedDefectChoice x d))) =
      sineLiftWeight ((N : ℝ) + (defects x).card) (leftStepLift (orderedDefectLift x) d) := by
  rw [defectGroundWeight_eq_orderedSiteLift _ (card_upper_defects_choice hx d ha),
    leftStepLift_eq_endpointLift]
  exact sineLiftWeight_canonical_cyclic hN _ _ (choiceEndpointLift x d)
    (choiceEndpointLift_strictMono hx d ha) (choiceEndpoint x d)
    (choiceEndpoint_mem hx d ha) (choiceEndpoint_val x d)
    (fun a => (choiceEndpointLift_bounds x d a).1)
    (fun a => (choiceEndpointLift_bounds x d a).2) (choiceEndpointLift_span hN hx d ha)
end

/-- The original candidate agrees with the sine product on its canonical integer lift. -/
theorem defectGroundWeight_eq_lift (x : Finset (Fin N)) :
    defectGroundWeight x = sineLiftWeight ((N : ℝ) + (defects x).card) (orderedDefectLift x) := by
  rfl

end PottsDiscontinuity.SixVertex
