module
public import Mathlib

public import PottsDiscontinuity.TorusRC.TiltProbability

/-! # Complementary duality invariance of the tilted torus law -/

@[expose] public section




namespace PottsDiscontinuity.TorusRC

open Torus PottsDiscontinuity.SixVertex

variable {N M : ℕ}

private theorem translatedDualConfig_apply_nxt (A : RCConfig N M)
    (v : Fin N × Fin M) :
    translatedDualConfig A (nxt v.1, v.2) = Bool.not (A v) := by
  rw [translatedDualConfig, shiftRCConfig_nxt]
  rfl

/-- Translation followed by complementation is a bijection of indexed torus
configurations. Its inverse uses the opposite horizontal shift. -/
def translatedDualConfigEquiv : RCConfig N M ≃ RCConfig N M where
  toFun := translatedDualConfig
  invFun A := fun v => Bool.not (A (nxt v.1, v.2))
  left_inv A := by
    funext v
    change Bool.not (translatedDualConfig A (nxt v.1, v.2)) = A v
    rw [translatedDualConfig_apply_nxt]
    simp
  right_inv A := by
    funext v
    have h := translatedDualConfig_apply_nxt
      (fun w => Bool.not (A (nxt w.1, w.2))) (prv v.1, v.2)
    all_goals grind

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M))


private theorem torusRCTiltEventWeight_translatedDual
     :
    torusRCTiltEventWeight hN hM q E =
      torusRCTiltEventWeight hN hM q
        (translatedDualConfig ⁻¹' E) := by
  classical
  
  calc
     ∑ A, E.indicator (torusRCTiltWeight hN hM q) A  =
        ∑ A, E.indicator (torusRCTiltWeight hN hM q)
          (translatedDualConfigEquiv A) := Eq.symm (Equiv.sum_comp translatedDualConfigEquiv (E.indicator (torusRCTiltWeight hN hM q)))
    _ = ∑ A, (translatedDualConfig ⁻¹' E).indicator
          (torusRCTiltWeight hN hM q) A := by
      apply Finset.sum_congr rfl
      intro A _
      change (if translatedDualConfig A ∈ E then
          torusRCTiltWeight hN hM q (translatedDualConfig A) else 0) =
         if translatedDualConfig A ∈ E then torusRCTiltWeight hN hM q A else 0 
      by_cases hA : translatedDualConfig A ∈ E
      · simp only [hA]
        exact (torusRCTiltWeight_translatedDual hN hM q A).symm
      · simp only [hA, ite_false]

/-- The normalized self-dual tilt assigns the same probability to an event and
to its inverse image under translated complementary duality. -/
theorem torusRCTiltProbability_translatedDual  :
    torusRCTiltProbability hN hM q E =
      torusRCTiltProbability hN hM q (translatedDualConfig ⁻¹' E) := by
  grind [torusRCTiltProbability, torusRCTiltEventWeight_translatedDual]

/-- Translated complementary duality transfers a standard-law event bound with
the exact `q^2` loss used for the source's torus duality step. -/
theorem torusRCProbability_translatedDual_lower  :
    torusRCProbability hN hM q (translatedDualConfig ⁻¹' E) / q.val ^ 2 ≤
      torusRCProbability hN hM q E := by
  have hqpos  := lt_of_lt_of_le zero_lt_one q.property
  
  
  
  
  calc
    torusRCProbability hN hM q (translatedDualConfig ⁻¹' E) / q.val ^ 2 ≤
         q.val * torusRCTiltProbability hN hM q (translatedDualConfig ⁻¹' E)  /
          q.val ^ 2 :=
      div_le_div_of_nonneg_right (torusRCTiltProbability_comparison hN hM q
                                    (translatedDualConfig ⁻¹' E)).2 (pow_pos hqpos _).le
    _ = torusRCTiltProbability hN hM q E / q.val := by
      rw [ torusRCTiltProbability_translatedDual hN hM q E ]
      field_simp 
    _ ≤ torusRCProbability hN hM q E := (torusRCTiltProbability_comparison hN hM q E).1

end

end PottsDiscontinuity.TorusRC
