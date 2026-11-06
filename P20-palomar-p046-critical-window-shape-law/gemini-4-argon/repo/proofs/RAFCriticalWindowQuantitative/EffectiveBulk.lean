module

public import proofs.RAFCriticalWindowQuantitative.SeedDeficit

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

theorem effective_static_bulk (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    ∀ N : ℕ, 0 < N →
      staticReactionMeasure N a {ω |
        m*(temporaryReactionClosure (10*k) (staticOpenReactions ω)).card <
          (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  let a := rationalParameter b hb.le hb1
  let η : ENNReal := (m : ENNReal)⁻¹/(m+1)
  let k := seedIndex b hb hb1 m
  have hk : 0 < k := (seedIndex_spec b hb hb1 m).1
  have hbound : contourBudget a k / (1 - contourBudget a k) ≤ η := by
    simpa [η, div_eq_mul_inv, ENNReal.mul_inv] using selected_contour_deficit b hb hb1 m hm
  intro N hN
  let U := Fintype.card (Molecule N)
  let d := U/m+1
  have hd : 0 < d := Nat.succ_pos _
  have hUd : (U : ENNReal) ≤ (m : ENNReal)*d :=
    by exact_mod_cast (by have := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self (U/m)); dsimp [d]; nlinarith : U ≤ m*d)
  refine (measure_mono (t := {ω | (temporaryReactionClosure (10*k) (staticOpenReactions ω)).card+d ≤ U}) fun ω hω => ?_).trans ?_
  · have := Nat.div_mul_le_self U m
    change m*(temporaryReactionClosure (10*k) (staticOpenReactions ω)).card < (m-1)*U at hω
    dsimp [d]; nlinarith [show m-1+1 = m by omega]
  · calc
      _ ≤ η + ((m : ENNReal)*d)*η/d :=
        (measure_temporaryClosure_deficit (w := 5*k) (k := k) (by omega) (by omega) (by omega) hN a d hd).trans (by gcongr)
      _ = (m : ENNReal)⁻¹ := by
        rw [mul_right_comm (m : ENNReal) d η, ENNReal.mul_div_cancel_right (by exact_mod_cast Nat.ne_of_gt hd) (by simp),
          ← one_add_mul, add_comm 1 (m : ENNReal)]
        exact ENNReal.mul_div_cancel (by simp) (by simp)

end RAFCriticalWindowQuantitative
