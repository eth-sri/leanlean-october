module

public import proofs.RAFCriticalWindowQuantitative.FiniteClosure
public import proofs.RAFCriticalWindowQuantitative.SeedDeficit
public import proofs.HordijkSteelThreshold.StaticEventContinuity

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

def rationalEventProbability (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (event : (J → Bool) → Bool) : ℚ :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0

/-- Exact probability semantics for an arbitrary executable Boolean event. -/
theorem rationalEventProbability_correct (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (event : (J → Bool) → Bool) :
    ((Measure.pi (fun _ : J => ambientCoordLaw (rationalParameter q hq hq1)))
      {ω | event (fun j => decide (ω j))}).toReal =
      (rationalEventProbability J q event : ℝ) := by
  let e : (J → Bool) ≃ (J → Prop) := Equiv.piCongrRight fun _ => Equiv.propEquivBool.symm
  have hF : (Finset.univ.filter (fun ω : J → Prop => event (fun j => decide (ω j))) : Set (J → Prop)) =
      {ω | event (fun j => decide (ω j))} := by ext; simp
  rw [← hF, ← sum_measure_singleton, ENNReal.toReal_sum fun _ _ => by finiteness,
    Finset.sum_filter, ← e.sum_comp, rationalEventProbability, Rat.cast_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hw (j : J) : (ambientCoordLaw (rationalParameter q hq hq1) {ω j = true}).toReal =
      ↑(if ω j = true then q else 1 - q) := by
    cases ω j <;> simp [ambientCoordLaw, rationalParameter]
  cases hev : event ω <;> simp [e, Equiv.propEquivBool, hev, Measure.pi_singleton, ENNReal.toReal_prod, hw]

end RAFCriticalWindowQuantitative
