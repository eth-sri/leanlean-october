module

public import proofs.RAFCriticalWindowQuantitative.FiniteClosure
public import proofs.RAFCriticalWindowQuantitative.SeedDeficit
public import proofs.HordijkSteelThreshold.StaticEventContinuity

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

variable (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)

def rationalEventProbability
    (event : (J → Bool) → Bool) : ℚ :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0

/-- Exact probability semantics for an arbitrary executable Boolean event. -/
theorem rationalEventProbability_correct
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (event : (J → Bool) → Bool) :
    (Measure.pi (fun _ : J => ambientCoordLaw $ rationalParameter q hq hq1)
      {ω | event $ fun j => decide $ ω j}).toReal =
      (rationalEventProbability J q event : ℝ) := by
  let a := rationalParameter q hq hq1
  let μ := Measure.pi (fun _ : J => ambientCoordLaw a)
  let E : Set (J → Prop) := {ω | event $ fun j => decide $ ω j}
  let F : Finset (J → Prop) := Finset.univ.filter $ fun ω => ω ∈ E
  have hF : F = E := by grind
  have hatom ω : μ {ω} = (∏ j, staticAtomWeight a (ω j) : NNReal) := by
    rw [Measure.pi_singleton]
    simp only [ambientCoordLaw_atom, ENNReal.ofNNReal_finsetProd]
  have he : μ E = ((∑ ω ∈ F, ∏ j, staticAtomWeight a (ω j) : NNReal)) := by
    rw [← hF, ← sum_measure_singleton]
    simp_all
  rw [he]
  simp only [ENNReal.coe_toReal, NNReal.coe_sum]
  rw [Finset.sum_filter]
  let e : (J → Bool) ≃ (J → Prop) := Equiv.piCongrRight $ fun _ => Equiv.propEquivBool.symm
  rw [← e.sum_comp]
  have hw P : (staticAtomWeight a P) = if P then (q : ℝ) else 1-q := by
    by_cases hP : P <;> simp [staticAtomWeight,hP,a,rationalParameter]
  simp [rationalEventProbability,e,Equiv.propEquivBool,E]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hev : event ω = true
  · simp only [hev]
    push_cast
    apply Finset.prod_congr rfl
    aesop
  simp_all

end RAFCriticalWindowQuantitative
