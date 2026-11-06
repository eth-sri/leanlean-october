module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.RectangleInfiniteComparison
public import PottsDiscontinuity.TorusLoops.RectangleOneArmComparison

/-!
# Rooted one-arm probabilities in the canonical free limit

Finite free origin boxes are dominated by the free-limit probability of a
one-arm event rooted at any fixed lattice vertex. Translation invariance of the
free limit then identifies that probability with the origin one-arm probability.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.FK.Internal
open PottsDiscontinuity.Zhang

noncomputable section

/-- The coordinate one-arm event rooted at `a`, represented by translating the
configuration so that `a` becomes the origin. -/
def translatedOneArmEvent (a : LatticeVertex) (k : ℕ)  :=
   latticeConfigurationTranslationHomeomorph (-a)  ⁻¹' oneArmEvent k

/-- Translated finite-witness approximations to a rooted one-arm event. -/
def translatedFreeOneArmApprox (a : LatticeVertex) (k n : ℕ)  :=
   latticeConfigurationTranslationHomeomorph (-a)  ⁻¹' freeOneArmApprox k n

section

variable (a : LatticeVertex)


theorem translatedFreeOneArmApprox_mono  (k : ℕ) :
    Monotone (translatedFreeOneArmApprox a k) := fun n m hnm ω hω => freeOneArmApprox_mono k hnm hω

theorem translatedFreeOneArmApprox_isClopen  (k n : ℕ) :
    IsClopen (translatedFreeOneArmApprox a k n) :=
  by
    solve_by_elim [_root_.IsClopen.preimage, _root_.PottsDiscontinuity.TorusLoops.freeOneArmApprox_isClopen, _root_.Homeomorph.continuous]

theorem translatedFreeOneArmApprox_isUpperSet  (k n : ℕ) :
    IsUpperSet (translatedFreeOneArmApprox a k n) := by
  intro ω η hωη hω
  change latticeConfigurationTranslate (-a) ω ∈ freeOneArmApprox k n at hω
  
  change latticeConfigurationTranslate (-a) η ∈ freeOneArmApprox k n
  exact freeOneArmApprox_isUpperSet k n (by
                                           intro e
                                           aesop) hω

theorem iUnion_translatedFreeOneArmApprox  (k : ℕ) :
     ⋃ n, translatedFreeOneArmApprox a k n  = translatedOneArmEvent a k := by
  ext ω
  simp only [translatedFreeOneArmApprox, translatedOneArmEvent,
    Set.mem_iUnion, Set.mem_preimage]
  rw [← iUnion_freeOneArmApprox k]
  simp only [Set.mem_iUnion]

end

private theorem tendsto_translatedFreeOneArmApprox_probability
    (ν : ProbabilityMeasure LatticeConfiguration) (a : LatticeVertex) (k : ℕ) :
    Tendsto (fun n : ℕ => ν.toFiniteMeasure (translatedFreeOneArmApprox a k n)) atTop
      (𝓝 (ν.toFiniteMeasure (translatedOneArmEvent a k))) := by
  have hacc (n : ℕ) :
      Set.accumulate (translatedFreeOneArmApprox a k) n =
        translatedFreeOneArmApprox a k n := by
    ext ω
    rw [Set.mem_accumulate]
    constructor
    · rintro ⟨m, hmn, hm⟩
      exact translatedFreeOneArmApprox_mono a k hmn hm
    · aesop
  have h := ν.toFiniteMeasure.tendsto_measure_iUnion_accumulate
    (f := translatedFreeOneArmApprox a k)
  have h' : Tendsto
      (fun n => ν.toFiniteMeasure (translatedFreeOneArmApprox a k n)) atTop
      (𝓝 (ν.toFiniteMeasure (⋃ n, translatedFreeOneArmApprox a k n))) := by
    simp_all
  simpa [iUnion_translatedFreeOneArmApprox] using h'

/-- Every free origin-box probability of a rooted one-arm event is bounded by
its probability in the canonical free limit. -/
theorem boxProbabilityMeasure_translatedOneArm_le_freeBoxLimit
    (q : Parameters) (r : ℕ) (a : LatticeVertex) (k : ℕ) :
    boxProbabilityMeasure q (0, 0) r (translatedOneArmEvent a k) ≤
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (translatedOneArmEvent a k) := by
  let μ  :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  let ν  := boxProbabilityMeasure q (0, 0) r
  
  
  have hle (n : ℕ)  :=
    freeBoxLimit_clopen_upper_ge_box q r (translatedFreeOneArmApprox a k n)
      (translatedFreeOneArmApprox_isClopen a k n)
      (translatedFreeOneArmApprox_isUpperSet a k n)
  
  simpa only [FiniteMeasure.self_eq_mass_mul_normalize, ProbabilityMeasure.mass_toFiniteMeasure, ProbabilityMeasure.toFiniteMeasure_normalize_eq_self, one_mul, μ] using  le_of_tendsto_of_tendsto' (tendsto_translatedFreeOneArmApprox_probability ν a k) (tendsto_translatedFreeOneArmApprox_probability μ a k) hle 

/-- Translation invariance identifies a rooted one-arm probability in the
canonical free limit with the probability rooted at the origin. -/
theorem freeBoxLimit_translatedOneArm_probability_eq (q : Parameters)
    (a : LatticeVertex) (k : ℕ) :
    (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (translatedOneArmEvent a k) =
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (oneArmEvent k) := by
  let μ  :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hinv := freeBoxLimit_translation_invariant q (-a)
  have hinv' : ProbabilityMeasure.map μ
      (latticeConfigurationTranslationHomeomorph (-a)).toFun = μ := by
    assumption
  
  have hEval := congrArg
    (fun ν  => ν (oneArmEvent k)) hinv'
  rw [ ProbabilityMeasure.map_apply μ
          (latticeConfigurationTranslationHomeomorph (-a)).continuous_toFun.measurable.aemeasurable 
         (measurableSet_oneArmEvent k) ] at hEval
  simpa only [translatedOneArmEvent, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, μ] using hEval

end
end PottsDiscontinuity.TorusLoops
