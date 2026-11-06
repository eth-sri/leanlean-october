module

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

section
variable (a : LatticeVertex)
/-- The coordinate one-arm event rooted at `a`, represented by translating the
configuration so that `a` becomes the origin. -/
def translatedOneArmEvent (k : ℕ) : Set LatticeConfiguration :=
  (latticeConfigurationTranslationHomeomorph (-a)) ⁻¹' oneArmEvent k

/-- Translated finite-witness approximations to a rooted one-arm event. -/
def translatedFreeOneArmApprox (k n : ℕ) :
    Set LatticeConfiguration :=
  (latticeConfigurationTranslationHomeomorph (-a)) ⁻¹' freeOneArmApprox k n

theorem translatedFreeOneArmApprox_mono (k : ℕ) :
    Monotone (translatedFreeOneArmApprox a k) := by
  intro n m hnm ω hω
  exact freeOneArmApprox_mono k hnm hω

theorem translatedFreeOneArmApprox_isClopen (k n : ℕ) :
    IsClopen (translatedFreeOneArmApprox a k n) :=
  (freeOneArmApprox_isClopen k n).preimage
    (latticeConfigurationTranslationHomeomorph (-a)).continuous

theorem translatedFreeOneArmApprox_isUpperSet (k n : ℕ) :
    IsUpperSet (translatedFreeOneArmApprox a k n) := by
  intro ω η hωη hω
  have htranslated : latticeConfigurationTranslate (-a) ω ≤
      latticeConfigurationTranslate (-a) η := by
    intro e
    aesop
  exact freeOneArmApprox_isUpperSet k n htranslated hω

theorem iUnion_translatedFreeOneArmApprox (k : ℕ) :
    (⋃ n, translatedFreeOneArmApprox a k n) = translatedOneArmEvent a k := by
  simp only [translatedFreeOneArmApprox, translatedOneArmEvent]
  rw [← iUnion_freeOneArmApprox k]
  simp
end

theorem tendsto_translatedFreeOneArmApprox_probability
    (ν : ProbabilityMeasure LatticeConfiguration) (a : LatticeVertex) (k : ℕ) :
    Tendsto (fun n : ℕ => ν.toFiniteMeasure (translatedFreeOneArmApprox a k n)) atTop
      (𝓝 (ν.toFiniteMeasure (translatedOneArmEvent a k))) := by
  have hacc (n : ℕ) :
      Set.accumulate (translatedFreeOneArmApprox a k) n =
        translatedFreeOneArmApprox a k n := by
    ext ω
    simp
    constructor
    · rintro ⟨m, hmn, hm⟩
      exact translatedFreeOneArmApprox_mono a k hmn hm
    grind
  have h := ν.toFiniteMeasure.tendsto_measure_iUnion_accumulate
    (f := translatedFreeOneArmApprox a k)
  grind [Tendsto, translatedFreeOneArmApprox, atTop, iUnion_translatedFreeOneArmApprox]

section
variable (q : Parameters)
/-- Every free origin-box probability of a rooted one-arm event is bounded by
its probability in the canonical free limit. -/
theorem boxProbabilityMeasure_translatedOneArm_le_freeBoxLimit
    (r : ℕ) (a : LatticeVertex) (k : ℕ) :
    boxProbabilityMeasure q (0, 0) r (translatedOneArmEvent a k) ≤
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (translatedOneArmEvent a k) := by
  let μ :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  let ν := boxProbabilityMeasure q (0, 0) r
  have hle (n : ℕ) :=
    freeBoxLimit_clopen_upper_ge_box q r (translatedFreeOneArmApprox a k n)
      (translatedFreeOneArmApprox_isClopen a k n)
      (translatedFreeOneArmApprox_isUpperSet a k n)
  have h := le_of_tendsto_of_tendsto' (tendsto_translatedFreeOneArmApprox_probability ν a k) (tendsto_translatedFreeOneArmApprox_probability μ a k) hle
  tauto

/-- Translation invariance identifies a rooted one-arm probability in the
canonical free limit with the probability rooted at the origin. -/
theorem freeBoxLimit_translatedOneArm_probability_eq (a : LatticeVertex) (k : ℕ) :
    (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (translatedOneArmEvent a k) =
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (oneArmEvent k) := by
  let μ :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hinv := freeBoxLimit_translation_invariant q (-a)
  have hinv' : ProbabilityMeasure.map μ
      (latticeConfigurationTranslationHomeomorph (-a)).toFun = μ := by
    tauto
  have hmap := ProbabilityMeasure.map_apply μ
    ((latticeConfigurationTranslationHomeomorph (-a)).continuous_toFun.measurable.aemeasurable)
    (measurableSet_oneArmEvent k)
  have hEval := congrArg
    (fun ν : ProbabilityMeasure LatticeConfiguration => ν (oneArmEvent k)) hinv'
  rw [hmap] at hEval
  tauto
end

end
end PottsDiscontinuity.TorusLoops
