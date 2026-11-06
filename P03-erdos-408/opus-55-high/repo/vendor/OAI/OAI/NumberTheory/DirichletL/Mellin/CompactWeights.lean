module

public import OAI.NumberTheory.DirichletL.Mellin.CompactScale

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open Finset Complex
open Filter Real Asymptotics
open Filter
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory

namespace CompactScaleBridge

section


end

open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

end CompactScaleBridge

open Filter Asymptotics MeasureTheory

namespace ConcreteCompactWeight

def bumpData : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩


def positiveExtension (y : ℝ) : ℝ :=
  1 + (y - 1) * Real.smoothTransition (2 * y - 1)

theorem positiveExtension_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) positiveExtension := by
  unfold positiveExtension
  have ht : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => 2 * y - 1) := by fun_prop
  exact contDiff_const.add
    ((contDiff_id.sub contDiff_const).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp ht))

theorem positiveExtension_pos (y : ℝ) : 0 < positiveExtension y := by
  unfold positiveExtension
  by_cases hhalf : y ≤ 1 / 2
  · have ht : 2 * y - 1 ≤ 0 := by linarith
    simp [Real.smoothTransition.zero_of_nonpos ht]
  · by_cases hone : 1 ≤ y
    · have ht : 1 ≤ 2 * y - 1 := by linarith
      rw [Real.smoothTransition.one_of_one_le ht]
      linarith
    · have hle := Real.smoothTransition.le_one (2 * y - 1)
      nlinarith

theorem positiveExtension_eq (y : ℝ) (hy : 1 ≤ y) :
    positiveExtension y = y := by
  unfold positiveExtension
  simp [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * y - 1)]


end ConcreteCompactWeight

namespace CompactScaleBridge

section


end

end CompactScaleBridge

namespace ActualEisensteinCubic


end ActualEisensteinCubic

namespace TwoPassProfiles

end TwoPassProfiles

end

end OAI
