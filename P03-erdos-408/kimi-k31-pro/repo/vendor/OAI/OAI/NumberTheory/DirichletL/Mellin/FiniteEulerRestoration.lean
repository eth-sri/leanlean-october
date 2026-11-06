module

public import OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid




namespace CompactMellinBridge

structure BaseChangeCompactTest
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) where
  W : ℝ → ℂ
  F : ℝ → ℂ
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_lt : sigma < ρ.re
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W
  support : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0
  sum_eq : ∀ t : ℝ, 0 < t →
    HasSum (fun n : ℕ =>
      ShortDraftHeckeBridge.normFiberCoeff
        (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)) (F t)
  term_integrable : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)))
      (Set.Ioi 0)
  fubini : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
    ∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t))‖)
  locally_integrable : LocallyIntegrableOn
    (fun D : ℝ => F D⁻¹) (Set.Ioi 0)
  power_bound : (fun D : ℝ => F D⁻¹) =O[atTop]
    (fun D : ℝ => D ^ sigma)
  mellin_nonzero : mellin W ρ ≠ 0

end CompactMellinBridge

end

end OAI
