module
public import OAI.NumberTheory.DirichletL.Fourier.LogDensity
public import OAI.NumberTheory.DirichletL.CubicSieve.TwistedProfiles

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace SecondPassArithmetic

section


section
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label)
open JointLogSeparation (
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)

end

section
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label)
open JointLogSeparation (
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)

end

open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (columnLog jLabel b0Label)
open JointLogSeparation (tripleCoefficient frequencyTwist frequencyTwist_apply)

end

open JointLogSeparation (frequencyTwist frequencyTwist_apply)

end SecondPassArithmetic

namespace CanonicalQuadraticSieve

def HasSieveExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M * N) ^ ε * (M + N ^ α)

theorem hasSieveExponent_two : HasSieveExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N hM hN
  have hc : (⌈N⌉₊ : ℝ) ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ N by linarith)
    linarith
  have hc2 : (⌈N⌉₊ : ℝ) ^ 2 ≤ 4 * N ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌈N⌉₊]
  have hmn : 1 ≤ M * N := by nlinarith [mul_le_mul hM hN (by norm_num : (0 : ℝ) ≤ 1) (show 0 ≤ M by linarith)]
  have he : 1 ≤ (M * N) ^ ε := Real.one_le_rpow hmn hε.le
  rw [Real.rpow_two]
  calc
    _ ≤ C * (M + (⌈N⌉₊ : ℝ) ^ 2) := sieveNorm_initial M N hM hN
    _ ≤ 4 * C * (M + N ^ 2) := by nlinarith
    _ ≤ (4 * C) * (M * N) ^ ε * (M + N ^ 2) := by
      nlinarith [show 0 ≤ (4 * C) * (M + N ^ 2) by positivity]

theorem HasSieveExponent.reverse {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C * (M * N) ^ ε * (N + M ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨262144 * C, by positivity, ?_⟩
  intro M N hM hN
  calc
    _ ≤ 262144 * sieveNorm N M := sieveNorm_reverse_le M N
    _ ≤ 262144 * (C * (N * M) ^ ε * (N + M ^ α)) :=
      mul_le_mul_of_nonneg_left (hb N M hN hM) (by norm_num)
    _ = _ := by rw [mul_comm N M]; ring

theorem sqrt_divisor_sieve_pair_le (M N D₁ D₂ Q C : ℝ)
    (hN : 0 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (h₁ : sieveNorm M (N / D₁) ≤ C * (N / D₁ + Q))
    (h₂ : sieveNorm M (N / D₂) ≤ C * (N / D₂ + Q)) :
    Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
      C * (N + Q * (D₁ * D₂)) := by
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD₁le : D₁ ≤ D₁ * D₂ := by nlinarith
  have hD₂le : D₂ ≤ D₁ * D₂ := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ D₁ * D₂ * (C * (N / D₁ + Q)) * (C * (N / D₂ + Q)) := by
      gcongr
      exact sieveNorm_nonneg _ _
    _ = C ^ 2 * ((N + Q * D₁) * (N + Q * D₂)) := by field_simp
    _ ≤ C ^ 2 * ((N + Q * (D₁ * D₂)) * (N + Q * (D₁ * D₂))) := by gcongr
    _ = _ := by ring

theorem HasSieveExponent.divisor_pair {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N D₁ D₂ : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
      Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
        C * (M * N) ^ ε * (N + M ^ α * (D₁ * D₂)) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h.reverse ε hε
  refine ⟨C, hC, ?_⟩
  intro M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N
  have hbound (D : ℝ) (hD : 1 ≤ D) (hDN : D ≤ N) :
      sieveNorm M (N / D) ≤ (C * (M * N) ^ ε) * (N / D + M ^ α) := by
    have hD0 : 0 < D := by linarith
    have hND : 1 ≤ N / D := (le_div_iff₀ hD0).mpr (by simpa using hDN)
    apply (hb M (N / D) hM hND).trans
    have hprod : M * (N / D) ≤ M * N := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_self (by linarith) hD
    gcongr
  exact sqrt_divisor_sieve_pair_le M N D₁ D₂ (M ^ α) (C * (M * N) ^ ε)
    (by linarith) hD₁ hD₂ (Real.rpow_nonneg (by linarith) _) (by positivity)
    (hbound D₁ hD₁ hD₁N) (hbound D₂ hD₂ hD₂N)

open IdealCoprimeSieveOperator DivisorBlockCauchy

variable {n p : Type*} [Fintype n] [Fintype p]

def divisorEnergyFactor (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2 *
    Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ k, ‖b k‖ ^ 2)

theorem divisorEnergyFactor_nonneg (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) :
    0 ≤ divisorEnergyFactor ε hε N a b := by
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  positivity

theorem divisorBlockCost_sqrt (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) =
      divisorEnergyFactor ε hε N a b *
        Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) := by
  have hA := sieveNorm_nonneg M (N / D₁)
  have hB := sieveNorm_nonneg M (N / D₂)
  have hp : 0 ≤ D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) := by positivity
  have ha : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ∑ k, ‖b k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := by
    unfold divisorBlockCost
    positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (divisorEnergyFactor_nonneg ε hε N a b) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hc]
  simp only [divisorEnergyFactor, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hp]
  unfold divisorBlockCost
  ring
