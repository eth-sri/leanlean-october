module

public import NearlyMinimax.Model
public import NearlyMinimax.Rates


@[expose] public section

/-!
Exact statistical statements from the current manuscript. The five `...Claim`
definitions below are propositions, not axioms. Separate statistical endpoint
modules use these definitions as their proof targets. Constants
in the high-smoothness claims precede the extension-domain quantifier, as the
paper requires.  The theorems in this file only assemble explicitly assumed
bounds and derive their analytic consequences.
-/

noncomputable section
open Filter Set
open scoped Topology ENNReal

namespace NearlyMinimax

/-- Only the open extension domain varies; the numerical model constants stay fixed. -/
structure ExtensionDomain (d : ℕ) where
  carrier : Set (Covariate d)
  isOpen : IsOpen carrier
  cube_subset : unitCube d ⊆ carrier

section
variable {d : ℕ} (C : ModelConstants d) {n : ℕ} (hn : 2 ≤ n)

def ModelConstants.originalDomain : ExtensionDomain d :=
  ⟨C.domain, C.domain_open, C.cube_subset⟩

def ModelConstants.withDomain
    (U : ExtensionDomain d) : ModelConstants d :=
  { C with domain := U.carrier, domain_open := U.isOpen, cube_subset := U.cube_subset }

def highSmoothnessRegime : Prop :=
  1 < C.smoothness ∧ 4 * C.smoothness < (d : ℝ)

/-- The density-ratio parameter in (main-constants). -/
def paperTau : ℝ :=
  Real.log ((Real.sqrt C.densityUpper + Real.sqrt C.densityLower) /
    (Real.sqrt C.densityUpper - Real.sqrt C.densityLower))

def paperPolynomialDimension : ℕ :=
  Nat.choose (d + C.order) d

def paperLogGap : ℝ :=
  (d : ℝ) * ((paperPolynomialDimension C : ℝ) - 1 / 2) / ((d : ℝ) + 4)

/-- Exactly the displayed lower scale `Psi_n`. -/
def paperRiskScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-rateExponent C.smoothness d) *
    Real.exp (-stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)) *
    (Real.log n) ^ lowerLogPower C.smoothness d

/-- The upper display uses the sum of the lower logarithmic power and `Gamma`. -/
def paperUpperScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-rateExponent C.smoothness d) *
    Real.exp (-stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)) *
    (Real.log n) ^ (lowerLogPower C.smoothness d + paperLogGap C)

include hn in
theorem paperUpperScale_eq :
    paperUpperScale C n = paperRiskScale C n * (Real.log n) ^ paperLogGap C := by
  unfold paperUpperScale paperRiskScale
  rw [Real.rpow_add (Real.log_pos (by norm_cast))]
  ring

include hn in
theorem paperRiskScale_eq_rateScale :
    paperRiskScale C n = rateScale (rateExponent C.smoothness d)
      (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d) n := by
  exact (rateScale_eq_rpow _ _ _ (by norm_cast)).symm

include hn in
theorem paperUpperScale_eq_rateScale :
    paperUpperScale C n = rateScale (rateExponent C.smoothness d)
      (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d + paperLogGap C) n := by
  exact (rateScale_eq_rpow _ _ _ (by norm_cast)).symm

include hn in
theorem paperRiskScale_pos :
    0 < paperRiskScale C n := by
  rw [paperRiskScale_eq_rateScale C hn]
  exact rateScale_pos ..

include hn in
theorem paperUpperScale_pos :
    0 < paperUpperScale C n := by
  rw [paperUpperScale_eq_rateScale C hn]
  exact rateScale_pos ..

end

section
variable {d : ℕ} (C : ModelConstants d)

/-- `thm:main` / `thm:bracket`, with the stated logarithmic gap. -/
def MainBracketClaim : Prop :=
  highSmoothnessRegime C →
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n ∧
        minimaxRMS (C.withDomain U) n ≤
          ENNReal.ofReal (A * paperRiskScale C n * (Real.log n) ^ paperLogGap C)

/-- The separate refined upper bound `thm:upper-sharp`. -/
def UpperSharpClaim : Prop :=
  highSmoothnessRegime C →
    ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        minimaxRMS (C.withDomain U) n ≤ ENNReal.ofReal (A * paperUpperScale C n)

/-- The separate lower bound `thm:lower`. -/
def LowerSharpClaim : Prop :=
  highSmoothnessRegime C →
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n

end

def lowSmoothnessScale (s : ℝ) (d n : ℕ) : ℝ :=
  max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(4 * s / ((d : ℝ) + 4 * s))))

section
variable {d : ℕ} (C : ModelConstants d)

/-- Pure assembly: this theorem assumes BOTH statistical claims. -/
theorem mainBracketClaim_of_separate_bounds
    (hupper : UpperSharpClaim C) (hlower : LowerSharpClaim C) : MainBracketClaim C := by
  intro hreg
  obtain ⟨A, hA, nU, hnU, hu⟩ := hupper hreg
  obtain ⟨c, hc, nL, hnL, hl⟩ := hlower hreg
  refine ⟨c, A, hc, hA, max nL nU, hnL.trans (le_max_left _ _), ?_⟩
  intro U n hn
  refine ⟨hl U n ((le_max_left _ _).trans hn), ?_⟩
  have hun := hu U n ((le_max_right _ _).trans hn)
  rw [paperUpperScale_eq C (by omega), ← mul_assoc] at hun
  exact hun

/-- Finiteness needed before translating extended-valued risk to a real number. -/
theorem minimaxRMS_finite (n : ℕ) :
    minimaxRMS C n < ∞ := ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ne_of_lt (minimaxRisk_finite C n))

/-- A claimed statistical bracket gives the explicit REAL rate-bracket hypothesis
used by the already-proved analytic corollaries. -/
theorem hasNatRateBracket_of_mainBracketClaim
    (hreg : highSmoothnessRegime C) (hmain : MainBracketClaim C) :
    HasNatRateBracket (fun n => (minimaxRMS C n).toReal)
      (rateExponent C.smoothness d) (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d) (paperLogGap C) := by
  obtain ⟨c, A, hc, hA, n₀, hn₀, hbound⟩ := hmain hreg
  refine ⟨c, A, hc, hA, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hb := hbound C.originalDomain n hn
  have hn2 := hn₀.trans hn
  have hlo := ENNReal.toReal_mono (ne_of_lt (minimaxRMS_finite C n)) hb.1
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.2
  rw [ENNReal.toReal_ofReal (mul_pos hc (paperRiskScale_pos C hn2)).le] at hlo
  rw [ENNReal.toReal_ofReal (by
    rw [mul_assoc, ← paperUpperScale_eq C hn2]
    positivity [paperUpperScale_pos C hn2]), mul_assoc, ← paperUpperScale_eq C hn2] at hhi
  rw [paperRiskScale_eq_rateScale C hn2] at hlo
  rw [paperUpperScale_eq_rateScale C hn2] at hhi
  tauto

end

/-- The larger of the upper constant and the reciprocal lower constant
works in both directions on every nonnegative rate scale. -/
theorem balance_rate_bounds {s : ℕ → ℝ} {R : ℕ → ℝ≥0∞} {b : ℝ}
    (hs : ∀ n, 1 ≤ n → 0 ≤ s n)
    (lo : ∃ c : ℝ, 0 < c ∧ ∀ n, 1 ≤ n → ENNReal.ofReal (c * s n) ≤ R n)
    (hi : ∀ n, 1 ≤ n → R n ≤ ENNReal.ofReal (b * s n)) :
    ∃ A : ℝ, 0 < A ∧ ∀ n, 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * s n) ≤ R n ∧ R n ≤ ENNReal.ofReal (A * s n) := by
  obtain ⟨c, hc, hl⟩ := lo
  refine ⟨max b c⁻¹, (inv_pos.mpr hc).trans_le (le_max_right ..), fun n hn =>
    ⟨le_trans ?_ (hl n hn), (hi n hn).trans ?_⟩⟩
  all_goals apply ENNReal.ofReal_le_ofReal; apply mul_le_mul_of_nonneg_right _ (hs n hn)
  · exact inv_le_of_inv_le₀ hc (le_max_right ..)
  · exact le_max_left ..

end NearlyMinimax
