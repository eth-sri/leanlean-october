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
variable {d : ℕ} (C : ModelConstants d)
include C

def ModelConstants.originalDomain  : ExtensionDomain d :=
  ⟨C.domain, C.domain_open, C.cube_subset⟩

def ModelConstants.withDomain 
    (U : ExtensionDomain d)  :=
  { C with domain := U.carrier, domain_open := U.isOpen, cube_subset := U.cube_subset }

theorem ModelConstants.withDomain_original  :
    C.withDomain C.originalDomain = C := rfl

def highSmoothnessRegime   :=
  1 < C.smoothness ∧ 4 * C.smoothness < (d : ℝ)
end


/-- The density-ratio parameter in (main-constants). -/
def paperTau {d } (C : ModelConstants d)  :=
  Real.log ((Real.sqrt C.densityUpper + Real.sqrt C.densityLower) /
    (Real.sqrt C.densityUpper - Real.sqrt C.densityLower))

section
variable {d : ℕ} (C : ModelConstants d)
include C

def paperPolynomialDimension   :=
  Nat.choose (d + C.order) d

def paperLogGap   :=
  (d : ℝ) * ((paperPolynomialDimension C : ℝ) - 1 / 2) / ((d : ℝ) + 4)

/-- Exactly the displayed lower scale `Psi_n`. -/
def paperRiskScale  (n : ℕ)  :=
  (n : ℝ) ^ (-rateExponent C.smoothness d) *
    Real.exp (-stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)) *
    (Real.log n) ^ lowerLogPower C.smoothness d

/-- The upper display uses the sum of the lower logarithmic power and `Gamma`. -/
def paperUpperScale  (n : ℕ)  :=
  (n : ℝ) ^ (-rateExponent C.smoothness d) *
    Real.exp (-stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)) *
    (Real.log n) ^ (lowerLogPower C.smoothness d + paperLogGap C)

section
variable {n : ℕ} (hn : 2 ≤ n)
include hn

theorem paperUpperScale_eq   :
    paperUpperScale C n = paperRiskScale C n * (Real.log n) ^ paperLogGap C := by
  have hnreal : (1 : ℝ) < n := by measurability
  unfold paperUpperScale paperRiskScale
  rw [Real.rpow_add (Real.log_pos hnreal)]
  ring

theorem paperRiskScale_eq_rateScale 
     :
    paperRiskScale C n = rateScale (rateExponent C.smoothness d)
      (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d) n := by
  have hnreal : (1 : ℝ) < n := by measurability
  exact (rateScale_eq_rpow _ _ _ hnreal).symm

theorem paperUpperScale_eq_rateScale 
     :
    paperUpperScale C n = rateScale (rateExponent C.smoothness d)
      (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d + paperLogGap C) n := by
  have hnreal : (1 : ℝ) < n := by measurability
  exact (rateScale_eq_rpow _ _ _ hnreal).symm

theorem paperRiskScale_pos   :
    0 < paperRiskScale C n := by
  rw [paperRiskScale_eq_rateScale C hn]
  exact rateScale_pos _ _ _ _

theorem paperUpperScale_pos   :
    0 < paperUpperScale C n := by
  rw [paperUpperScale_eq_rateScale C hn]
  exact rateScale_pos _ _ _ _
end


/-- `thm:main` / `thm:bracket`, with the stated logarithmic gap. -/
def MainBracketClaim   :=
  highSmoothnessRegime C →
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n ∧
        minimaxRMS (C.withDomain U) n ≤
          ENNReal.ofReal (A * paperRiskScale C n * (Real.log n) ^ paperLogGap C)

/-- The separate refined upper bound `thm:upper-sharp`. -/
def UpperSharpClaim   :=
  highSmoothnessRegime C →
    ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        minimaxRMS (C.withDomain U) n ≤ ENNReal.ofReal (A * paperUpperScale C n)

/-- The separate lower bound `thm:lower`. -/
def LowerSharpClaim   :=
  highSmoothnessRegime C →
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n
end


def lowSmoothnessScale s (d n : ℕ)  :=
  max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(4 * s / ((d : ℝ) + 4 * s))))

section
variable {d : ℕ} (C : ModelConstants d)
include C

/-- `thm:main2`, the exact low-smoothness bracket for every `n≥1`. -/
def LowSmoothnessClaim   :=
  C.smoothness ≤ 1 → ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
    ENNReal.ofReal (A⁻¹ * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n ∧
    minimaxRMS C n ≤ ENNReal.ofReal (A * lowSmoothnessScale C.smoothness d n)

/-- `thm:parametric`, with its stated `s>1` hypothesis. -/
def ParametricClaim   :=
  1 < C.smoothness → (d : ℝ) ≤ 4 * C.smoothness →
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n ∧
      minimaxRMS C n ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-(1 / 2 : ℝ)))

/-- Pure assembly: this theorem assumes BOTH statistical claims. -/
theorem mainBracketClaim_of_separate_bounds 
    (hupper : UpperSharpClaim C) (hlower : LowerSharpClaim C) : MainBracketClaim C := by
  intro hreg
  obtain ⟨A, hA, nU, hnU, hu⟩ := hupper hreg
  obtain ⟨c, hc, nL, hnL, hl⟩ := hlower hreg
  refine ⟨c, A, hc, hA, max nL nU, hnL.trans (le_max_left _ _), ?_⟩
  intro U n hn
  grind only [le_max_left, le_max_right, paperUpperScale_eq]

/-- Finiteness needed before translating extended-valued risk to a real number. -/
theorem minimaxRMS_finite  n :
    minimaxRMS C n < ∞ := ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (ne_of_lt (minimaxRisk_finite C n))

section
variable (hreg : highSmoothnessRegime C) (hmain : MainBracketClaim C)
include hreg hmain

/-- A claimed statistical bracket gives the explicit REAL rate-bracket hypothesis
used by the already-proved analytic corollaries. -/
theorem hasNatRateBracket_of_mainBracketClaim 
     :
    HasNatRateBracket (fun n => (minimaxRMS C n).toReal)
      (rateExponent C.smoothness d) (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d) (paperLogGap C) := by
  obtain ⟨c, A, hc, hA, n₀, hn₀, hbound⟩ := hmain hreg
  refine ⟨c, A, hc, hA, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hb := hbound C.originalDomain n hn
  rw [C.withDomain_original] at hb
  have hn2 := hn₀.trans hn
  have hfin  := ne_of_lt (minimaxRMS_finite C n)
  have hlo := ENNReal.toReal_mono hfin hb.1
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.2
  rw [ENNReal.toReal_ofReal (mul_pos hc (paperRiskScale_pos C hn2)).le] at hlo
  have hu : 0 ≤ A * paperRiskScale C n * (Real.log n) ^ paperLogGap C := by
    rw [mul_assoc, ← paperUpperScale_eq C hn2]
    exact (mul_pos hA (paperUpperScale_pos C hn2)).le
  rw [ENNReal.toReal_ofReal hu, mul_assoc, ← paperUpperScale_eq C hn2] at hhi
  rw [paperRiskScale_eq_rateScale C hn2] at hlo
  rw [paperUpperScale_eq_rateScale C hn2] at hhi
  exact ⟨hlo, hhi⟩

/-- Conditional exponent limit; it does not establish the assumed main bracket. -/
theorem paper_exponent_limit_of_mainBracketClaim 
     :
    Tendsto (fun n  => -Real.log (minimaxRMS C n).toReal / Real.log n)
      atTop (𝓝 (rateExponent C.smoothness d)) :=
  exponent_limit_nat_of_rateBracket (hasNatRateBracket_of_mainBracketClaim C hreg hmain)
end

end


end NearlyMinimax
