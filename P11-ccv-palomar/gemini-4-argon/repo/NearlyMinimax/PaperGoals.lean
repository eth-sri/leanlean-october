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


variable {d n : ℕ}
/-- Only the open extension domain varies; the numerical model constants stay fixed. -/
structure ExtensionDomain (d : ℕ) where
  carrier : Set (Covariate d)
  isOpen : IsOpen carrier
  cube_subset : unitCube d ⊆ carrier

def ModelConstants.originalDomain  (C : ModelConstants d) : ExtensionDomain d :=
  ⟨C.domain, C.domain_open, C.cube_subset⟩

def ModelConstants.withDomain  (C : ModelConstants d)
    (U : ExtensionDomain d) : ModelConstants d :=
  { C with domain := U.carrier, domain_open := U.isOpen, cube_subset := U.cube_subset }

theorem ModelConstants.withDomain_original  (C : ModelConstants d) :
    C.withDomain C.originalDomain = C := rfl

def highSmoothnessRegime {d : ℕ} (C : ModelConstants d) : Prop :=
  1 < C.smoothness ∧ 4 * C.smoothness < (d : ℝ)

/-- The density-ratio parameter in (main-constants). -/
def paperTau {d : ℕ} (C : ModelConstants d) : ℝ :=
  Real.log ((Real.sqrt C.densityUpper + Real.sqrt C.densityLower) /
    (Real.sqrt C.densityUpper - Real.sqrt C.densityLower))

def paperPolynomialDimension {d : ℕ} (C : ModelConstants d) : ℕ :=
  Nat.choose (d + C.order) d

def paperLogGap {d : ℕ} (C : ModelConstants d) : ℝ :=
  (d : ℝ) * ((paperPolynomialDimension C : ℝ) - 1 / 2) / ((d : ℝ) + 4)

/-- Exactly the displayed lower scale `Psi_n`. -/
def paperRiskScale {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-rateExponent C.smoothness d) *
    Real.exp (-stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)) *
    (Real.log n) ^ lowerLogPower C.smoothness d

/-- The upper display uses the sum of the lower logarithmic power and `Gamma`. -/
def paperUpperScale  (C : ModelConstants d) (n : ℕ) : ℝ :=
  n ^ (-rateExponent C.smoothness d) *
    Real.exp (-stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)) *
    (Real.log n) ^ (lowerLogPower C.smoothness d + paperLogGap C)

theorem paperUpperScale_eq  (C : ModelConstants d)  (hn : 2 ≤ n) :
    paperUpperScale C n = paperRiskScale C n * (Real.log n) ^ paperLogGap C := by
  unfold paperUpperScale paperRiskScale
  rw [Real.rpow_add (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide) hn)))]
  ring

theorem paperRiskScale_eq_rateScale  (C : ModelConstants d)
     (hn : 2 ≤ n) :
    paperRiskScale C n = rateScale (rateExponent C.smoothness d)
      (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d) n := (rateScale_eq_rpow _ _ _ (by exact_mod_cast (lt_of_lt_of_le (by decide) hn))).symm

theorem paperUpperScale_eq_rateScale  (C : ModelConstants d)
     (hn : 2 ≤ n) :
    paperUpperScale C n = rateScale (rateExponent C.smoothness d)
      (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d + paperLogGap C) n := (rateScale_eq_rpow _ _ _ (by exact_mod_cast (lt_of_lt_of_le (by decide) hn))).symm

theorem paperRiskScale_pos  (C : ModelConstants d)  (hn : 2 ≤ n) :
    0 < paperRiskScale C n := by
  rw [paperRiskScale_eq_rateScale C hn]
  exact rateScale_pos _ _ _ _

/-- `thm:main` / `thm:bracket`, with the stated logarithmic gap. -/
def MainBracketClaim  (C : ModelConstants d) : Prop :=
  highSmoothnessRegime C →
    ∃ c A, 0 < c ∧ 0 < A ∧ ∃ n₀, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) n, n₀ ≤ n →
        ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n ∧
        minimaxRMS (C.withDomain U) n ≤
          ENNReal.ofReal (A * paperRiskScale C n * (Real.log n) ^ paperLogGap C)

/-- The separate refined upper bound `thm:upper-sharp`. -/
def UpperSharpClaim  (C : ModelConstants d) : Prop :=
  highSmoothnessRegime C →
    ∃ A, 0 < A ∧ ∃ n₀, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) n, n₀ ≤ n →
        minimaxRMS (C.withDomain U) n ≤ ENNReal.ofReal (A * paperUpperScale C n)

/-- The separate lower bound `thm:lower`. -/
def LowerSharpClaim  (C : ModelConstants d) : Prop :=
  highSmoothnessRegime C →
    ∃ c, 0 < c ∧ ∃ n₀, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) n, n₀ ≤ n →
        ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n

def lowSmoothnessScale (s : ℝ) (d n : ℕ) : ℝ :=
  max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(4 * s / ((d : ℝ) + 4 * s))))

/-- `thm:main2`, the exact low-smoothness bracket for every `n≥1`. -/
def LowSmoothnessClaim  (C : ModelConstants d) : Prop :=
  C.smoothness ≤ 1 → ∃ A, 0 < A ∧ ∀ n, 1 ≤ n →
    ENNReal.ofReal (A⁻¹ * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n ∧
    minimaxRMS C n ≤ ENNReal.ofReal (A * lowSmoothnessScale C.smoothness d n)

/-- `thm:parametric`, with its stated `s>1` hypothesis. -/
def ParametricClaim  (C : ModelConstants d) : Prop :=
  1 < C.smoothness → d ≤ 4 * C.smoothness →
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * ↑n ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n ∧
      minimaxRMS C n ≤ ENNReal.ofReal (A * ↑n ^ (-(1 / 2 : ℝ)))

/-- A claimed statistical bracket gives the explicit REAL rate-bracket hypothesis
used by the already-proved analytic corollaries. -/
theorem hasNatRateBracket_of_mainBracketClaim  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hmain : MainBracketClaim C) :
    HasNatRateBracket (fun n => (minimaxRMS C n).toReal)
      (rateExponent C.smoothness d) (stretchConstant C.smoothness d (paperTau C))
      (lowerLogPower C.smoothness d) (paperLogGap C) := by
  obtain ⟨c, A, hc, hA, n₀, hn₀, hbound⟩ := hmain hreg
  refine ⟨c, A, hc, hA, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hb := hbound C.originalDomain n hn
  rw [C.withDomain_original] at hb
  have hn2 := hn₀.trans hn
  have h_minimaxRisk_finite : minimaxRisk C n < ∞ := by
    apply lt_of_le_of_lt (minimaxRisk_le_worstCaseRisk C
      (constantEstimator d n C.varianceLower))
    apply lt_of_le_of_lt (iSup_le fun (θ : {θ : RegressionParameter d // Admissible C θ}) =>
      constantEstimator_risk_bound (n := n) C θ.val θ.property)
    exact ENNReal.ofReal_lt_top
  have h_minimaxRMS_finite  := ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (ne_of_lt h_minimaxRisk_finite)
  have hfin  := ne_of_lt h_minimaxRMS_finite
  have hlo := ENNReal.toReal_mono hfin hb.1
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.2
  rw [ENNReal.toReal_ofReal (mul_pos hc (paperRiskScale_pos C hn2)).le] at hlo
  rw [ENNReal.toReal_ofReal (by rw [mul_assoc, ← paperUpperScale_eq C hn2]; exact (mul_pos hA (by rw [paperUpperScale_eq_rateScale C hn2]; exact rateScale_pos _ _ _ _)).le), mul_assoc, ← paperUpperScale_eq C hn2] at hhi
  rw [paperRiskScale_eq_rateScale C hn2] at hlo
  rw [paperUpperScale_eq_rateScale C hn2] at hhi
  exact ⟨hlo, hhi⟩

end NearlyMinimax
