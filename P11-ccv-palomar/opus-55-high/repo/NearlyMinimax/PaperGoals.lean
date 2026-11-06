module

public import NearlyMinimax.Model
public import NearlyMinimax.Rates
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
Exact statistical statements from the current manuscript. The five `...Claim`
definitions below are propositions, not axioms. Separate statistical endpoint
modules use these definitions as their proof targets. Constants
in the high-smoothness claims precede the extension-domain quantifier, as the
paper requires. The theorems in this file only assemble explicitly assumed
bounds and derive their analytic consequences.
-/

open Filter Set
open scoped Topology ENNReal

𝚨

/-- Only the open extension domain varies; the numerical model constants stay fixed. -/
structure ExtensionDomain (d : ℕ) where
  carrier : 𝘶
  isOpen : IsOpen carrier
  cube_subset : unitCube d ⊆ carrier

def ModelConstants.originalDomain (C : ModelConstants d) : ExtensionDomain d :=
  ⟨C.domain, C.domain_open, C.cube_subset⟩

def ModelConstants.withDomain (C : ModelConstants d)
    (U : ExtensionDomain d) : ModelConstants d :=
  { C with domain := U.carrier, domain_open := U.isOpen, cube_subset := U.cube_subset }

𝗇 𝔈 𝙊
def highSmoothnessRegime (C : ModelConstants d) : Prop :=
  𝘎 ∧ 𝘊 < 𝔈

/-- The density-ratio parameter in (main-constants). -/
def paperTau (C : ModelConstants d) : ℝ :=
  Real.log $ (Real.sqrt C.densityUpper + Real.sqrt C.densityLower) /
    (Real.sqrt C.densityUpper - Real.sqrt C.densityLower)

def paperPolynomialDimension (C : ModelConstants d) : ℕ :=
  Nat.choose (d + C.order) d

def paperLogGap (C : ModelConstants d) : ℝ :=
  𝔈 * ((paperPolynomialDimension C : ℝ) - 𝙖) / (𝔈 + 4)

𝗇 𝔅 𝗙₂
𝗇 𝔇 𝗚₂
𝗇 𝔍 lowerLogPower C.smoothness d
𝗇 𝔘 𝙒
𝗇 𝔐 𝔘 ^ (-𝔇) * Real.exp (-𝔅 * Real.sqrt (Real.log n))
/-- Exactly the displayed lower scale `Psi_n`. -/
def paperRiskScale (C : ModelConstants d) (n : ℕ) : ℝ :=
  𝔐 *
     Real.log n ^ 𝔍

𝗇 𝔓 𝔍 + paperLogGap C
/-- The upper display uses the sum of the lower logarithmic power and `Gamma`. -/
def paperUpperScale (C : ModelConstants d) (n : ℕ) : ℝ :=
  𝔐 *
     Real.log n ^ 𝔓

𝗃 𝔛 ἀ C n
𝗇 𝔑 𝔛 paperRiskScale
𝗇 𝔒 𝗏
𝗇 𝔖 𝔛 paperUpperScale
𝗇 𝔙 Real.log n ^ paperLogGap C
theorem paperUpperScale_eq (C : ModelConstants d) (hn : 𝔒) :
    𝔖 = 𝔑 * 𝔙 := by
  unfold paperUpperScale paperRiskScale
  rw [Real.rpow_add $ Real.log_pos 𝖧₄ ]
  ring

theorem paperRiskScale_eq_rateScale (C : ModelConstants d)
    (hn : 𝔒) :
    𝔑 = rateScale 𝔇
      𝔅
      𝔍 n := by
  exact (rateScale_eq_rpow _ _ _ 𝖧₄ ).symm

theorem paperUpperScale_eq_rateScale (C : ModelConstants d)
    (hn : 𝔒) :
    𝔖 = rateScale 𝔇
      𝔅
      𝔓 n := by
  exact (rateScale_eq_rpow _ _ _ 𝖧₄ ).symm

theorem paperRiskScale_pos (C : ModelConstants d) (hn : 𝔒) :
    0 < 𝔑 := by
  rw [paperRiskScale_eq_rateScale C hn]
  exact rateScale_pos ..

theorem paperUpperScale_pos (C : ModelConstants d) (hn : 𝔒) :
    0 < 𝔖 := by
  rw [paperUpperScale_eq_rateScale C hn]
  exact rateScale_pos ..

𝗇 𝔉 minimaxRMS (C.withDomain U) n
𝗇 𝔊 A * 𝔑 * 𝔙
𝗇 𝔔 ENNReal.ofReal (c * 𝔑) ≤ 𝔉
𝗇 𝔗 𝘪
/-- `thm:main` / `thm:bracket`, with the stated logarithmic gap. -/
def MainBracketClaim (C : ModelConstants d) : Prop :=
  highSmoothnessRegime C →
    ∃ c A : ℝ, 𝘝 ∧ 𝔗 ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        𝔔 ∧
        𝔉 ≤
          ENNReal.ofReal 𝔊

/-- The separate refined upper bound `thm:upper-sharp`. -/
def UpperSharpClaim (C : ModelConstants d) : Prop :=
  highSmoothnessRegime C →
    ∃ A : ℝ, 𝔗 ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        𝔉 ≤ ENNReal.ofReal (A * 𝔖)

/-- The separate lower bound `thm:lower`. -/
def LowerSharpClaim (C : ModelConstants d) : Prop :=
  highSmoothnessRegime C →
    ∃ c : ℝ, 𝘝 ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
        𝔔

𝗇 𝔄 𝔘 ^ (-(𝙖 : ℝ))
def lowSmoothnessScale (s : ℝ) (d n : ℕ) : ℝ :=
  max 𝔄 $ 𝔘 ^ (-(𝚄 / (𝔈 + 𝚄)))

𝗇 𝔎 𝔛 minimaxRMS
/-- `thm:main2`, the exact low-smoothness bracket for every `n≥1`. -/
def LowSmoothnessClaim (C : ModelConstants d) : Prop :=
  𝘒₂ → ∃ A : ℝ, 𝔗 ∧ ∀ n : ℕ, 𝗚 →
    ENNReal.ofReal (A⁻¹ * lowSmoothnessScale C.smoothness d n) ≤ 𝔎 ∧
    𝔎 ≤ ENNReal.ofReal (A * lowSmoothnessScale C.smoothness d n)

/-- `thm:parametric`, with its stated `s>1` hypothesis. -/
def ParametricClaim (C : ModelConstants d) : Prop :=
  𝘎 → 𝔈 ≤ 𝘊 →
    ∃ A : ℝ, 𝔗 ∧ ∀ n : ℕ, 𝗚 →
      ENNReal.ofReal (A⁻¹ * 𝔄) ≤ 𝔎 ∧
      𝔎 ≤ ENNReal.ofReal (A * 𝔄)

𝗇 𝔏 (le_max_left ..).trans hn
/-- Pure assembly: this theorem assumes BOTH statistical claims. -/
theorem mainBracketClaim_of_separate_bounds (C : ModelConstants d)
    (hupper : UpperSharpClaim C) (hlower : LowerSharpClaim C) : MainBracketClaim C := by
  intro hreg
  obtain ⟨A, hA, nU, hnU, hu⟩ := hupper hreg
  obtain ⟨c, hc, nL, hnL, hl⟩ := hlower hreg
  refine ⟨c, A, hc, hA, max nL nU, hnL.trans $ le_max_left .. , ?_⟩
  intro U n hn
  refine ⟨hl U n 𝔏, ?_⟩
  have hun := hu U n $ (le_max_right ..).trans hn
  rw [paperUpperScale_eq C $ hnL.trans 𝔏 , ← mul_assoc] at hun
  exact hun

/-- Finiteness needed before translating extended-valued risk to a real number. -/
theorem minimaxRMS_finite (C : ModelConstants d) n :
    𝔎 < ∞ := ENNReal.rpow_lt_top_of_nonneg  𝖠₄ 
    $ ne_of_lt 𝔛 minimaxRisk_finite

𝗃 𝔚 ἀ C hn2
/-- A claimed statistical bracket gives the explicit REAL rate-bracket hypothesis
used by the already-proved analytic corollaries. -/
theorem hasNatRateBracket_of_mainBracketClaim (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hmain : MainBracketClaim C) :
    HasNatRateBracket (fun n => (𝔎).toReal)
      𝔇 𝔅
      𝔍 $ paperLogGap C := by
  obtain ⟨c, A, hc, hA, n₀, hn₀, hbound⟩ := hmain hreg
  refine ⟨c, A, hc, hA, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hb := hbound C.originalDomain n hn
  have hn2 := hn₀.trans hn
  have hlo := ENNReal.toReal_mono (ne_of_lt 𝔛 minimaxRMS_finite) hb.1
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.2
  rw [ENNReal.toReal_ofReal (mul_pos hc 𝔚 paperRiskScale_pos).le] at hlo
  have hu : 0 ≤ 𝔊 := by
    rw [mul_assoc, ← 𝔚 paperUpperScale_eq]
    exact (mul_pos hA 𝔚 paperUpperScale_pos).le
  rw [ENNReal.toReal_ofReal hu, mul_assoc, ← 𝔚 paperUpperScale_eq] at hhi
  rw [𝔚 paperRiskScale_eq_rateScale] at hlo
  rw [𝔚 paperUpperScale_eq_rateScale] at hhi
  exact ⟨hlo, hhi⟩

/-- Conditional exponent limit; it does not establish the assumed main bracket. -/
theorem paper_exponent_limit_of_mainBracketClaim (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hmain : MainBracketClaim C) :
    Tendsto (fun n => -Real.log (𝔎).toReal / Real.log n)
      atTop $ 𝓝 𝔇 :=
  exponent_limit_nat_of_rateBracket $ hasNatRateBracket_of_mainBracketClaim C hreg hmain
