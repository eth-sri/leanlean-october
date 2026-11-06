module
public import proofs.RAF.Polymer.Reactions
public import Mathlib
@[expose] public section

namespace HordijkSteelThreshold
def molecularContourConstant := 2 * 7 ^ 64 * 81
end HordijkSteelThreshold

namespace RAF.Concrete
open MeasureTheory ProbabilityTheory unitInterval RAF.Polymer
variable (n : Nat)
noncomputable def rawCatalysisP  (lambda : ℝ)  :=
  lambda * n / Fintype.card (Reaction n)

/-- Clamp only to obtain a total unit-interval parameter.  The asymptotic proof
later shows the clamp is inactive in the positive fixed-lambda tail. -/
noncomputable def catalysisP  (lambda : ℝ) : I :=
  ⟨min 1 (max 0 (rawCatalysisP n lambda)), by
    constructor
    · exact le_min (by norm_num) (le_max_left _ _)
    · exact min_le_left _ _⟩
end RAF.Concrete

namespace RAFCriticalWindowQuantitative
variable (b : ℚ)
open Filter HordijkSteelThreshold


section

variable (t c ε : ℚ)

variable (r : ℕ)

def geometricTest   := 0 < r ∧ c*t^r ≤ ε

instance  : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε)

include ht0 ht1 hε in
theorem geometricTest_exists  :
    ∃ r, geometricTest t c ε r := by
  have hs := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul c
  simp at hs
  obtain ⟨r, hr, hv⟩ := ((eventually_ge_atTop 1).and (hs.eventually_lt_const hε)).exists
  exact ⟨r, by omega, hv.le⟩

end

/-- A decidable rational test, using the source's literal contour constant. -/
def seedTest  (m k : ℕ)  :=
  0 < k ∧ molecularContourConstant * (1 - b^2)^k *
    (m * (m+1) + 1) ≤ 1

instance  (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ)

include hb hb1 in
theorem seedTest_exists  :
    ∃ k, seedTest b m k := by
  simpa [seedTest, geometricTest, mul_assoc, mul_left_comm, mul_comm] using
    geometricTest_exists (1-b^2) (molecularContourConstant*((m : ℚ)*(m+1)+1)) 1
      (by nlinarith) (by nlinarith) (by norm_num)

/-- Executable unbounded search; termination is proved from geometric decay. -/
def seedIndex   :=
  Nat.find (seedTest_exists b hb hb1 m)

section
variable (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε)

def geometricIndex   :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)

/-- The repair-failure ratio is a genuine geometric ratio at every positive openness. -/
theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 := by grind [pow_pos, pow_le_one₀]
end


theorem rationalHalf_pos (q : ℚ) (hq : 0 < q) : 0 < q/2 :=
  div_pos hq zero_lt_two

variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)

include hq hq1 in
theorem rationalHalf_le_one  : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

variable (ε : ℚ)

def precisionIndex   := ⌈4/ε⌉₊+2

theorem precisionIndex_ge_two  : 2 ≤ precisionIndex ε := by
  unfold precisionIndex
  omega



variable (L : ℕ) (ε : ℚ) (hε : 0 < ε)

def recordIndex    :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)

theorem recordIndex_error   :
    0 < recordIndex q hq hq1 L ε hε ∧
      2^(L+1)*(1-q^(L+1))^(recordIndex q hq hq1 L ε hε) ≤ ε/4 :=
by
  unfold recordIndex geometricIndex
  exact Nat.find_spec (p := geometricTest _ _ _) _

open HordijkSteelThreshold unitInterval

def rationalParameter  (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩


end RAFCriticalWindowQuantitative

namespace RAFReactionQuotient
open unitInterval

variable (lambda : ℝ) (hlambda : 0 < lambda)

noncomputable def criticalOpenness  : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩

end RAFReactionQuotient
