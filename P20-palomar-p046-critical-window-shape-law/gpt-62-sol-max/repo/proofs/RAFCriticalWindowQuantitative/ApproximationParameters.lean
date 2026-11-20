module

public import Mathlib
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-- The original constant in the certified cutoff test. -/
def HordijkSteelThreshold.molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81

namespace RAFCriticalWindowQuantitative
open Filter HordijkSteelThreshold unitInterval
open scoped Topology

/-- A decidable rational test, using the source's literal contour constant. -/
def seedTest (b : ℚ) (m k : ℕ) : Prop :=
  0 < k ∧ (molecularContourConstant : ℚ) * (1 - b^2)^k *
    ((m : ℚ) * (m+1) + 1) ≤ 1

instance (b : ℚ) (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))

def geometricTest (t c ε : ℚ) (r : ℕ) : Prop := 0 < r ∧ c*t^r ≤ ε

instance (t c ε : ℚ) (r : ℕ) : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))

section
variable (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε)
include ht0 ht1 hε

/-- Geometric decay with a positive index even when the ratio is zero. -/
theorem geometricTest_exists :
    ∃ r, geometricTest t c ε r := by
  have h : Tendsto (fun n : ℕ => c*t^n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1)
  obtain ⟨n,hn⟩ := eventually_atTop.mp (h.eventually_lt_const hε)
  exact ⟨n+1,Nat.succ_pos _,(hn _ (Nat.le_succ _)).le⟩

def geometricIndex : ℕ :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)

end

/-- The repair-failure ratio is a genuine geometric ratio at every positive openness. -/
theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 :=
  ⟨sub_nonneg.mpr (pow_le_one₀ hq.le hq1), sub_lt_self _ (pow_pos hq _)⟩

section
variable (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ)
include hb hb1

theorem seedTest_exists :
    ∃ k, seedTest b m k := by
  have h := repair_ratio b hb hb1 1
  simpa only [seedTest, geometricTest, mul_right_comm] using geometricTest_exists (1-b^2)
    ((molecularContourConstant : ℚ)*((m : ℚ)*(m+1)+1)) 1 h.1 h.2 zero_lt_one

/-- Executable unbounded search; termination is proved from geometric decay. -/
def seedIndex : ℕ :=
  Nat.find (seedTest_exists b hb hb1 m)

theorem seedIndex_spec :
    seedTest b m (seedIndex b hb hb1 m) := Nat.find_spec (seedTest_exists b hb hb1 m)

end

section
variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)

include hq in
theorem rationalHalf_pos : 0 < q/2 :=
  div_pos hq zero_lt_two

include hq hq1 in
theorem rationalHalf_le_one : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

def precisionIndex (ε : ℚ) : ℕ := ⌈4/ε⌉₊+2

theorem precisionIndex_error (ε : ℚ) (hε : 0 < ε) :
    (precisionIndex ε : ℚ)⁻¹ ≤ ε/4 := by
  simpa [one_div] using one_div_le_one_div_of_le (by positivity : 0 < (4:ℚ)/ε)
    ((Nat.le_ceil _).trans (by simp [precisionIndex]))

variable (L : ℕ) (ε : ℚ) (hε : 0 < ε)

def recordIndex : ℕ :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)

theorem recordIndex_error :
    (2 : ℚ)^(L+1)*(1-q^(L+1))^(recordIndex q hq hq1 L ε hε) ≤ ε/4 :=
  (Nat.find_spec (p := geometricTest _ _ _) _).2

end

def rationalParameter (b : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩

theorem rationalParameter_mono {p q : ℚ} {hp hp1 hq hq1} (h : p ≤ q) :
    rationalParameter p hp hp1 ≤ rationalParameter q hq hq1 :=
  (Rat.cast_le (K := ℝ)).mpr h

end RAFCriticalWindowQuantitative
