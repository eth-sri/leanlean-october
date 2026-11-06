module

public import proofs.HordijkSteelThreshold.StaticClosureMass
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Filter HordijkSteelThreshold
open scoped Topology

def geometricTest (t c ε : ℚ) (r : ℕ) : Prop := 0 < r ∧ c*t^r ≤ ε

instance (t c ε : ℚ) (r : ℕ) : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem geometricTest_exists (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    ∃ r, geometricTest t c ε r := by
  have hs := (tendsto_pow_atTop_nhds_zero_of_lt_one (by exact_mod_cast ht0 : (0 : ℝ) ≤ t)
    (by exact_mod_cast ht1)).const_mul (c : ℝ)
  rw [mul_zero] at hs
  obtain ⟨r, hr, hv⟩ := ((eventually_ge_atTop 1).and (hs.eventually_lt_const (by exact_mod_cast hε : (0 : ℝ) < ε))).exists
  exact ⟨r, hr, by exact_mod_cast hv.le⟩

def seedTest (b : ℚ) (m k : ℕ) : Prop :=
  0 < k ∧ (molecularContourConstant : ℚ) * (1 - b^2)^k *
    ((m : ℚ) * (m+1) + 1) ≤ 1

instance (b : ℚ) (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem seedTest_exists (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    ∃ k, seedTest b m k := by
  obtain ⟨k, hk, hv⟩ := geometricTest_exists (1 - b^2)
    ((molecularContourConstant : ℚ) * ((m : ℚ) * (m+1) + 1)) 1 (by nlinarith) (by nlinarith) one_pos
  exact ⟨k, hk, by linarith⟩

def seedIndex (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) : ℕ :=
  Nat.find (seedTest_exists b hb hb1 m)

theorem seedIndex_spec (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    seedTest b m (seedIndex b hb hb1 m) := Nat.find_spec (seedTest_exists b hb hb1 m)

end RAFCriticalWindowQuantitative
