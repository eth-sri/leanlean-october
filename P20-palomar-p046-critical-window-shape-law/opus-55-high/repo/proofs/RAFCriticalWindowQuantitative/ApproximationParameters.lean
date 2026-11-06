module

public import proofs.RAFCriticalWindowQuantitative.GeometricCutoff

@[expose] public section

namespace RAFCriticalWindowQuantitative

section
variable (q : ℚ)

theorem rationalHalf_pos  (hq : 0 < q) : 0 < q/2 :=
  div_pos hq zero_lt_two

theorem rationalHalf_le_one  (hq : 0 < q) (hq1 : q ≤ 1) : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

end

section
variable (ε : ℚ)

def precisionIndex  : ℕ := ⌈4/ε⌉₊+2

theorem precisionIndex_ge_two  : 2 ≤ precisionIndex ε := by
  unfold precisionIndex
  omega

theorem precisionIndex_error  (hε : 0 < ε) :
    1/(precisionIndex ε : ℚ) ≤ ε/4 := by
  have hc := Nat.le_ceil (4/ε)
  have hm : (0 : ℚ) < precisionIndex ε := by
    exact_mod_cast (show 0 < precisionIndex ε from lt_of_lt_of_le (by omega) $ precisionIndex_ge_two ε)
  have hbig : 4/ε ≤ precisionIndex ε := by
    exact hc.trans $ by simp [precisionIndex]
  have hx := (div_le_iff₀ hε).mp hbig
  apply (div_le_iff₀ hm).mpr
  nlinarith

end

def recordIndex (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)

end RAFCriticalWindowQuantitative
