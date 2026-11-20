module
public import proofs.RAF.Concrete.PolymerCRS

/-! Executable rational cutoffs and the pool and intensity parameter maps. -/

@[expose] public section

open unitInterval

namespace HordijkSteelThreshold
open RAF.Polymer

def molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81

noncomputable def fixedPoolParameter (p : I) (k : ℕ) : I := σ ((σ p)^k)

def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

end HordijkSteelThreshold

namespace RAFCriticalWindowQuantitative
open Filter HordijkSteelThreshold

section
variable (t c ε : ℚ)

def geometricTest (r : ℕ) : Prop := 0 < r ∧ c*t^r ≤ ε

instance (r : ℕ) : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε)

include ht0 ht1 hε in
theorem geometricTest_exists :
    ∃ r, geometricTest t c ε r := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul c
  obtain ⟨k,hk,he⟩ := ((eventually_gt_atTop 0).and (h.eventually_lt_const (by simpa using hε))).exists
  exact ⟨k,hk,he.le⟩

def geometricIndex : ℕ :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)
end

section
variable (b : ℚ)
/-- A decidable rational test, using the source's literal contour constant. -/
def seedTest (m k : ℕ) : Prop :=
  0 < k ∧ (molecularContourConstant : ℚ) * (1 - b^2)^k *
    ((m : ℚ) * (m+1) + 1) ≤ 1

instance (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ)
include hb hb1 in
theorem seedTest_exists :
    ∃ k, seedTest b m k := by
  obtain ⟨k,hk,he⟩ := geometricTest_exists (1-b^2)
    (molecularContourConstant*((m : ℚ)*(m+1)+1)) 1 (by nlinarith) (by nlinarith) zero_lt_one
  exact ⟨k,hk,by linarith only [he]⟩

/-- Executable unbounded search; termination is proved from geometric decay. -/
def seedIndex : ℕ :=
  Nat.find (seedTest_exists b hb hb1 m)
end

section
variable (ε : ℚ)
def precisionIndex : ℕ := ⌈4/ε⌉₊+2

end

variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) (ε : ℚ) (hε : 0 < ε)

include hq hq1 in
/-- The repair-failure ratio is a genuine geometric ratio at every positive openness. -/
theorem repair_ratio :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 :=
  ⟨sub_nonneg.mpr (pow_le_one₀ hq.le hq1),sub_lt_self _ (pow_pos hq _)⟩

def recordIndex : ℕ :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)

include hq in
theorem rationalHalf_pos : 0 < q/2 :=
  div_pos hq zero_lt_two

include hq hq1 in
theorem rationalHalf_le_one : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

def rationalParameter (b : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩

def rationalPool (p : ℚ) (k : ℕ) : ℚ := 1-(1-p)^k

end RAFCriticalWindowQuantitative

namespace RAFReactionQuotient
noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩
end RAFReactionQuotient
