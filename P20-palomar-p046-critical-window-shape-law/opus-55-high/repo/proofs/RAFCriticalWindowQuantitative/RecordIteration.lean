module

public import proofs.RAFCriticalWindowQuantitative.RecordContraction

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

variable {g : List Bool × ℕ → List Bool × ℕ}

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 $ fun _ cap => 2*cap+ell

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

theorem recordCap_mono_length {ell L : ℕ} (h : ell ≤ L) (j : ℕ) :
    recordCap ell j ≤ recordCap L j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

theorem escapedMissing_antitone (v : List Bool) : Antitone (escapedMissing g · v) := by
  intro B N hBN ω hω
  obtain ⟨w,hw,hg⟩ := hω.1
  exact ⟨⟨w,by omega,hg⟩,
    fun hv => hω.2 $ finiteReversibleGenerated_mono_cap hBN hv⟩

theorem repeated_record_failure (hg : PrefixIndex g) (a : I) (v : List Bool) (hv : 0 < v.length) (r : ℕ) :
    infiniteSplitPi a (escapedMissing g (recordCap v.length r) v) ≤
      (1-(toNNReal a : ENNReal)^(v.length+1))^r := by
  induction r with
  | zero => simpa using prob_le_one
  | succ r ih =>
    calc
      _ ≤ infiniteSplitPi a (escapedMissing g (recordCap v.length r) v) *
          (1-(toNNReal a)^(v.length+1)) :=
        escaped_missing_contraction hg a v hv _ $ recordCap_ge_two _ _
      _ ≤ (1-(toNNReal a)^(v.length+1))^r *
          (1-(toNNReal a)^(v.length+1)) := mul_le_mul' ih le_rfl
theorem common_cap_target_failure (hg : PrefixIndex g) (a : I) (v : List Bool) (hv : 0 < v.length)
    (L : ℕ) (hvL : v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a (escapedMissing g (recordCap L r) v) ≤
      (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hp : (toNNReal a)^(L+1) ≤ (toNNReal a : ENNReal)^(v.length+1) := by
    apply pow_le_pow_of_le_one zero_le
    · exact_mod_cast a.property.2
    omega
  exact ((measure_mono $ escapedMissing_antitone v $ recordCap_mono_length hvL r).trans
    (repeated_record_failure hg a v hv r)).trans
      (pow_le_pow_left' (tsub_le_tsub_left hp 1) r)

end RAFCriticalWindowQuantitative
