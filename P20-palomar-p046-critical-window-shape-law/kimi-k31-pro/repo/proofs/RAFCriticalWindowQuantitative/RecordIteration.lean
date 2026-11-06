module

public import proofs.RAFCriticalWindowQuantitative.RecordContraction

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

theorem recordCap_mono_length {ell L : ℕ} (h : ell ≤ L) (j : ℕ) :
    recordCap ell j ≤ recordCap L j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

end RAFCriticalWindowQuantitative
