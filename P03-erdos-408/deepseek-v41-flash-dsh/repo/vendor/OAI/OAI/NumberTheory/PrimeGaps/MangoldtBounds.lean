module

public import OAI.NumberTheory.PrimeGaps.OrthantIntegrals

@[expose] public section

namespace OAI

namespace LargePrimeGaps







theorem theta_le_vonMangoldt (n : ℕ) : theta n ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : Nat.Prime n
  · simp [theta, hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [theta, hn]

theorem sum_vonMangoldt_sub_theta (Y : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Y, (ArithmeticFunction.vonMangoldt n - theta n)) =
      Chebyshev.psi Y - Chebyshev.theta Y := by
  simp only [Finset.sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast,
    theta, Finset.sum_filter]

theorem residueSlice_primepower_error {U : ℕ} (hU : 1 ≤ U) (L q c : ℕ) :
    |residueSlice ArithmeticFunction.vonMangoldt L U q c - residueSlice theta L U q c| ≤
      2 * Real.sqrt U * Real.log U := by
  have hdiff : 0 ≤ residueSlice ArithmeticFunction.vonMangoldt L U q c -
      residueSlice theta L U q c := by
    rw [residueSlice, residueSlice, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun n _ => sub_nonneg.mpr (theta_le_vonMangoldt n)
  rw [abs_of_nonneg hdiff, residueSlice, residueSlice, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 U, (ArithmeticFunction.vonMangoldt n - theta n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnL,hnU⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, hnU⟩
      · intro n _ _
        exact sub_nonneg.mpr (theta_le_vonMangoldt n)
    _ = Chebyshev.psi U - Chebyshev.theta U := sum_vonMangoldt_sub_theta U
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hU)

theorem residueSlice_theta_le {L U bound : ℕ} (hU : U ≤ bound) (hb : 1 ≤ bound)
    (q c : ℕ) : residueSlice theta L U q c ≤ (U-L:ℕ) * Real.log bound := by
  have hlog : 0 ≤ Real.log (bound:ℝ) := Real.log_nonneg (by exact_mod_cast hb)
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), Real.log bound := by
      apply Finset.sum_le_sum
      intro n hn
      have hnU := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
      by_cases hp : Nat.Prime n
      · rw [theta, ite_eq_left hp]
        exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hnU.trans hU)
      · simpa [theta, hp]
    _ = (((Finset.Ioc L U).filter (fun n => n % q = c)).card:ℝ) * Real.log bound := by simp
    _ ≤ (U-L:ℕ) * Real.log bound := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast (Finset.card_filter_le (Finset.Ioc L U) (fun n => n % q = c)).trans_eq
        (Nat.card_Ioc L U)

noncomputable def endpointError (x : ℝ) (q : ℕ) : NNReal :=
  (Finset.range q).sup fun c => if Nat.Coprime c q then
    NNReal.mk (|residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c - x/q.totient|)
      (abs_nonneg _) else 0

theorem endpointClassError_le (X : ℕ) {q c : ℕ} (hc : c < q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient| ≤
      (endpointError X q : ℝ) := by
  have h := Finset.le_sup (f := fun c => if Nat.Coprime c q then
    NNReal.mk (|residuePrefix ArithmeticFunction.vonMangoldt ⌊(X:ℝ)⌋₊ q c -
      (X:ℝ)/q.totient|) (abs_nonneg _) else 0) (Finset.mem_range.mpr hc)
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [ite_eq_left hcop, NNReal.coe_mk, Nat.floor_natCast, endpointError] using hr

def BombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊,
        (endpointError x q : ℝ)) ≤ M*x*(Real.log x)^(-A)

theorem harmonic_le_twice_log {Q X : ℕ} (hQX : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (harmonic Q : ℝ) ≤ 2 * Real.log (X:ℝ) := by
  have hmono : (harmonic Q : ℝ) ≤ (harmonic X : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hQX) (by intros; positivity)
  have hh := harmonic_le_one_add_log X
  linarith

end LargePrimeGaps

end OAI
