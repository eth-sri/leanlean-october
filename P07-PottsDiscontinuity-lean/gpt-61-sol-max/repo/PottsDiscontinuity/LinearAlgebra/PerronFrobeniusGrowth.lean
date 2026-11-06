module

public import Mathlib
public import PottsDiscontinuity.LinearAlgebra.PerronFrobeniusIrreducible

/-!
# Perron-Frobenius growth: `(1/M) log tr (A ^ M) → log ρ`

For a primitive symmetric nonnegative matrix `A` with largest eigenvalue `ρ = pfRoot A`:

* `tendsto_log_trace_pow_primitive`:  `(1/M) * log (trace (A ^ M)) → log ρ`;
* `tendsto_log_dotProduct_pow_mulVec_primitive`: the same for the pairing `x ⬝ᵥ A ^ M *ᵥ y` with
  nonzero nonnegative vectors `x`, `y`;
* `tendsto_log_sum_entries_pow_primitive`: the same for the sum of all entries of `A ^ M`.

The analytic input is `tendsto_log_sum_mul_pow`: if one weight-positive term `μ i0 = ρ > 0`
dominates, `(1/M) * log (∑ i, μ i ^ M * a i) → log ρ`.
-/

@[expose] public section

open Matrix Filter Topology

namespace PottsDiscontinuity.PerronFrobenius

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section

variable (μ a : ι → ℝ) (i0 : ι) {ρ : ℝ} (hρ : 0 < ρ) (hi0 : μ i0 = ρ)
include a hρ hi0

/-- `∑ i, μ i ^ M * a i` divided by `ρ ^ M` tends to `a i0` when `μ i0 = ρ` and all the other
`|μ i|` are `< ρ`. -/
theorem tendsto_sum_mul_pow_div 
    (hgap : ∀ i, i ≠ i0 → |μ i| < ρ) :
    Tendsto (fun M : ℕ => (∑ i, μ i ^ M * a i) / ρ ^ M) atTop (𝓝 (a i0)) := by
  have hterm : ∀ i, Tendsto (fun M  => (μ i / ρ) ^ M * a i) atTop
      (𝓝 (if i = i0 then a i0 else 0)) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [hi0, div_self hρ.ne', one_pow, one_mul]
      exact tendsto_const_nhds
    · simp only [hi]
      have h1 : |μ i / ρ| < 1 := by
        rw [abs_div, abs_of_pos hρ, div_lt_one hρ]
        exact hgap i hi
      have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h1).mul_const (a i)
      simpa using this
  have hsum := tendsto_finsetSum  Finset.univ   fun i _ => hterm i 
  rw [Finset.sum_ite_eq' Finset.univ i0  fun _ => a i0 ] at hsum
  simp only [Finset.mem_univ] at hsum
  refine hsum.congr fun M => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_pow, div_mul_eq_mul_div]

theorem tendsto_log_sum_mul_pow 
    (ha : 0 < a i0) (hgap : ∀ i, i ≠ i0 → |μ i| < ρ) :
    Tendsto (fun M : ℕ =>  1 / (M : ℝ)  * Real.log (∑ i, μ i ^ M * a i)) atTop
      (𝓝 (Real.log ρ)) := by
  have hT := tendsto_sum_mul_pow_div μ a i0 hρ hi0 hgap
  
  
  
  have h0 : Tendsto (fun M : ℕ =>  1 /  M   * Real.log ((∑ i, μ i ^ M * a i) / ρ ^ M))
      atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat).mul (hT.log ha.ne')
  have hlim : Tendsto (fun M : ℕ => Real.log ρ +
       1 / (M )  * Real.log ((∑ i, μ i ^ M * a i) / ρ ^ M)) atTop (𝓝 (Real.log ρ)) := by
    simpa using (tendsto_const_nhds (x := Real.log ρ)).add h0
  refine hlim.congr' ?_
  filter_upwards [ hT.eventually (lt_mem_nhds ha) , eventually_ge_atTop 1] with M hM hM1
  
  
  
  rw [Real.log_div (by
                      intro h
                      simp_all)  (pow_pos hρ M).ne' , Real.log_pow]
  field_simp
  ring

end

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ}

/-- For a primitive symmetric nonnegative matrix there is a unique eigenvalue index attaining
`pfRoot A`, and all the other eigenvalues are strictly smaller in absolute value. -/
theorem exists_unique_top_eigenvalue (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) {k : ℕ}
    (hk0 : 0 < k) (hk : ∀ i j, 0 < (A ^ k) i j) :
    ∃ i0, hA.eigenvalues i0 = pfRoot A ∧ ∀ i, i ≠ i0 → |hA.eigenvalues i| < pfRoot A := Exists.casesOn (existsUnique_eigenvalues_eq_pfRoot hnn (fun i j => Exists.intro k ⟨hk0, hk i j⟩) hA) fun i0 h =>
                                                                                          And.casesOn h fun hi0 huniq =>
                                                                                            Exists.intro i0
                                                                                              ⟨hi0, fun i hi =>
                                                                                                abs_lt_pfRoot_of_primitive hnn hk0 hk hA (IsHermitian.eigenvalues_mem_spectrum_real hA i) fun h =>
                                                                                                  hi (huniq i h)⟩

theorem tendsto_log_trace_pow_primitive (hA : A.IsHermitian) (hprim : A.IsPrimitive) :
    Tendsto (fun M : ℕ =>  1 / (M : ℝ)  * Real.log (A ^ M).trace) atTop
      (𝓝 (Real.log (pfRoot A))) := by
  obtain ⟨k, hk0, hk⟩ := hprim.exists_pos_pow
  have hnn := hprim.nonneg
  
  
  obtain ⟨i0, hi0, hgap⟩ := exists_unique_top_eigenvalue hA hnn hk0 hk
  
  refine (tendsto_log_sum_mul_pow hA.eigenvalues (fun _ => 1) i0 (pfRoot_pos_of_irreducible hnn (fun i j => ⟨k, hk0, hk i j⟩) hA) hi0 one_pos hgap).congr fun M => ?_
  rw [trace_pow_eq_sum hA]
  simp

end

end PottsDiscontinuity.PerronFrobenius
