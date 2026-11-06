module

public import GoldbachLean.Wu2008.Sum

/-!
T1, unit U-1133, PC run 20261020T0003Z-10609. P0043 Wu 2008 Lemma 2.2: the O(N^{1−κ₁}) term made
explicit. For any finite A of integers 0 < a < N coprime to N and κ₁ with N^κ₁ > 1,
  E = #{a ∈ A : a sifted at N^κ₁, a not squarefree} ≤ N/(N^κ₁ − 1),     `Esq_le`
since such an a has q² | a for a prime q ≥ N^κ₁, at most N/q² of 1..N are multiples of q², and
Σ_{q ≥ M} 1/q² ≤ 1/(M − 1). With Wu2008Lemma22Sum.lean this gives (2.2) with an explicit error,
   3Υ₁ + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁ ≤ 4 D₁₂ + 4N/(N^κ₁ − 1),
and for Wu's own A = {N − p : p < N prime, p ∤ N}, `wuA`, `lemma22_wuA`.
KNOWN mathematics. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuSum
open Finset
open GoldbachLean.Wu2008.WuSieve (Sifted)
open GoldbachLean.Wu2008.WuReal (Admissible)

@[expose] public noncomputable section
open scoped Classical
variable (N : ℕ) (k1 k2 : ℝ)

/-- Wu's set `A = {N − p : p < N prime, p ∤ N}`. -/
def wuA : Finset ℕ := ((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)).image (fun p => N - p)

/-- **(2.2) for Wu's own `A = {N − p}`, explicit error.** -/
theorem lemma22_wuA (hA : Admissible k1 k2) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ k1) :
    (3 * Y1 (wuA N) N k1 + Y2 (wuA N) N k2 + Y5 (wuA N) N k1 k2 + Y6 (wuA N) N k1 k2 : ℝ)
      - Y3 (wuA N) N k1 - Y4 (wuA N) N k1 - 2 * Y7 (wuA N) N k1 - Y8 (wuA N) N k1
      - Y9 (wuA N) N k1 k2 - Y10 (wuA N) N k1 k2 - Y11 (wuA N) N k1 k2
      ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ k1 - 1)) := by
  have hok : ∀ a ∈ wuA N, 0 < a ∧ a < N ∧ a.Coprime N := by  
    intro a ha
    obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
    obtain ⟨hpN, hpr, hnd⟩ := by simpa only [mem_filter, mem_range] using hp
    have h2 := hpr.two_le
    refine ⟨by omega, by omega, ?_⟩
    exact (Nat.coprime_self_sub_left (by omega)).2 ((Nat.Prime.coprime_iff_not_dvd hpr).2 hnd)
  have hAN := hok
  have hNk' := hNk
  have hE : (Esq (wuA N) N k1 : ℝ) ≤ (N : ℝ) / ((N : ℝ) ^ k1 - 1) := by
  
    set M := ⌈(N : ℝ) ^ k1⌉₊
    have hM2 : 2 ≤ M := by
      have : (1 : ℝ) < M := lt_of_lt_of_le hNk' (Nat.le_ceil _)
      exact_mod_cast this
    set Q := (Icc M N).filter Nat.Prime
    have hsub : {a ∈ (wuA N) | Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a} ⊆
        Q.biUnion (fun q => (Ioc 0 N).filter (fun a => q * q ∣ a)) := by
      intro a ha
      obtain ⟨haA, hs, hsq⟩ := mem_filter.1 ha
      obtain ⟨h0, hlt, hcop⟩ := hAN a haA
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push_neg at hsq
      obtain ⟨q, hq, hqq⟩ := hsq
      have hqa : q ∣ a := dvd_trans (dvd_mul_right q q) hqq
      have hk := (sifted_iff h0 hlt hcop _).1 hs q ((mem_pf h0).2 ⟨hq, hqa⟩)
      rw [mem_biUnion]
      exact ⟨q, mem_filter.2 ⟨mem_Icc.2 ⟨Nat.ceil_le.2 hk, (Nat.le_of_dvd h0 hqa).trans hlt.le⟩, hq⟩,
        mem_filter.2 ⟨mem_Ioc.2 ⟨h0, hlt.le⟩, hqq⟩⟩
    have h1 : (Esq (wuA N) N k1 : ℝ) ≤ ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) := by
      have h := (card_le_card hsub).trans card_biUnion_le
      calc (Esq (wuA N) N k1 : ℝ)
          ≤ ((∑ q ∈ Q, #((Ioc 0 N).filter (fun a => q * q ∣ a)) : ℕ) : ℝ) := by
            unfold Esq; exact_mod_cast h
        _ = ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) := by
          push_cast
          exact sum_congr rfl fun q _ => by rw [Nat.Ioc_filter_dvd_card_eq_div]
    have h2 : ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) ≤ ∑ m ∈ Icc M N, (N : ℝ) * (1 / (m : ℝ) ^ 2) := by
      calc ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) ≤ ∑ q ∈ Q, (N : ℝ) * (1 / (q : ℝ) ^ 2) := by
            refine sum_le_sum fun q hq => ?_
            rw [mul_one_div]
            calc ((N / (q * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((q * q : ℕ) : ℝ) := Nat.cast_div_le
              _ = (N : ℝ) / (q : ℝ) ^ 2 := by push_cast; field_simp
        _ ≤ ∑ m ∈ Icc M N, (N : ℝ) * (1 / (m : ℝ) ^ 2) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    have hsum : ∑ m ∈ Icc M N, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
      have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
      rcases le_or_gt M N with h | h
      · have hk : M - 1 ≠ 0 := by omega
        have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := M - 1) (n := N) hk (by omega)
        rw [show Ioc (M - 1) N = Icc M N by ext x; simp only [mem_Ioc, mem_Icc]; omega] at h
        simp only [one_div] at h ⊢
        norm_num [Nat.cast_sub (by omega : 1 ≤ M)] at h
        have hNk' : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
        linarith
      · have h0 : Icc M N = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x hx
          simp only [mem_Icc] at hx
          omega
        rw [h0]
        positivity
    have h3 : ∑ m ∈ Icc M N, (N : ℝ) * (1 / (m : ℝ) ^ 2) ≤ N / ((N : ℝ) ^ k1 - 1) := by
      rw [← mul_sum]
      calc (N : ℝ) * ∑ m ∈ Icc M N, 1 / (m : ℝ) ^ 2 ≤ N * (1 / ((M : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
        _ = N / ((M : ℝ) - 1) := by rw [mul_one_div]
        _ ≤ N / ((N : ℝ) ^ k1 - 1) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith [Nat.le_ceil ((N : ℝ) ^ k1)])
    linarith
  have h := lemma22_sum (wuA N) N k1 k2 hA hN hok
  have hR := (Int.cast_le (R := ℝ)).2 h
  push_cast at hR
  linarith [hE]

end

end GoldbachLean.Wu2008.WuSum
