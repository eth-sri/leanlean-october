module

public import GoldbachLean.Wu2008.Sum

/-!
T1, unit U-1133, PC run 20261020T0003Z-10609. P0043 Wu 2008 Lemma 2.2: the O(N^{1−κ₁}) term made
explicit. For any finite A of integers 0 < a < N coprime to N and κ₁ with N^κ₁ > 1,
  E = #{a ∈ A : a sifted at N^κ₁, a not squarefree} ≤ N/(N^κ₁ − 1),     `Esq_le`
since such an a has q² | a for a prime q ≥ N^κ₁, at most N/q² of 1..N are multiples of q², and
Σ_{q ≥ M} 1/q² ≤ 1/(M − 1). With Wu2008Lemma22Sum.lean this gives (2.2) with an explicit error,
  3Υ₁ + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁ ≤ 4 D₁₂ + 4N/(N^κ₁ − 1),   `lemma22_explicit`,
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

/-- `Σ_{M ≤ m ≤ K} 1/m² ≤ 1/(M − 1)` for `M ≥ 2`. -/
lemma sum_inv_sq_le' (M : ℕ) (hM : 2 ≤ M) (K : ℕ) :
    ∑ m ∈ Icc M K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  by_cases h : M ≤ K
  · have h' := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := M - 1) (n := K) (by omega) (by omega)
    rw [show Ioc (M - 1) K = Icc M K by ext; simp; omega] at h'
    rw [Nat.cast_sub (by omega : 1 ≤ M)] at h'
    norm_num at h'
    calc
      ∑ m ∈ Icc M K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - (K : ℝ)⁻¹ := by
        simpa only [one_div] using h'
      _ ≤ _ := sub_le_self _ (by positivity)
  · rw [Icc_eq_empty (by omega), sum_empty]
    positivity

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)
local notation "Ny" => (N : ℝ) ^ k1
macro "WL" A:term:max N:term:max k1:term:max k2:term:max : term =>
  `((3 * Y1 $A $N $k1 + Y2 $A $N $k2 + Y5 $A $N $k1 $k2 + Y6 $A $N $k1 $k2 : ℝ)
    - Y3 $A $N $k1 - Y4 $A $N $k1 - 2 * Y7 $A $N $k1 - Y8 $A $N $k1
    - Y9 $A $N $k1 $k2 - Y10 $A $N $k1 $k2 - Y11 $A $N $k1 $k2)

/-- **The non-squarefree error, explicit.** -/
theorem Esq_le (hN : 1 < Ny) (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (Esq A N k1 : ℝ) ≤ N / (Ny - 1) := by
  set M := ⌈Ny⌉₊
  have hM2 : 2 ≤ M := by
    have : (1 : ℝ) < M := lt_of_lt_of_le hN (Nat.le_ceil _)
    exact_mod_cast this
  set Q := (Icc M N).filter Nat.Prime
  -- every bad a has q² | a for some q ∈ Q
  have hsub : {a ∈ A | Sifted N Ny a ∧ ¬ Squarefree a} ⊆
      Q.biUnion (fun q => (Ioc 0 N).filter (fun a => q * q ∣ a)) := by
    intro a ha
    obtain ⟨haA, hs, hsq⟩ := mem_filter.1 ha
    obtain ⟨h0, hlt, hcop⟩ := hAN a haA
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push_neg at hsq
    obtain ⟨q, hq, hqq⟩ := hsq
    have hqa : q ∣ a := dvd_trans (dvd_mul_right q q) hqq
    have hk := (sifted_iff h0 hcop _).1 hs q ((mem_pf h0).2 ⟨hq, hqa⟩)
    have hqN : q ≤ N := (Nat.le_of_dvd h0 hqa).trans hlt.le
    rw [mem_biUnion]
    refine ⟨q, mem_filter.2 ⟨mem_Icc.2 ⟨Nat.ceil_le.2 hk, hqN⟩, hq⟩, mem_filter.2
      ⟨mem_Ioc.2 ⟨h0, hlt.le⟩, hqq⟩⟩
  calc
    (Esq A N k1 : ℝ) ≤ ∑ q ∈ Q, ((N / (q * q) : ℕ) : ℝ) := by
      unfold Esq
      have h := (card_le_card hsub).trans card_biUnion_le
      calc (#{a ∈ A | Sifted N Ny a ∧ ¬ Squarefree a} : ℝ)
          ≤ ((∑ q ∈ Q, #((Ioc 0 N).filter (fun a => q * q ∣ a)) : ℕ) : ℝ) := by exact_mod_cast h
        _ = _ := by
          push_cast
          refine sum_congr rfl fun q _ => ?_
          rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ q ∈ Q, (N : ℝ) * (1 / (q : ℝ) ^ 2) := by
      apply sum_le_sum
      intro q hq
      calc
        ((N / (q * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * q) := by
          exact_mod_cast Nat.cast_div_le (α := ℝ) (m := N) (n := q * q)
        _ = _ := by ring
    _ ≤ ∑ m ∈ Icc M N, (N : ℝ) * (1 / (m : ℝ) ^ 2) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ N * (1 / ((M : ℝ) - 1)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_inv_sq_le' M hM2 N) (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (by linarith [Nat.le_ceil Ny])

/-- **Wu 2008 (2.2), Υ₁₁ repaired, with the error explicit.** -/
theorem lemma22_explicit (hA : Admissible k1 k2) (hN : 1 < N) (hNk : 1 < Ny)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (WL A N k1 k2) ≤ 4 * D12 A + 4 * (N / (Ny - 1)) := by
  calc
    _ ≤ (4 * D12 A + 4 * Esq A N k1 : ℝ) := by
      exact_mod_cast lemma22_sum A N k1 k2 hA hN hAN
    _ ≤ _ := by linarith [Esq_le A N k1 hNk hAN]

/-- Wu's set `A = {N − p : p < N prime, p ∤ N}`. -/
def wuA : Finset ℕ := ((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)).image (fun p => N - p)

lemma wuA_ok : ∀ a ∈ wuA N, 0 < a ∧ a < N ∧ a.Coprime N := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
  obtain ⟨hpN, hpr, hnd⟩ := by simpa only [mem_filter, mem_range] using hp
  have h2 := hpr.two_le
  refine ⟨by omega, by omega, ?_⟩
  have hc : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hpr).2 hnd
  exact (Nat.coprime_self_sub_left (by omega)).2 hc

/-- **(2.2) for Wu's own `A = {N − p}`, explicit error.** -/
theorem lemma22_wuA (hA : Admissible k1 k2) (hN : 1 < N) (hNk : 1 < Ny) :
    (WL (wuA N) N k1 k2) ≤ 4 * D12 (wuA N) + 4 * (N / (Ny - 1)) :=
  lemma22_explicit (wuA N) N k1 k2 hA hN hNk (wuA_ok N)

end

end GoldbachLean.Wu2008.WuSum
