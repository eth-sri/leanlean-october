module

public import GoldbachLean.Wu2008.Sieve
public import GoldbachLean.Wu2008.Real

/-! # Wu's summed inequality

After interchanging the sums it suffices to count on the distinct prime factors
of each sifted member. The thresholds satisfy `N^κ₂ < N^(1/2-3κ₁) ≤ N^(1/3)`.
If there are two small factors, the quadruple sums count the pairs beyond the
first two. If there are at least three factors but fewer than two small ones,
the least factors give witnesses for the negative terms.
-/

namespace GoldbachLean.Wu2008.WuSum
open Finset WuSieve WuReal
open scoped ArithmeticFunction.Omega Classical

@[expose] public noncomputable section

/-- Pairs of primes below `N`, both coprime to `N`, with condition `C`. -/
def P2 (N : ℕ) (C : ℕ → ℕ → Prop) :=
  {q ∈ range N ×ˢ range N | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧ C q.1 q.2}

/-- Quadruples of primes below `N`, all coprime to `N`, with condition `C`. -/
def P4 (N : ℕ) (C : ℕ → ℕ → ℕ → ℕ → Prop) :=
  {q ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N | q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
    q.2.2.2.Prime ∧ q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
    C q.1 q.2.1 q.2.2.1 q.2.2.2}

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)

local notation "Z" => fun t : ℝ => (N : ℝ) ^ t
local notation "K" => Z k1
local notation "L" => Z k2
local notation "M" => Z (WuReal.em k1)
local notation "T" => Z e13

-- Use the same single-prime summand in the definitions and bounds.
local notation "SingleSum(" B "," x ")" => ∑ p ∈ PS N K x, S B p N K
-- Common summands within the pair and quadruple families.
section
set_option quotPrecheck false
local notation "QuadSum(" C ")" =>
  (P4 N C).sum fun q => S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1

local notation "BasePairs(" C ")" => (P2 N C).sum fun q => S A (q.1 * q.2) N K
local notation "LowPairs(" C ")" => (P2 N C).sum fun q => S A (q.1 * q.2) (N * q.1) q.2

def Y1 := S A 1 N K
def Y2 := S A 1 N L
def Y3 := SingleSum(A, T)
def Y4 := SingleSum(A, M)
def C5 (p₁ p₂ : ℕ) := K ≤ p₁ ∧ p₁ < p₂ ∧ (p₂ : ℝ) < L
def Y5 := BasePairs(C5 N k1 k2)
def C6 (p₁ p₂ : ℕ) := K ≤ p₁ ∧ (p₁ : ℝ) < L ∧
  L ≤ p₂ ∧ (p₂ : ℝ) < M
def Y6 := BasePairs(C6 N k1 k2)
def C7 (p₁ p₂ : ℕ) := M ≤ p₁ ∧ p₁ < p₂ ∧ p₁ * p₂ ^ 2 < N
def Y7 := LowPairs(C7 N k1)
def C8 (p₁ p₂ : ℕ) := K ≤ p₁ ∧ (p₁ : ℝ) < T ∧
  T ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
def Y8 := LowPairs(C8 N k1)
def C9 (p₁ p₂ : ℕ) := L ≤ p₁ ∧ (p₁ : ℝ) < M ∧
  M ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
/-- Υ₉ with the intended P(Np₁p₂) at level (N/p₁p₂)^{1/2}. -/
def Y9 := ∑ q ∈ P2 N (C9 N k1 k2),
  S A (q.1 * q.2) (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2)))
def C10 (p₁ p₂ p₃ p₄ : ℕ) := K ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧
  (p₄ : ℝ) < L
def Y10 := QuadSum(C10 N k1 k2)
/-- Υ₁₁ with the repaired range `N^κ₂ ≤ p₄ < N^{1/2−3κ₁}`; Wu prints `p₄ < N^{1/2−2κ₁}/p₃`. -/
def C11 (p₁ p₂ p₃ p₄ : ℕ) := K ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
  (p₃ : ℝ) < L ∧ L ≤ p₄ ∧ (p₄ : ℝ) < M
def Y11 := QuadSum(C11 N k1 k2)
end

def D12 := #{a ∈ A | Ω a ≤ 2}
def Esq := #{a ∈ A | Sifted N K a ∧ ¬ Squarefree a}

scoped notation "WuLHS(" R "," A "," N "," k "," l ")" =>
  (3 * Y1 A N k + Y2 A N l + Y5 A N k l + Y6 A N k l : R) - Y3 A N k - Y4 A N k
    - 2 * Y7 A N k - Y8 A N k - Y9 A N k l - Y10 A N k l - Y11 A N k l

section
variable {N k1 k2} {a : ℕ}
local notation "d" => a.primeFactors
attribute [local simp] S filter_singleton

/-- Pointwise counting on the distinct prime divisors of a sifted member. -/
private lemma per_a (hA : Admissible k1 k2) (hN : (1 : ℝ) < N) :
    0 < a ∧ a < N ∧ a.Coprime N →
      WuLHS(ℤ, {a}, N, k1, k2) ≤ 4 * D12 {a} + 4 * Esq {a} N k1 := by
  rintro ⟨ha, haN, hc⟩
  have zm := Real.monotone_rpow_of_base_ge_one hN.le
  by_cases hs : Sifted N K a
  swap
  · have hle := zm hA.2.1.le
    have hs' : ¬ Sifted N L a := by grind [Sifted]
    simp [Y1, Y2, Y5, Y6, hs, hs']
    omega
  suffices h : WuLHS(ℤ, {a}, N, k1, k2) ≤ if #d ≤ 2 then 4 else 0 by
    refine h.trans ?_
    have hΩ (hsf : Squarefree a) : Ω a = #d :=
      (List.toFinset_card_of_nodup hsf.nodup_primeFactorsList).symm
    simp [D12, Esq, apply_ite, hs]
    grind only
  obtain ⟨h1, -, h3, h4⟩ := hA
  have hlm : L ≤ M := zm (by unfold WuReal.em; linarith)
  have hmt : M ≤ T := zm (by unfold WuReal.em e13; linarith)
  have hk := (sifted_coprime ha.ne' hc).mp hs
  have pf (p : ℕ) (hp : p ∈ d) : p < N ∧ p.Prime ∧ p.Coprime N ∧ p ∣ a := by
    grind [→ Nat.le_of_mem_primeFactors, → Nat.Coprime.coprime_dvd_left]
  let below (x : ℝ) := (d).filter fun p : ℕ => (p : ℝ) < x
  -- Small and middle factors, respectively.
  let F := below L
  let G := below M \ F
  have nested : Monotone below := by grind [Monotone]
  have cf : #G + #F = #(below M) := card_sdiff_add_card_eq_card (nested hlm)
  have c34 := card_le_card (nested hmt)
  have single (x : ℝ) : #(below x) ≤ SingleSum({a}, x) := by
    simp [apply_ite]
    apply card_le_card
    grind [PS, ← Nat.lt_ceil]
  have y3 : #(below T) ≤ Y3 {a} N k1 := single T
  have y4 : #(below M) ≤ Y4 {a} N k1 := single M
  have y2 : Sifted N L a ↔ #F = 0 := by
    simp [sifted_coprime ha.ne' hc, F, below, filter_eq_empty_iff]
  have cast_lt {x y : ℕ} : x < y → (x : ℝ) < y := Nat.cast_lt.mpr
  have ⟨y5, y6⟩ : Y5 {a} N k1 k2 ≤ (#F).choose 2 ∧ Y6 {a} N k1 k2 ≤ #F * #G := by
    simp [Y5, Y6, apply_ite]
    rw [← card_product_filter_lt, ← card_product]
    constructor <;> apply card_le_card <;> rintro ⟨p, q⟩ <;>
      grind [P2, C5, C6, → dvd_of_mul_left_dvd, → dvd_of_mul_right_dvd]
  norm_num [Y1, Y2, hs, y2, -card_eq_zero, apply_ite (f := Finset.card)]
  by_cases hn : #d ≤ 2
  · have hd : #(below M) ≤ #d := card_filter_le ..
    have hf : #F ≤ 2 := by omega
    interval_cases h : #F <;> norm_num [h, Nat.choose] at y5 y6 ⊢ <;> omega
  rw [ite_eq_right hn]
  -- Decompose the sorted factors once for both kinds of witnesses.
  have ord := sortedLT_sort d
  have len : 2 < (sort d).length := by simpa using Nat.lt_of_not_ge hn
  have eqd := sort_toFinset d (· ≤ ·)
  generalize sort d = v at *
  rcases v with _ | ⟨p, _ | ⟨q, _ | ⟨r, u⟩⟩⟩ <;>
    simp at len
  have nd := ord.nodup
  have ord := ord.pairwise
  simp only [List.pairwise_cons] at ord
  have ⟨hp, hq', hr⟩ : p ∈ d ∧ q ∈ d ∧ r ∈ d := by simp [← eqd]
  have hpq := ord.1 q (by simp)
  have hqr := ord.2.1 r (by simp)
  have sift {D : ℕ} {z : ℝ} (hpD : p ∣ D) (hqD : z ≤ q ∨ q ∣ D) (hz : z ≤ r) : Sifted D z a := by
    grind [Sifted, List.mem_toFinset]
  have low := sift (dvd_mul_left p N) (Or.inl le_rfl) (Nat.cast_le.mpr hqr.le)
  -- Extend each residual pair by (p, q) to obtain a distinct quadruple.
  by_cases hqL : (q : ℝ) < L
  · let R := F \ {p, q}
    have hR : #R + 2 = #F := by
      rw [← card_pair hpq.ne]
      exact card_sdiff_add_card_eq_card (by grind)
    have ⟨y10, y11⟩ : (#R).choose 2 ≤ Y10 {a} N k1 k2 ∧ #R * #G ≤ Y11 {a} N k1 k2 := by
      simp [Y10, Y11, apply_ite]
      rw [← card_product_filter_lt, ← card_product]
      constructor <;>
        refine card_le_card_of_injOn (fun y => (p, q, y.1, y.2)) ?_ (by simp [Set.InjOn, Prod.ext_iff])
      all_goals
        rintro ⟨x, y⟩ hxy
        simp [R, F, G, below, -Nat.mem_primeFactors] at hxy
        have ⟨hqx, pr⟩ : q < x ∧ p * q * x * y ∣ a := by
          grind only [List.mem_toFinset, List.mem_cons,
            Nat.coprime_primes, Nat.coprime_mul_iff_left, ← Nat.Coprime.mul_dvd_of_dvd_of_dvd]
        grind [P4, C10, C11]
    simp [← hR, Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_mul] at y5 y6
    omega
  -- With at most one small factor, (p, q) supplies the witnesses for Y₇–Y₉.
  have hF : #F ≤ 1 := card_le_one.mpr (by grind [List.mem_toFinset])
  have pr : p * q * r ∣ a := by
    grind only [Nat.coprime_primes, Nat.coprime_mul_iff_left, ← Nat.Coprime.mul_dvd_of_dvd_of_dvd]
  have prod2 : p * q ^ 2 < N := by
    nlinarith only [Nat.le_of_dvd ha pr, haN, hqr, Nat.zero_le (p*q)]
  have cube : T ^ 3 = (N : ℝ) := by
    norm_num [← Real.rpow_mul_natCast (Nat.cast_nonneg _), e13]
  have pT : (p : ℝ) < T := by
    apply lt_of_pow_lt_pow_left₀ 3 (by positivity)
    rw [cube]
    exact_mod_cast (lt_of_le_of_lt (by rw [pow_succ']; gcongr) prod2 : p ^ 3 < N)
  have ⟨h7, h8, h9⟩ : (M ≤ p → 1 ≤ Y7 {a} N k1) ∧ (T ≤ q → 1 ≤ Y8 {a} N k1) ∧
      (#F = 0 → (p : ℝ) < M → M ≤ q → T ≤ r → 1 ≤ Y9 {a} N k1 k2) := by
    have hpq' := dvd_of_mul_right_dvd pr
    simp [Y7, Y8, Y9, apply_ite, -card_eq_zero]
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> refine ⟨(p, q), ?_⟩
    -- Only Y₉ needs the square-root cutoff instead of q.
    rotate_left 2
    rename_i hz pm qm rt
    have pL := le_of_not_gt (card_filter_eq_zero_iff.mp hz p hp)
    -- Admissibility puts the square-root cutoff at most T.
    have hroot : Real.sqrt ((N : ℝ) / (p * q)) ≤ T := by
      rw [Real.sqrt_le_left (by positivity)]
      apply div_le_of_le_mul₀ (by positivity) (sq_nonneg _)
      grw [← pL, ← qm, ← Real.rpow_add (zero_lt_one.trans hN)]
      refine cube.symm.trans_le ?_
      rw [pow_succ]
      gcongr
      exact zm (by unfold WuReal.em e13; linarith)
    have hs9 := sift ((dvd_mul_left p N).mul_right q) (Or.inr (by simp)) (hroot.trans rt)
    simp at hs9
    all_goals grind [P2, C7, C8, C9]
  -- The cutoff counts include the three least factors that fall below them.
  simp only [below, ← eqd, nd.card_eq_countP, List.countP_cons, decide_eq_true_eq] at y3 y4 cf
  clear * - y3 y4 y5 y6 h7 h8 h9 cf pT hF
  grind only [← Nat.choose_eq_zero_of_lt]

end

/-- **Wu 2008, Lemma 2.2**, with the repaired range of Υ₁₁. -/
theorem lemma22_sum (hA : Admissible k1 k2) (hN : 1 < N)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    WuLHS(ℤ, A, N, k1, k2) ≤ 4 * D12 A + 4 * Esq A N k1 := by
  simpa only [Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, S, D12, Esq, Nat.cast_sum,
    natCast_card_filter, sum_singleton, sum_comm (t := A), mul_sum, ← sum_sub_distrib, ← sum_add_distrib] using
    (sum_le_sum fun a ha => per_a hA (by exact_mod_cast hN) (hAN a ha))

end
end GoldbachLean.Wu2008.WuSum
