module

public import GoldbachLean.Wu2008.Sieve
public import GoldbachLean.Wu2008.Counting
public import GoldbachLean.Wu2008.Real

/-!
# Wu's sieve sums

Swap the sum over prime tuples with the sum over sequence members. For a sifted member, apply
`Counting.accounting` to the set of its prime factors. All comparisons with real cutoffs are
exact: for an integer prime `p`, `p < y` means precisely `p < ⌈y⌉₊`.
-/

@[expose] public noncomputable section
namespace GoldbachLean.Wu2008.WuSum
open Finset WuSieve WuReal Counting
open scoped Classical ArithmeticFunction.Omega

/-! ## Index sets and Wu's sums -/

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)

/-- Pairs of primes below `N`, both coprime to `N`, with condition `C`. -/
def P2 (C : ℕ → ℕ → Prop) := (range N ×ˢ range N).filter fun ⟨p, q⟩ =>
  p.Prime ∧ q.Prime ∧ p.Coprime N ∧ q.Coprime N ∧ C p q

/-- Quadruples of primes below `N`, all coprime to `N`, with condition `C`. -/
def P4 (C : ℕ → ℕ → ℕ → ℕ → Prop) :=
  (range N ×ˢ range N ×ˢ range N ×ˢ range N).filter fun ⟨p, q, r, s⟩ =>
    p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ p.Coprime N ∧ q.Coprime N ∧ r.Coprime N ∧
      s.Coprime N ∧ C p q r s

local notation "Z" κ:arg => (N : ℝ) ^ (κ : ℝ)

local notation "W₁" => Z k1
local notation "W₂" => Z k2
local notation "M₀" => Z (WuReal.em k1)
local notation "E₀" => Z e13

-- Share the index and sieve parameters within each family. The ordinary pairs sift at W₁,
-- whereas the low-sifted pairs and quadruples exclude divisors of Np and sift at q.
local notation "singleTo " v:arg => ∑ p ∈ PS N W₁ v, S A p N W₁
local notation "plainPairs " C:arg => ∑ ⟨p, q⟩ ∈ P2 N (C N k1 k2), S A (p * q) N W₁
local notation "lowPairs " C:arg => ∑ ⟨p, q⟩ ∈ P2 N (C N k1), S A (p * q) (N * p) q
local notation "quads " C:arg => ∑ ⟨p, q, r, s⟩ ∈ P4 N (C N k1 k2), S A (p * q * r * s) (N * p) q

def Y1 := S A 1 N W₁
def Y2 := Y1 A N k2
def Y3 := singleTo E₀
def Y4 := singleTo M₀

variable (p₁ p₂ p₃ p₄ : ℕ)

-- The common upper bound on the second exceptional prime, p₂ < √(N / p₁).
local notation "pairFits" => p₁ * p₂ ^ 2 < N

def C5 := W₁ ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < W₂
def Y5 := plainPairs C5
def C6 := W₁ ≤ p₁ ∧ p₁ < W₂ ∧ W₂ ≤ p₂ ∧ p₂ < M₀
def Y6 := plainPairs C6
def C7 := M₀ ≤ p₁ ∧ p₁ < p₂ ∧ pairFits
def Y7 := lowPairs C7
def C8 := W₁ ≤ p₁ ∧ p₁ < E₀ ∧ E₀ ≤ p₂ ∧ pairFits
def Y8 := lowPairs C8
def C9 := W₂ ≤ p₁ ∧ p₁ < M₀ ∧ M₀ ≤ p₂ ∧ pairFits
/-- Υ₉ with the intended P(Np₁p₂) at level (N/p₁p₂)^{1/2}. -/
def Y9 := ∑ ⟨p, q⟩ ∈ P2 N (C9 N k1 k2),
  S A (p * q) (N * p * q) (Real.sqrt ((N : ℝ) / (p * q)))
def C10 := W₁ ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧ p₄ < W₂
def Y10 := quads C10
/-- Υ₁₁ with the repaired range `N ^ κ₂ ≤ p₄ < N^{1/2−3κ₁}`; Wu prints `p₄ < N^{1/2−2κ₁}/p₃`. -/
def C11 := W₁ ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
  p₃ < W₂ ∧ W₂ ≤ p₄ ∧ p₄ < M₀
def Y11 := quads C11

def D12 := #{a ∈ A | Ω a ≤ 2}
def Esq := #{a ∈ A | Sifted N W₁ a ∧ ¬ Squarefree a}

/-- The same signed sieve weight, evaluated in ℤ or ℝ. -/
scoped notation "weight[" R "]" A:arg N:arg k1:arg k2:arg =>
  (3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 : R) - Y3 A N k1 - Y4 A N k1
    - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2

-- A product of distinct prime factors divides the sequence member, even without squarefreeness.
local macro "factors_dvd" : tactic => `(tactic|
  grind only [← Nat.Coprime.mul_dvd_of_dvd_of_dvd, Nat.coprime_mul_iff_left, Nat.coprime_primes])

-- Expand the index sets and express all prime cutoffs in ℕ.
local macro "ranges" : tactic => `(tactic|
  simp only [edges, P2, P4, mem_union, PS, mem_filter, mem_product,
    mem_coe, mem_range, C5, C6, C7, C8, C9, C10, C11, ← Nat.lt_ceil (α := ℝ), ← Nat.ceil_le (α := ℝ)])

/-- Wu's inequality, summed over any allowed sequence, with the exact square-factor error. -/
theorem lemma22_sum (hA : Admissible k1 k2) (hN : 1 < N)
    (hAN : ∀ a ∈ A, a eligibleFor N) :
    weight[ℤ] A N k1 k2 ≤ 4 * D12 A + 4 * Esq A N k1 := by
  obtain ⟨hwz, hzm, hme, hprod⟩ : W₁ ≤ W₂ ∧ W₂ ≤ M₀ ∧ M₀ ≤ E₀ ∧ Z 1 ≤ W₂ * M₀ * E₀ ^ 2 := by
    simp (disch := norm_cast <;> omega) only [← Real.rpow_mul_natCast, ← Real.rpow_add,
      Real.rpow_le_rpow_left_iff, WuReal.em, e13]
    grind [Admissible]
  rw [Real.rpow_one] at hprod
  -- Transpose every double sum; after taking a single member of A, the inner sums
  -- are again counts of prime tuples.
  unfold Y2 Y1 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 D12 Esq S
  simp only [card_filter, sum_comm (t := A)]
  push_cast
  simp only [mul_sum (s := A), ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_le_sum; intro a ha
  simp only [sum_boole]
  obtain ⟨h0, haN, hc⟩ := hAN a ha
  -- For an unsifted member all the positive contributions vanish.
  by_cases! hs : ¬ Sifted N W₁ a
  · have hs' : ¬ Sifted N W₂ a := by grind [Sifted]
    simp [hs, hs']; omega
  have mem (p) (h : p ∈ a.primeFactors) : p.Prime ∧ p ∣ a ∧ p < N ∧ p.Coprime N ∧ ⌈W₁⌉₊ ≤ p := by
    grind [sifted_iff h0.ne' hc, Nat.le_of_mem_primeFactors h, hc.coprime_dvd_left]
  simp only [one_dvd, hs, ite_true, true_and, mul_one, sifted_iff h0.ne' hc]
  replace hzm := Nat.ceil_mono hzm
  rw [add_assoc (3 + _), ← Nat.cast_add]
  refine' le_trans ?_ ((accounting (s := a.primeFactors) hzm (Nat.ceil_mono hme) ?_).trans ?_)
  · gcongr
    · -- Υ₅ and Υ₆ count disjoint families of edges, separated by the second prime.
      rw [← card_union_of_disjoint]
      · apply card_le_card; intro ⟨x, y⟩; ranges
        grind [dvd_of_mul_left_dvd, dvd_of_mul_right_dvd]
      · rw [disjoint_left]; intro ⟨x, y⟩; ranges; omega
    all_goals apply card_le_card; intro p; ranges; grind
  · intro p q t hd hpq hq ht
    simp only [hd, forall_mem_insert] at mem
    obtain ⟨r, hr⟩ := ht
    have hqr := hq r hr
    have d3 : p * q * r ∣ a := by factors_dvd
    have d2 := dvd_of_mul_right_dvd d3
    have h2 : p * q ^ 2 < N := lt_of_le_of_lt (by rw [pow_two, ← mul_assoc]; gcongr)
      ((Nat.le_of_dvd h0 d3).trans_lt haN)
    have hl : Sifted (N * p) q a := by simp [factors h0.ne', hd]; grind
    -- p * q * r divides a < N, so p < N ^ (1/3) and p * q² < N.
    have he : p < ⌈E₀⌉₊ := by
      rw [Nat.lt_ceil, e13, one_div, Real.lt_rpow_inv_iff_of_pos, Real.rpow_ofNat] <;> try positivity
      norm_cast
      exact lt_of_le_of_lt (by rw [pow_succ']; gcongr) h2
    refine ⟨he, ?_, ?_, ?_, ?_⟩
    · -- Prefix each tail edge with the two least primes. Its last prime decides between
      -- Υ₁₀ and the repaired Υ₁₁.
      apply le_trans (card_le_card_of_injOn (fun v => (p, q, v)) ?_ (by simp [Set.InjOn])) (card_union_le ..)
      rintro ⟨x, y⟩; ranges
      intro h
      have d4 : p * q * x * y ∣ a := by factors_dvd
      grind
    all_goals
      intros; apply card_pos.mpr ⟨(p, q), ?_⟩; ranges
    · grind
    · grind
    -- In Υ₉, the remaining factors are at least E₀. The last admissibility condition
    -- gives N ≤ W₂ * M₀ * E₀², which implies the square-root sieve condition.
    refine ⟨by grind, d2, ?_⟩
    simp [factors h0.ne', hd, dvd_mul_of_dvd_left, -Real.sqrt_div]
    intro x hx; left
    rw [Real.sqrt_le_left, div_le_iff₀, mul_comm] <;> try positivity [mem.1.1.pos, mem.2.1.1.pos]
    apply hprod.trans; gcongr <;> grind [below, card_eq_zero, filter_eq_empty_iff, Nat.ceil_le]
  · -- For a squarefree member Ω counts distinct factors; otherwise Esq pays its full weight.
    have card (h : Squarefree a) : #a.primeFactors = Ω a := List.toFinset_card_of_nodup h.nodup_primeFactorsList
    grind

end GoldbachLean.Wu2008.WuSum
