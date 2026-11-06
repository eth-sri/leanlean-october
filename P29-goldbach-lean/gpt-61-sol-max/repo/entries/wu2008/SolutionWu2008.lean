import Mathlib

/-!
# Wu's double sieve inequality, with the last range repaired

The proof has three parts: a finite weighted counting argument, its application
via logarithmic prime weights to the sieve sums, and a reciprocal-square bound
for the non-squarefree error. Li's version is the corresponding specialization.
-/

open Finset Classical
set_option quotPrecheck false
set_option maxHeartbeats 3000000
noncomputable section

variable (A : Finset ℕ) (N e D : ℕ) (k1 k2 y w z : ℝ) (a p₁ p₂ p₃ p₄ : ℕ)

namespace GoldbachLean.Wu2008.WuSieve

/-- `a` survives sifting by `P(D) = {q prime : q ∤ D}` up to `y`. -/
abbrev Sifted :=
  ∀ q, q ∣ a → q.Prime → y ≤ q ∨ q ∣ D

/-- `S(A_e; P(D), y)`. -/
abbrev S :=
  #{a ∈ A | e ∣ a ∧ Sifted D y a}

/-- The primes `p` with `w ≤ p < z` and `(p, N) = 1`. -/
abbrev PS :=
  {p ∈ range ⌈z⌉₊ | Nat.Prime p ∧ w ≤ p ∧ p.Coprime N}

end GoldbachLean.Wu2008.WuSieve

attribute [local grind .] Nat.Prime.coprime_iff_not_dvd Nat.coprime_primes Nat.coprime_mul_iff_right
  Nat.Coprime.mul_dvd_of_dvd_of_dvd Nat.prod_primeFactors_dvd Nat.toFinset_factors
  Nat.ceil_natCast Nat.cast_pos prod_pos card_sdiff_add_card_eq_card
  Nat.dvd_sub_iff_right Nat.dvd_gcd
attribute [local grind →] Nat.Coprime.coprime_dvd_left Nat.le_of_dvd Nat.Prime.one_lt Real.rpow_lt_rpow_of_exponent_lt
  dvd_of_mul_left_dvd dvd_of_mul_right_dvd List.toFinset_card_of_nodup
  Squarefree.nodup_primeFactorsList min'_lt_of_mem_erase_min'

namespace GoldbachLean.Wu2008.WuReal

/-- Wu's values, κ₁ = 1/13.27 and κ₂ = 1/8.24. The lemma is proved for every admissible pair. -/
abbrev wk1 : ℝ := 100 / 1327
abbrev wk2 : ℝ := 100 / 824
variable (d : Finset ℕ) (w : ℕ → ℝ)

abbrev em := 0.5 - 3 * k1
abbrev e13 : ℝ := 3⁻¹

/-- Wu's hypotheses on κ₁, κ₂ for Lemma 2.2, p. 371: κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2,
3κ₁ − κ₂ < 1/6. The last condition is weakened to `≤` here. The equivalent
threshold form below shares `em`: `κ₂ < em κ₁ ≤ 1/3 ≤ em κ₁ + κ₂`. -/
abbrev Admissible :=
  k1 < k2 ∧ em k1 ∈ Set.Ioc k2 e13 ∧ e13 ≤ em k1 + k2

attribute [scoped simp] Admissible filter_insert Nat.Prime.pos Nat.Prime.ne_zero sq_pos_iff
  Nat.choose_succ_succ Nat.choose_eq_zero_of_lt StrictMonoOn

lemma wu_admissible : Admissible wk1 wk2 := by
  norm_num

/-- For `(a, b) ∈ d ×ˢ d`, this says that `a, b` are the two least members of `d`. -/
abbrev low2 a b := ∀ q ∈ d, b ≤ q ↔ q ≠ a

/-! ## Finset helpers -/

lemma exists_two_least : 2 ≤ d.card → ∃ p ∈ d ×ˢ d, low2 d p.1 p.2 := by
  intro h
  have := one_lt_card_iff_nontrivial.mp h
  use (d.min' this.nonempty, (d.erase (d.min' this.nonempty)).min' this.erase_nonempty)
  grind [min'_mem, min'_le]

/-- **Wu 2008 Lemma 2.2, Υ₁₁ repaired, pointwise in the real exponent model.** -/
theorem Admissible.pointwise : Admissible k1 k2 → StrictMonoOn w d → ∀ _hs : d.sum w < 1,
    let U t := {e ∈ d | w e < t}
    let Uq T := #{t ∈ d ×ˢ d ×ˢ T | t.2.1 < Prod.fst t.2.2 ∧ low2 d t.1 t.2.1}
    let V T := #{p ∈ d ×ˢ d | w p.1 + 2 * w p.2 < 1 ∧ low2 d p.1 p.2 ∧ T p}
    let A := U k2
    let C := U (em k1)
    let E := U e13
    let B := C \ A
    ite (A = ∅) 4 3 + A.card.choose 2 + A.card * B.card ≤
      ite (d.card ≤ 2) 4 0 + Uq (A ×ˢ B) + Uq {p ∈ A ×ˢ A | p.1 < p.2}
        + V (fun p => p.1 ∈ B ∧ em k1 ≤ w p.2 ∧
            ∀ q ∈ (d.erase p.1).erase p.2, 1 ≤ w p.1 + w p.2 + 2 * w q)
        + V (fun p => w p.1 < e13 ∧ e13 ≤ w p.2)
        + 2 * V (fun p => em k1 ≤ w p.1) + C.card + E.card := by
  intros
  expose_names
  simp_all
  have : C.card ≤ E.card := by
    gcongr
    grind
  by_cases hA : 2 ≤ A.card
  · -- at least two small exponents
    choose p hq using exists_two_least _ hA
    let A2 := (A.erase p.1).erase p.2
    have : A.card = A2.card + 2 := by grind
    have :
        A2.card.choose 2 ≤ Uq {p ∈ A ×ˢ A | p.1 < p.2} ∧ A2.card * B.card ≤ Uq (A ×ˢ B) := by
      constructor <;> simp [← card_product_filter_lt, ← card_product] <;>
        apply card_le_card_of_injOn <| Prod.mk p.1 ∘ Prod.mk p.2 <;> intro <;> grind
    simp_all
    grind
  -- With fewer than two small exponents, isolate the least three members.
  split_ifs <;> try grind
  all_goals
    choose p hq using exists_two_least d (by omega)
    choose c hmin using exists_min_image ((d.erase p.1).erase p.2) w
      (card_pos.1 (by grind))
    have hmin3 : {p.1, p.2, c} ⊆ d := by grind
    have ht t := card_le_card (filter_subset_filter (w · < t)
      hmin3)
    simp at ht
    have := _hs.trans_le' (sum_le_sum_of_subset_of_nonneg hmin3
      (by grind [ht k2]))
    grind (splits := 40) [card_filter_eq_zero_iff]

end GoldbachLean.Wu2008.WuReal

open GoldbachLean.Wu2008.WuSieve GoldbachLean.Wu2008.WuReal
namespace GoldbachLean.Wu2008.WuSum

/-! ## Index sets and Wu's sums -/

/-- All tuple indices use the same prime domain. -/
local notation "P" => PS N 0 N

abbrev P2 C := filter (Function.uncurry C) (P ×ˢ P)
/-- Repeated uncurrying supplies the predicate on right-associated quadruples. -/
abbrev P4 C := filter
  (Function.uncurry <| Function.uncurry ∘ Function.comp Function.uncurry ∘ C)
  (P ×ˢ P ×ˢ P ×ˢ P)

local notation "X" => (N : ℝ)
local notation "z₁" => X ^ k1
local notation "z₂" => X ^ k2
local notation "z₃" => X ^ em k1
local notation "S₁" => (S A · N z₁)

def Y1 := S₁ 1
def Y2 := Y1
def Y3 := Finset.sum (PS N z₁ (X ^ e13)) S₁
def Y4 := Finset.sum (PS N z₁ z₃) S₁
local notation lo " ◁ " mid:80 => lo ≤ p₁ ∧ ↑p₁ < mid ∧ mid ≤ p₂
abbrev C5 := z₁ ◁ p₂ ∧ ↑p₂ < z₂
local notation "YS" C => ∑ q ∈ P2 N C, S₁ (q.1 * q.2)
def Y5 := YS C5 N k1 k2
abbrev C6 := z₁ ◁ z₂ ∧ ↑p₂ < z₃
def Y6 := YS C6 N k1 k2
local notation "Small" => p₁ * p₂ ^ 2 < N
abbrev C7 := z₃ ◁ p₂ ∧ Small
local notation "YP" C => ∑ q ∈ P2 N C, S A (q.1 * q.2) (N * q.1) q.2
def Y7 := YP C7 N k1
abbrev C8 := z₁ ◁ X ^ e13 ∧ Small
def Y8 := YP C8 N k1
abbrev C9 := z₂ ◁ z₃ ∧ Small
/-- Υ₉ with the intended P(Np₁p₂) at level (N/p₁p₂)^{1/2}. -/
def Y9 := ∑ q ∈ P2 N (C9 N k1 k2),
  let p := q.1 * q.2
  S A p (N * p) (Real.sqrt (X / p))
local notation "L" => z₁ ◁ p₂ ∧ p₂ < p₃
abbrev C10 := L ∧ C5 N k1 k2 p₃ p₄
local notation "YQ" C => ∑ q ∈ P4 N C,
  S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1
def Y10 := YQ C10 N k1 k2
/-- Υ₁₁ with the repaired range `N^κ₂ ≤ p₄ < N^{1/2−3κ₁}`; Wu prints `p₄ < N^{1/2−2κ₁}/p₃`. -/
abbrev C11 := L ∧ C6 N k1 k2 p₃ p₄
def Y11 := YQ C11 N k1 k2

abbrev D12 := #{a ∈ A | a.primeFactorsList.length ≤ 2}
abbrev Esq := #{a ∈ A | Sifted N z₁ a ∧ ¬ Squarefree a}

/-- The common weighted sieve sum; the coefficient type is inferred. -/
local notation A "RHS" =>
  3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 - Y3 A N k1 - Y4 A N k1
      - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2

/-- Wu's set `A = {N − p : p < N prime, p ∤ N}`. -/
abbrev wuA := image (N - ·) P

/-! ## The summed lemma -/

variable (hA : Admissible k1 k2) (hN : 1 < N)
include hA hN

/-- **Wu 2008 Lemma 2.2, (2.2), summed, Υ₁₁ repaired.** -/
theorem lemma22_sum
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (A RHS : ℤ)
      ≤ 4 * D12 A + 4 * Esq A N k1 := by
  rify at hN
  unfold Y2 Y1 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11
  push_cast [card_filter, sum_comm (t := A), mul_sum A, ← sum_sub_distrib, ← sum_add_distrib]
  gcongr with a
  by_cases hs : Sifted N z₁ a
  · have := hA.pointwise k1 k2 a.primeFactors (Real.logb N ·)
      (by
        intro
        intros
        dsimp
        gcongr
        grind)
      (by
        rw [← Real.logb_prod, Real.logb_lt_iff_lt_rpow, ← Nat.cast_prod]
        all_goals
          norm_cast
          grind)
    simp +contextual (disch := simp_all) only
      [low2, ← Real.logb_rpow_eq_mul_logb_of_pos, ← Real.logb_mul,
        Real.logb_lt_iff_lt_rpow, Real.le_logb_iff_rpow_le] at this
    zify [← card_product_filter_lt, ← card_product] at this
    simp [-Real.sqrt_div]
    refine le_trans ?_ (this.trans ?_)
    all_goals gcongr
    all_goals
      clear this
      try intro
      simp +contextual (disch := simp_all) only
        [filter_eq_empty_iff, mem_filter, mem_product, mem_range, Nat.lt_ceil, Sifted,
         Nat.Prime.dvd_mul, Nat.prime_dvd_prime_iff_eq,
         Real.sqrt_le_left, div_le_iff₀, mul_assoc] at *
      norm_cast at *
      grind [=_ Nat.cast_le (α := ℝ)]
  -- not sifted at N^κ₁: every positive term vanishes
  simp [hs]
  grind

/-- **(2.2) for Wu's own `A = {N − p}`, explicit error.** -/
theorem lemma22_wuA :
    1 < z₁ → (wuA N RHS : ℝ)
      ≤ 4 * D12 (wuA N) + 4 * (N / (z₁ - 1)) := by
  intro
  have := lemma22_sum (wuA N) N k1 k2 hA hN (by
    grind [Nat.coprime_self_sub_left])
  rify at this
  apply this.trans
  gcongr
  set M := ⌈z₁ - 1⌉₊
  grw [show Esq _ N k1 ≤ ∑ q ∈ Ioc M (max M N), N / q ^ 2 by
    -- Charge each bad member to a prime-square divisor.
    simp_rw [← Nat.Ioc_filter_dvd_card_eq_div]
    apply card_biUnion_le.trans'
    apply card_le_card
    intro a ha
    simp [Nat.squarefree_iff_prime_squarefree] at ha
    choose q hq using ha.2.2
    have : z₁ ≤ q ∧ 0 < a := by
      grind
    simp +zetaDelta [pow_two]
    use q
    grind [Nat.ceil_le.mpr this.1]
  ]
  push_cast
  grw [Nat.cast_div_le]
  push_cast [div_eq_mul_inv, ← mul_sum]
  grw [sum_Ioc_inv_sq_le_sub (by positivity), sub_le_self]
  all_goals bound
end GoldbachLean.Wu2008.WuSum

namespace GoldbachLean.Li2024.Lemma31

open GoldbachLean.Wu2008.WuSum

/-- Li's κ₁ = 1/11.49. -/
abbrev lk1 : ℝ := 100 / 1149
/-- Li's κ₂ = 1/6.18. -/
abbrev lk2 : ℝ := 100 / 618

/-- Li's parameters satisfy Wu's hypotheses. -/
theorem li_admissible : Admissible lk1 lk2 := by
  norm_num

/-- **Li 2024, Lemma 3.1, with S₁₅'s range repaired**, for A = {N − p}, explicit error. -/
theorem lemma31_repaired : type_of% (lemma22_wuA N lk1 lk2 li_admissible) :=
  lemma22_wuA N lk1 lk2 li_admissible

end GoldbachLean.Li2024.Lemma31

end
