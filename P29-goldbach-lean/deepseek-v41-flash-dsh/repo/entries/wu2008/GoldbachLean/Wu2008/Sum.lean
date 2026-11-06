module

public import GoldbachLean.Wu2008.Sieve
public import GoldbachLean.Wu2008.Int

/-!
T1, unit U-1124, PC run 20261020T0003Z-10609. P0043 J. Wu, Acta Arith. 131, 2008, arXiv 0709.3764,
Lemma 2.2, inequality (2.2), in Wu's SUMMED form, with Υ₁₁ repaired to p₄ < N^{1/2−3κ₁}, F-0050:

  3Υ₁ + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁ ≤ 4 D₁₂ + 4 E,

for any finite set A of integers 0 < a < N coprime to N, as Wu's A = {N − p} is apart from p | N,
and any κ₁, κ₂ under Wu's hypotheses, `Admissible`. The Υ are Wu's sieve sums as read on
ar5iv 0709.3764 on 2026-10-20, with S(A_d; P(D), y) = #{a ∈ A : d | a, no prime q < y with q ∤ D
divides a}, the lab's `WuSieve.S`, and the intended sieve sets: Υ₉ at P(Np₁p₂), Υ₁₀ and Υ₁₁ at P(Np₁);
Wu prints P(Np₁) and P(N), under which those sums vanish, see STATEMENTS.md U-5411.
D₁₂ = #{a ∈ A : Ω(a) ≤ 2}. E = #{a ∈ A : a sifted at N^κ₁, a not squarefree} is Wu's O(N^{1−κ₁}).
Wu's P(z) uses p ≤ z; we read p < z as the lab does for Lemma 2.1, a cosmetic boundary.
Proof: swap each sum with the sum over a, then for each a either a is not sifted at N^κ₁, when
every positive term is 0, or it is, when each inner count is the integer term of
Wu2008Lemma22Int.lean and `pointwise_omega` applies.
KNOWN mathematics, Wu's lemma with its range fixed. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuSum
open Finset
open scoped ArithmeticFunction.Omega
open GoldbachLean.Wu2008.WuSieve (Sifted S PS mem_PS S_eq_sum sifted_mono)
open GoldbachLean.Wu2008.WuInt
open GoldbachLean.Wu2008.WuReal

@[expose] public noncomputable section
open scoped Classical

/-! ## Index sets and Wu's sums -/

/-- Pairs of primes below `N`, both coprime to `N`, with condition `C`. -/
def P2 (N : ℕ) (C : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧ C q.1 q.2}

/-- Quadruples of primes below `N`, all coprime to `N`, with condition `C`. -/
def P4 (N : ℕ) (C : ℕ → ℕ → ℕ → ℕ → Prop) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N | q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
    q.2.2.2.Prime ∧ q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
    C q.1 q.2.1 q.2.2.1 q.2.2.2}

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)

local notation "Ny" => fun (κ : ℝ) => (N : ℝ) ^ κ

def Y1 : ℕ := S A 1 N ((N : ℝ) ^ k1)
def Y2 : ℕ := S A 1 N ((N : ℝ) ^ k2)
def Y3 : ℕ := ∑ p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ e13), S A p N ((N : ℝ) ^ k1)
def Y4 : ℕ := ∑ p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ em k1), S A p N ((N : ℝ) ^ k1)
def C5 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ (p₂ : ℝ) < (N : ℝ) ^ k2
def Y5 : ℕ := ∑ q ∈ P2 N (C5 N k1 k2), S A (q.1 * q.2) N ((N : ℝ) ^ k1)
def C6 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ k2 ∧
  (N : ℝ) ^ k2 ≤ p₂ ∧ (p₂ : ℝ) < (N : ℝ) ^ em k1
def Y6 : ℕ := ∑ q ∈ P2 N (C6 N k1 k2), S A (q.1 * q.2) N ((N : ℝ) ^ k1)
def C7 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ em k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₁ * p₂ ^ 2 < N
def Y7 : ℕ := ∑ q ∈ P2 N (C7 N k1), S A (q.1 * q.2) (N * q.1) q.2
def C8 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ e13 ∧
  (N : ℝ) ^ e13 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
def Y8 : ℕ := ∑ q ∈ P2 N (C8 N k1), S A (q.1 * q.2) (N * q.1) q.2
def C9 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k2 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ em k1 ∧
  (N : ℝ) ^ em k1 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
/-- Υ₉ with the intended P(Np₁p₂) at level (N/p₁p₂)^{1/2}. -/
def Y9 : ℕ := ∑ q ∈ P2 N (C9 N k1 k2),
  S A (q.1 * q.2) (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2)))
def C10 (p₁ p₂ p₃ p₄ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧
  (p₄ : ℝ) < (N : ℝ) ^ k2
def Y10 : ℕ := ∑ q ∈ P4 N (C10 N k1 k2),
  S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1
/-- Υ₁₁ with the repaired range `N^κ₂ ≤ p₄ < N^{1/2−3κ₁}`; Wu prints `p₄ < N^{1/2−2κ₁}/p₃`. -/
def C11 (p₁ p₂ p₃ p₄ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
  (p₃ : ℝ) < (N : ℝ) ^ k2 ∧ (N : ℝ) ^ k2 ≤ p₄ ∧ (p₄ : ℝ) < (N : ℝ) ^ em k1
def Y11 : ℕ := ∑ q ∈ P4 N (C11 N k1 k2),
  S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1

def D12 : ℕ := #{a ∈ A | Ω a ≤ 2}
def Esq : ℕ := #{a ∈ A | Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a}

/-! ## Pointwise bridges -/

section bridges
variable {N} {a : ℕ} (ha0 : 0 < a) (haN : a < N) (hcop : a.Coprime N)
include ha0 haN hcop

omit haN hcop in
lemma mem_pf {p : ℕ} : p ∈ a.primeFactors ↔ p.Prime ∧ p ∣ a := by
  rw [Nat.mem_primeFactors]; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ha0.ne'⟩⟩

attribute [grind] mem_pf x_lt_iff rpow_le_iff lt_rpow_iff mul_sq_lt_iff lowP_iff

omit hcop in
lemma pf_lt {p : ℕ} (hp : p ∈ a.primeFactors) : p < N :=
  lt_of_le_of_lt (Nat.le_of_dvd ha0 (Nat.dvd_of_mem_primeFactors hp)) haN

omit ha0 haN in
lemma pf_cop {p : ℕ} (hp : p ∈ a.primeFactors) : p.Coprime N :=
  Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hcop

attribute [grind] pf_lt pf_cop

omit ha0 haN in
lemma prime_dvd_not_dvd_N {q : ℕ} (hq : q.Prime) (hqa : q ∣ a) : ¬ q ∣ N := fun h =>
  hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hqa h)

/-- Sifted by `P(N)` at `y` means every prime factor is at least `y`. -/
lemma sifted_iff (y : ℝ) : Sifted N y a ↔ ∀ p ∈ a.primeFactors, y ≤ (p : ℝ) := by
  constructor
  · intro h p hp
    obtain ⟨hpr, hpa⟩ := (mem_pf ha0).1 hp
    by_contra hlt
    exact h p hpr (not_le.1 hlt) (prime_dvd_not_dvd_N hcop hpr hpa) hpa
  · intro h q hq hqy _ hqa
    exact absurd (h q ((mem_pf ha0).2 ⟨hq, hqa⟩)) (not_le.2 hqy)

/-- Sifted by `P(Np₁)` at `p₂` is `lowP`. -/
lemma sifted_lowP {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) :
    Sifted (N * p₁) p₂ a ↔ lowP a p₁ p₂ := by
  constructor
  · intro h q hq
    obtain ⟨hqp, hqa⟩ := (mem_pf ha0).1 hq
    by_contra hc
    push_neg at hc
    refine h q hqp (by exact_mod_cast hc.1) ?_ hqa
    intro hd
    rcases (Nat.Prime.dvd_mul hqp).1 hd with hd | hd
    · exact prime_dvd_not_dvd_N hcop hqp hqa hd
    · exact hc.2 ((Nat.prime_dvd_prime_iff_eq hqp hp₁).1 hd)
  · intro h q hq hqy hqD hqa
    rcases h q ((mem_pf ha0).2 ⟨hq, hqa⟩) with h1 | h1
    · exact absurd hqy (not_lt.2 (by exact_mod_cast h1))
    · exact hqD (h1 ▸ dvd_mul_left _ _)

attribute [grind] sifted_lowP

/-- Sifted by `P(Np₁p₂)` at `(N/p₁p₂)^{1/2}` is Υ₉'s condition. -/
lemma sifted_nine {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    Sifted (N * p₁ * p₂) (Real.sqrt ((N : ℝ) / (p₁ * p₂))) a ↔
      ∀ q ∈ a.primeFactors, N ≤ p₁ * p₂ * q ^ 2 ∨ q = p₁ ∨ q = p₂ := by
  have hpos : (0 : ℝ) < (p₁ : ℝ) * p₂ := by
    have := hp₁.pos; have := hp₂.pos; positivity
  have key : ∀ q : ℕ, (q : ℝ) < Real.sqrt ((N : ℝ) / (p₁ * p₂)) ↔ p₁ * p₂ * q ^ 2 < N := by
    intro q
    rw [Real.lt_sqrt (by positivity), lt_div_iff₀ hpos, ← Nat.cast_lt (α := ℝ)]
    push_cast; constructor <;> intro h <;> linarith
  have hdvd : ∀ q : ℕ, q.Prime → q ∣ a → (q ∣ N * p₁ * p₂ ↔ q = p₁ ∨ q = p₂) := by
    intro q hq hqa
    have hqN : ¬ q ∣ N := prime_dvd_not_dvd_N hcop hq hqa
    rw [show N * p₁ * p₂ = N * (p₁ * p₂) by ring, Nat.Prime.dvd_mul hq,
      Nat.Prime.dvd_mul hq]
    simp [hqN, Nat.prime_dvd_prime_iff_eq hq hp₁, Nat.prime_dvd_prime_iff_eq hq hp₂]
  constructor
  · intro h q hq
    obtain ⟨hqp, hqa⟩ := (mem_pf ha0).1 hq
    by_contra hc
    push_neg at hc
    exact h q hqp ((key q).2 hc.1) (fun hd => by
      rcases (hdvd q hqp hqa).1 hd with h1 | h1
      · exact hc.2.1 h1
      · exact hc.2.2 h1) hqa
  · intro h q hq hqy hqD hqa
    rcases h q ((mem_pf ha0).2 ⟨hq, hqa⟩) with h1 | h1
    · exact absurd ((key q).1 hqy) (not_lt.2 h1)
    · exact hqD ((hdvd q hq hqa).2 h1)

/-- Generic pair bridge. -/
lemma pair_bridge (C : ℕ → ℕ → Prop) (T : ℕ → ℕ → Prop) (Q : ℝ → ℝ → Prop) (hN : 1 < N)
    (hdist : ∀ p₁ p₂, p₁.Prime → p₂.Prime → C p₁ p₂ → p₁ ≠ p₂)
    (hiff : ∀ p₁ ∈ a.primeFactors, ∀ p₂ ∈ a.primeFactors,
      (C p₁ p₂ ∧ T p₁ p₂ ↔ Q (ex N p₁) (ex N p₂))) :
    #{q ∈ P2 N C | q.1 * q.2 ∣ a ∧ T q.1 q.2} =
      #((a.primeFactors.image (ex N) ×ˢ a.primeFactors.image (ex N)).filter (fun p => Q p.1 p.2)) := by
  have h : #{q ∈ P2 N C | q.1 * q.2 ∣ a ∧ T q.1 q.2} =
      #{q ∈ a.primeFactors ×ˢ a.primeFactors | Q (ex N q.1) (ex N q.2)} := by

    congr 1
    ext ⟨p₁, p₂⟩
    simp only [P2, mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨⟨-, -⟩, h1, h2, -, -, hC⟩, hd, hT⟩
      have m1 := (mem_pf ha0).2 ⟨h1, dvd_trans (dvd_mul_right _ _) hd⟩
      have m2 := (mem_pf ha0).2 ⟨h2, dvd_trans (dvd_mul_left _ _) hd⟩
      exact ⟨⟨m1, m2⟩, (hiff p₁ m1 p₂ m2).1 ⟨hC, hT⟩⟩
    · rintro ⟨⟨m1, m2⟩, hC'⟩
      obtain ⟨hC, hT⟩ := (hiff p₁ m1 p₂ m2).2 hC'
      obtain ⟨h1, d1⟩ := (mem_pf ha0).1 m1
      obtain ⟨h2, d2⟩ := (mem_pf ha0).1 m2
      refine ⟨⟨⟨pf_lt ha0 haN m1, pf_lt ha0 haN m2⟩, h1, h2, pf_cop hcop m1,
        pf_cop hcop m2, hC⟩, ?_, hT⟩
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        ((Nat.coprime_primes h1 h2).2 (hdist p₁ p₂ h1 h2 hC)) d1 d2
  rw [h, ← prodMap_image_product (ex N) (ex N) a.primeFactors a.primeFactors, filter_image,
    card_image_of_injOn]
  · simp only [Prod.map]
  · intro p hp q hq heq
    simp only [Prod.map, Prod.mk.injEq] at heq
    obtain ⟨hp1, hp2⟩ := mem_product.1 (mem_filter.1 hp).1
    obtain ⟨hq1, hq2⟩ := mem_product.1 (mem_filter.1 hq).1
    exact Prod.ext (injP a hN hp1 hq1 heq.1) (injP a hN hp2 hq2 heq.2)

/-- Generic single-prime bridge. -/
lemma single_bridge (w z : ℝ) (hk : ∀ p ∈ a.primeFactors, w ≤ (p : ℝ)) (hs : Sifted N w a) :
    #{p ∈ PS N w z | p ∣ a ∧ Sifted N w a} = #(a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)) := by
  refine congrArg Finset.card ?_
  ext p
  simp only [mem_filter, mem_PS]
  constructor
  · rintro ⟨⟨hp, -, hz, -⟩, hd, -⟩
    exact ⟨(mem_pf ha0).2 ⟨hp, hd⟩, hz⟩
  · rintro ⟨m, hz⟩
    obtain ⟨hp, hd⟩ := (mem_pf ha0).1 m
    exact ⟨⟨hp, hk p m, hz, pf_cop hcop m⟩, hd, hs⟩

end bridges

/-- A product of four distinct primes dividing `a` divides `a`. -/
lemma mul4_dvd {p₁ p₂ p₃ p₄ a : ℕ} (h1 : p₁.Prime) (h2 : p₂.Prime) (h3 : p₃.Prime)
    (h4 : p₄.Prime) (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (d1 : p₁ ∣ a) (d2 : p₂ ∣ a) (d3 : p₃ ∣ a) (d4 : p₄ ∣ a) :
    p₁ * p₂ * p₃ * p₄ ∣ a := by
  have c : ∀ {x y : ℕ}, x.Prime → y.Prime → x < y → x.Coprime y :=
    fun hx hy hxy => (Nat.coprime_primes hx hy).2 hxy.ne
  have d12 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (c h1 h2 h12) d1 d2
  have d123 := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.mul_left (c h1 h3 (h12.trans h23)) (c h2 h3 h23)) d12 d3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.mul_left (Nat.Coprime.mul_left (c h1 h4 (h12.trans (h23.trans h34)))
      (c h2 h4 (h23.trans h34))) (c h3 h4 h34)) d123 d4


lemma swap1 {ι : Type*} (I : Finset ι) (e M : ι → ℕ) (y : ι → ℝ) :
    ∑ i ∈ I, S A (e i) (M i) (y i) = ∑ a ∈ A, #{i ∈ I | e i ∣ a ∧ Sifted (M i) (y i) a} := by
  simp only [S_eq_sum]
  rw [sum_comm]
  simp only [card_filter]

/-! ## The summed lemma -/

theorem lemma22_sum (hA : Admissible k1 k2) (hN : 1 < N)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 : ℤ) - Y3 A N k1 - Y4 A N k1
      - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2
      ≤ 4 * D12 A + 4 * Esq A N k1 := by
  unfold D12 Esq
  rw [card_filter, card_filter]
  push_cast
  unfold Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11
  simp only [swap1]
  simp only [S_eq_sum]
  push_cast
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_le_sum fun a ha => ?_
  obtain ⟨ha0, haN, hcop⟩ := hAN a ha

  have hk12 : (N : ℝ) ^ k1 ≤ (N : ℝ) ^ k2 :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hA.2.1.le
  by_cases hs : Sifted N ((N : ℝ) ^ k1) a
  swap
  · have hs2 : ¬ Sifted N ((N : ℝ) ^ k2) a := fun h => hs (sifted_mono hk12 h)
    simp only [hs, hs2, and_false, filter_false, card_empty, if_false, false_and, Nat.cast_zero]
    have : (0 : ℤ) ≤ (if Ω a ≤ 2 then 1 else 0) := by split_ifs <;> norm_num
    linarith
  have hk := (sifted_iff ha0 haN hcop _).1 hs
  set d := a.primeFactors.image (ex N) with hd
  have hinj : Set.InjOn (ex N) (a.primeFactors : Set ℕ) := injP a hN
  have hk' : ∀ e ∈ d, k1 ≤ e := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := mem_image.1 he
    exact (rpow_le_iff hN (pos_of_mem a hp) _).1 (hk p hp)
  have hs' : ∑ e ∈ d, e < 1 := by
    rw [hd, sum_image hinj]
    have hL := logN_pos hN
    have hprod : ((∏ p ∈ a.primeFactors, p : ℕ) : ℝ) < N := by
      exact_mod_cast lt_of_le_of_lt (Nat.le_of_dvd ha0 (Nat.prod_primeFactors_dvd a)) haN
    push_cast at hprod
    have hpos : ∀ p ∈ a.primeFactors, ((p : ℕ) : ℝ) ≠ 0 := fun p hp =>
      by exact_mod_cast (pos_of_mem a hp).ne'
    have hlog := Real.log_lt_log (prod_pos (fun p hp => by exact_mod_cast pos_of_mem a hp)) hprod
    rw [Real.log_prod hpos] at hlog
    simpa [ex, ← sum_div, div_lt_one hL] using hlog
  have hs2 : (if 1 ∣ a ∧ Sifted N ((N : ℝ) ^ k2) a then (1 : ℤ) else 0) = U2 k1 k2 d := by
    have hiff : Sifted N ((N : ℝ) ^ k2) a ↔ Aset k2 d = ∅ := by
      rw [sifted_iff ha0 haN hcop]
      constructor
      · intro h
        rw [eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨p, hp, rfl⟩ := mem_image.1 (mem_filter.1 hy).1
        exact not_lt.2 ((rpow_le_iff hN (pos_of_mem a hp) _).1 (h p hp)) (mem_filter.1 hy).2
      · intro h p hp
        by_contra hlt
        have hmem : ex N p ∈ Aset k2 d :=
          mem_filter.2 ⟨mem_image_of_mem _ hp, (lt_rpow_iff hN (pos_of_mem a hp) k2).1 (not_le.1 hlt)⟩
        rw [h] at hmem; simpa using hmem
    unfold U2
    by_cases h : Sifted N ((N : ℝ) ^ k2) a
    · simp [h, hiff.1 h]
    · rw [if_neg (by simp [h]), if_neg (fun hc => h (hiff.2 hc))]
  have e3 := (single_bridge ha0 haN hcop _ _ hk hs).trans
    (card_filter_image (injP a hN) (R := fun p : ℕ => (p : ℝ) < (N : ℝ) ^ e13) (Q := fun y => y < e13)
      (fun p hp => lt_rpow_iff hN (pos_of_mem a hp) e13))
  have e4 := (single_bridge ha0 haN hcop _ _ hk hs).trans
    (card_filter_image (injP a hN) (R := fun p : ℕ => (p : ℝ) < (N : ℝ) ^ em k1) (Q := fun y => y < em k1)
      (fun p hp => lt_rpow_iff hN (pos_of_mem a hp) (em k1)))
  let Aint := a.primeFactors.filter (fun p : ℕ => (p : ℝ) < (N : ℝ) ^ k2)
  let Bint := a.primeFactors.filter (fun p : ℕ => (N : ℝ) ^ k2 ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ em k1)
  have hAint : #(Aset k2 d) = #Aint := by
    rw [hd]
    change #((a.primeFactors.image (ex N)).filter (· < k2)) = #Aint
    exact (card_filter_image (injP a hN) (fun p hp => lt_rpow_iff hN (pos_of_mem a hp) k2)).symm
  have hBint : #(Bset k1 k2 d) = #Bint := by
    rw [hd]
    change #((a.primeFactors.image (ex N)).filter (fun y => k2 ≤ y ∧ y < em k1)) = #Bint
    exact (card_filter_image (injP a hN) (fun p hp => by
      rw [rpow_le_iff hN (pos_of_mem a hp) k2, lt_rpow_iff hN (pos_of_mem a hp) (em k1)])).symm
  have e5 : (↑(#{q ∈ P2 N (C5 N k1 k2) | q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}) : ℤ)
      ≤ U5 k1 k2 d := by
    rw [show U5 k1 k2 d = ((#Aint).choose 2 : ℤ) from by
      unfold U5; rw [hAint]]
    have hsub : (P2 N (C5 N k1 k2)).filter (fun q => q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a) ⊆
        (Aint ×ˢ Aint).filter (fun q => q.1 < q.2) := by
      intro q hq
      simp only [P2, mem_filter, mem_product, mem_range] at hq
      obtain ⟨⟨⟨h1N, h2N⟩, hp1, hp2, hc1, hc2, hC5⟩, hdvd, hS⟩ := hq
      have hp1d := (mem_pf ha0).2 ⟨hp1, dvd_trans (dvd_mul_right _ _) hdvd⟩
      have hp2d := (mem_pf ha0).2 ⟨hp2, dvd_trans (dvd_mul_left _ _) hdvd⟩
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_filter.2 ⟨hp1d,
        by linarith [hC5.2.2, show (q.1 : ℝ) < q.2 by exact_mod_cast hC5.2.1]⟩,
        mem_filter.2 ⟨hp2d, hC5.2.2⟩⟩, hC5.2.1⟩
    have h := card_le_card hsub
    rw [show #((Aint ×ˢ Aint).filter (fun q => q.1 < q.2)) = (#Aint).choose 2
      from Finset.card_product_filter_lt] at h
    exact_mod_cast h
  have e6 : (↑(#{q ∈ P2 N (C6 N k1 k2) | q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a}) : ℤ)
      ≤ U6 k1 k2 d := by
    rw [show U6 k1 k2 d = ((#Aint) * #Bint : ℕ) from by
      unfold U6; rw [hAint, hBint]]
    have hsub : (P2 N (C6 N k1 k2)).filter (fun q => q.1 * q.2 ∣ a ∧ Sifted N ((N : ℝ) ^ k1) a) ⊆
        Aint ×ˢ Bint := by
      intro q hq
      simp only [P2, mem_filter, mem_product, mem_range] at hq
      obtain ⟨⟨⟨h1N, h2N⟩, hp1, hp2, hc1, hc2, hC6⟩, hdvd, hS⟩ := hq
      have hp1d := (mem_pf ha0).2 ⟨hp1, dvd_trans (dvd_mul_right _ _) hdvd⟩
      have hp2d := (mem_pf ha0).2 ⟨hp2, dvd_trans (dvd_mul_left _ _) hdvd⟩
      exact mem_product.2 ⟨mem_filter.2 ⟨hp1d, hC6.2.1⟩,
        mem_filter.2 ⟨hp2d, hC6.2.2.1, hC6.2.2.2⟩⟩
    have h := card_le_card hsub
    rw [card_product] at h
    exact_mod_cast h
  have e7 : (↑(#{q ∈ P2 N (C7 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a}) : ℤ)
      = U7 k1 k2 d := by
    have h : ∀ p₁ ∈ a.primeFactors, ∀ p₂ ∈ a.primeFactors,
        (C7 N k1 p₁ p₂ ∧ Sifted (N * p₁) (p₂ : ℝ) a ↔
          (ex N p₁ < ex N p₂ ∧ em k1 ≤ ex N p₁ ∧ ex N p₁ + 2 * ex N p₂ < 1 ∧
            low2 d (ex N p₁) (ex N p₂))) := by
      intro p₁ m₁ p₂ m₂
      have hp1 := pos_of_mem a m₁
      have hp2 := pos_of_mem a m₂
      unfold C7
      grind
    rw [pair_bridge ha0 haN hcop hN (C := C7 N k1) (T := fun p₁ p₂ => Sifted (N * p₁) (p₂ : ℝ) a)
      (Q := fun x y => x < y ∧ em k1 ≤ x ∧ x + 2 * y < 1 ∧ low2 d x y)
      (fun _ _ _ _ h => h.2.1.ne) h]
    unfold U7
    rw [hd]
    congr 2
    ext x
    simp only [Finset.mem_filter]
  have e8 : (↑(#{q ∈ P2 N (C8 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) (q.2 : ℝ) a}) : ℤ)
      = U8 k1 k2 d := by
    have h : ∀ p₁ ∈ a.primeFactors, ∀ p₂ ∈ a.primeFactors,
        (C8 N k1 p₁ p₂ ∧ Sifted (N * p₁) (p₂ : ℝ) a ↔
          (ex N p₁ < e13 ∧ e13 ≤ ex N p₂ ∧ ex N p₁ + 2 * ex N p₂ < 1 ∧
            low2 d (ex N p₁) (ex N p₂))) := by
      intro p₁ m₁ p₂ m₂
      have hp1 := pos_of_mem a m₁
      have hp2 := pos_of_mem a m₂
      unfold C8
      grind
    rw [pair_bridge ha0 haN hcop hN (C := C8 N k1) (T := fun p₁ p₂ => Sifted (N * p₁) (p₂ : ℝ) a)
      (Q := fun x y => x < e13 ∧ e13 ≤ y ∧ x + 2 * y < 1 ∧ low2 d x y)
      (fun _ _ _ _ h => by
        have h1 := h.2.1; have h2 := h.2.2.1
        intro heq; subst heq; linarith) h]
    unfold U8
    rw [hd]
    congr 2
    ext x
    simp only [Finset.mem_filter]
  have e9 : (↑(#{q ∈ P2 N (C9 N k1 k2) | q.1 * q.2 ∣ a ∧
          Sifted (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2))) a}) : ℤ)
      = U9 k1 k2 d := by
    let Q : ℝ → ℝ → Prop := fun x y => k2 ≤ x ∧ x < em k1 ∧ em k1 ≤ y ∧ x + 2 * y < 1 ∧
      ∀ q ∈ d, 1 ≤ x + y + 2 * q ∨ q = x ∨ q = y
    have h : ∀ p₁ ∈ a.primeFactors, ∀ p₂ ∈ a.primeFactors,
        (C9 N k1 k2 p₁ p₂ ∧ Sifted (N * p₁ * p₂) (Real.sqrt ((N : ℝ) / (p₁ * p₂))) a ↔
          Q (ex N p₁) (ex N p₂)) := by
      intro p₁ m₁ p₂ m₂
      have hp1 := pos_of_mem a m₁
      have hp2 := pos_of_mem a m₂
      unfold C9 Q
      rw [sifted_nine ha0 haN hcop (Nat.prime_of_mem_primeFactors m₁)
        (Nat.prime_of_mem_primeFactors m₂),
        rpow_le_iff hN hp1 k2,
        lt_rpow_iff hN hp1 (em k1),
        rpow_le_iff hN hp2 (em k1),
        mul_sq_lt_iff hN hp1 hp2,
        hd, forall_mem_image]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        refine ⟨h1, h2, h3, h4, fun q hq => ?_⟩
        have := h5 q hq
        simpa [le_mul_mul_sq_iff hN hp1 hp2 (pos_of_mem a hq),
          x_eq_iff hN (pos_of_mem a hq) hp1,
          x_eq_iff hN (pos_of_mem a hq) hp2] using this
      · rintro ⟨h1, h2, h3, h4, h5⟩
        refine ⟨⟨h1, h2, h3, h4⟩, fun q hq => ?_⟩
        have := h5 (x := q) hq
        simpa [le_mul_mul_sq_iff hN hp1 hp2 (pos_of_mem a hq),
          x_eq_iff hN (pos_of_mem a hq) hp1,
          x_eq_iff hN (pos_of_mem a hq) hp2] using this
    rw [pair_bridge ha0 haN hcop hN (C := C9 N k1 k2)
      (T := fun p₁ p₂ => Sifted (N * p₁ * p₂) (Real.sqrt ((N : ℝ) / (p₁ * p₂))) a)
      (Q := Q) (fun _ _ _ _ h => by
        have h1 := h.2.1; have h2 := h.2.2.1
        intro heq; subst heq; linarith) h]
    unfold U9
    rw [hd]
    congr 2
    ext x
    simp only [Q, Finset.mem_filter]
    rw [hd]
  have hU10 : U10 k1 k2 d = ((#Aint - 2).choose 2 : ℤ) := by
    unfold U10; rw [hAint]
  have hU11 : U11 k1 k2 d = ((#Aint - 2 : ℕ) : ℤ) * #Bint := by
    unfold U11; rw [hAint, hBint]; push_cast; ring
  have e1011 : U10 k1 k2 d ≤ (↑(#{q ∈ P4 N (C10 N k1 k2) |
        q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧ Sifted (N * q.1) (q.2.1 : ℝ) a}) : ℤ) ∧
      U11 k1 k2 d ≤ (↑(#{q ∈ P4 N (C11 N k1 k2) |
        q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧ Sifted (N * q.1) (q.2.1 : ℝ) a}) : ℤ) := by
    by_cases ha2 : 2 ≤ #Aint
    · obtain ⟨p₁, p₂, hp₁, hp₂, h12, hq2⟩ := exists_two_least (S := Aint) ha2
      have hp1d : p₁ ∈ a.primeFactors := (mem_filter.1 hp₁).1
      have hp2d : p₂ ∈ a.primeFactors := (mem_filter.1 hp₂).1
      have hp1p := Nat.prime_of_mem_primeFactors hp1d
      have hp2p := Nat.prime_of_mem_primeFactors hp2d
      let A2 := (Aint.erase p₁).erase p₂
      have hA2sub : ∀ q ∈ A2, q ∈ Aint := by grind
      have hA2gt : ∀ q ∈ A2, p₂ < q := by
        intro q hq
        have := hA2sub q hq
        grind
      have hcard : #A2 = #Aint - 2 := by grind
      have hlow : lowP a p₁ p₂ := by
        intro q hq
        by_cases hqA : q ∈ Aint
        · grind
        · left
          have hqk : ¬ (q : ℝ) < (N : ℝ) ^ k2 := fun h => hqA (mem_filter.2 ⟨hq, h⟩)
          have hpk : (p₂ : ℝ) < (N : ℝ) ^ k2 := (mem_filter.1 hp₂).2
          exact le_of_lt (Nat.cast_lt.1 (lt_of_lt_of_le hpk (not_lt.1 hqk)))
      have hsift : Sifted (N * p₁) p₂ a := (sifted_lowP ha0 haN hcop hp1p).2 hlow
      constructor
      · rw [hU10]
        have h := card_le_card_of_injOn (fun t : ℕ × ℕ => (p₁, p₂, t.1, t.2))
          (s := (A2 ×ˢ A2).filter (fun p => p.1 < p.2)) (t := {q ∈ P4 N (C10 N k1 k2) |
            q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧ Sifted (N * q.1) (q.2.1 : ℝ) a}) ?_ ?_
        · rw [show #((A2 ×ˢ A2).filter (fun p => p.1 < p.2)) = (#A2).choose 2
              from Finset.card_product_filter_lt, hcard] at h
          exact_mod_cast h
        · intro t ht
          obtain ⟨htprod, ht12⟩ := mem_filter.1 ht
          obtain ⟨ht1, ht2⟩ := mem_product.1 htprod
          have ht1A := hA2sub _ ht1
          have ht2A := hA2sub _ ht2
          have ht1d := (mem_filter.1 ht1A).1
          have ht2d := (mem_filter.1 ht2A).1
          have ht1p := Nat.prime_of_mem_primeFactors ht1d
          have ht2p := Nat.prime_of_mem_primeFactors ht2d
          have ht2k : (t.2 : ℝ) < (N : ℝ) ^ k2 := (mem_filter.1 ht2A).2
          have hdvd : p₁ * p₂ * t.1 * t.2 ∣ a :=
            mul4_dvd (p₁ := p₁) (p₂ := p₂) (p₃ := t.1) (p₄ := t.2)
              hp1p hp2p ht1p ht2p h12 (hA2gt _ ht1) ht12
              (Nat.dvd_of_mem_primeFactors hp1d) (Nat.dvd_of_mem_primeFactors hp2d)
              (Nat.dvd_of_mem_primeFactors ht1d) (Nat.dvd_of_mem_primeFactors ht2d)
          have hc10 : C10 N k1 k2 p₁ p₂ t.1 t.2 :=
            ⟨hk p₁ hp1d, h12, hA2gt _ ht1, ht12, ht2k⟩
          unfold P4
          simp only [Finset.mem_coe, mem_filter, mem_product, mem_range]
          grind
        · intro t _ t' _ h; grind
      · rw [hU11]
        have h := card_le_card_of_injOn (fun t : ℕ × ℕ => (p₁, p₂, t.1, t.2))
          (s := A2 ×ˢ Bint) (t := {q ∈ P4 N (C11 N k1 k2) |
            q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧ Sifted (N * q.1) (q.2.1 : ℝ) a}) ?_ ?_
        · rw [card_product, hcard] at h
          exact_mod_cast h
        · intro t ht
          obtain ⟨ht1, ht2⟩ := mem_product.1 ht
          have ht1A := hA2sub _ ht1
          have ht1d := (mem_filter.1 ht1A).1
          obtain ⟨ht2d, ht2k, ht2m⟩ := mem_filter.1 ht2
          have ht1p := Nat.prime_of_mem_primeFactors ht1d
          have ht2p := Nat.prime_of_mem_primeFactors ht2d
          have ht1k : (t.1 : ℝ) < (N : ℝ) ^ k2 := (mem_filter.1 ht1A).2
          have h34 : t.1 < t.2 := by exact_mod_cast (lt_of_lt_of_le ht1k ht2k)
          have hdvd : p₁ * p₂ * t.1 * t.2 ∣ a :=
            mul4_dvd (p₁ := p₁) (p₂ := p₂) (p₃ := t.1) (p₄ := t.2)
              hp1p hp2p ht1p ht2p h12 (hA2gt _ ht1) h34
              (Nat.dvd_of_mem_primeFactors hp1d) (Nat.dvd_of_mem_primeFactors hp2d)
              (Nat.dvd_of_mem_primeFactors ht1d) (Nat.dvd_of_mem_primeFactors ht2d)
          have hc11 : C11 N k1 k2 p₁ p₂ t.1 t.2 :=
            ⟨hk p₁ hp1d, h12, hA2gt _ ht1, ht1k, ht2k, ht2m⟩
          unfold P4
          simp only [Finset.mem_coe, mem_filter, mem_product, mem_range]
          grind
        · intro t t' _ _ h; grind
    · have hzero : #Aint - 2 = 0 := by omega
      constructor
      · rw [hU10, hzero]; simp
      · rw [hU11, hzero]; simp
  rw [if_pos ⟨one_dvd a, hs⟩, hs2, e3, e4, e7, e8, e9]
  have key := pointwise k1 k2 hA d hk' hs'
  unfold rhs lhs at key
  rw [card_image_of_injOn hinj] at key
  have hw : (if #a.primeFactors ≤ 2 then (4 : ℤ) else 0) ≤ 4 * (if Ω a ≤ 2 then (1 : ℤ) else 0)
      + 4 * (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) := by
    by_cases hsq : Squarefree a
    · rw [show (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) = 0 from
        if_neg (fun h => h.2 hsq), show Ω a = #a.primeFactors from by
          rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors,
            List.toFinset_card_of_nodup ((Nat.squarefree_iff_nodup_primeFactorsList ha0.ne').1 hsq)]]
      split_ifs <;> norm_num
    · rw [show (if Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a then (1 : ℤ) else 0) = 1 from
        if_pos ⟨hs, hsq⟩]
      split_ifs <;> norm_num
  linarith

end

end GoldbachLean.Wu2008.WuSum
