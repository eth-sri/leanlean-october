module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Proof of Wu 2008 Lemma 2.2 (with Υ₁₁ repaired) and Li 2024 Lemma 3.1

Direct combinatorial proof over the prime factors of each sifted member `a ∈ A`, avoiding an
intermediate logarithmic real-exponent transfer layer, together with the explicit telescoping
bound for the non-squarefree error term `Esq`.
-/

open Finset
open scoped ArithmeticFunction.Omega Classical
set_option quotPrecheck false

@[expose] public noncomputable section

/-- `a` survives sifting by `P(D) = {q prime : q ∤ D}` up to `y`: no prime `q < y` with `q ∤ D`
divides `a`. -/
def GoldbachLean.Wu2008.WuSieve.Sifted (D y a) :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < y → ¬ q ∣ D → ¬ q ∣ a

/-- Wu's sieve function `S(A_e; P(D), y)`: the number of `a ∈ A` with `e ∣ a` that survive
sifting by `P(D)` up to `y`. -/
def GoldbachLean.Wu2008.WuSieve.S (A : Finset _) (e D y) :=
  #{a ∈ A | e ∣ a ∧ GoldbachLean.Wu2008.WuSieve.Sifted D y a}

/-- The primes `p` with `w ≤ p < z` and `(p, N) = 1`. -/
def GoldbachLean.Wu2008.WuSieve.PS (N) (w z : ℝ) :=
  (range ⌈z⌉₊).filter fun p : ℕ => p.Prime ∧ w ≤ p ∧ ↑p < z ∧ p.Coprime N

/-- Wu's κ₁ = 1/13.27. -/
def GoldbachLean.Wu2008.WuReal.wk1 : ℝ := 100 / 1327
/-- Wu's κ₂ = 1/8.24. -/
def GoldbachLean.Wu2008.WuReal.wk2 : ℝ := 100 / 824
/-- The exponent `1/2 − 3κ₁`. -/
def GoldbachLean.Wu2008.WuReal.em (k1 : ℝ) := 1 / 2 - 3 * k1
/-- The exponent `1/3`. -/
def GoldbachLean.Wu2008.WuReal.e13 : ℝ := 1 / 3

/-- Wu's hypotheses for Lemma 2.2: κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2, and 3κ₁ − κ₂ < 1/6, the last
weakened here to `≤`. -/
def GoldbachLean.Wu2008.WuReal.Admissible (k1 k2 : ℝ) :=
  1 / 18 ≤ k1 ∧ k1 < k2 ∧ 3 * k1 + k2 < 1 / 2 ∧ 3 * k1 - k2 ≤ 1 / 6

/-- Li's κ₁ = 1/11.49. -/
def GoldbachLean.Li2024.Lemma31.lk1 : ℝ := 100 / 1149
/-- Li's κ₂ = 1/6.18. -/
def GoldbachLean.Li2024.Lemma31.lk2 : ℝ := 100 / 618

attribute [local simp] GoldbachLean.Wu2008.WuReal.wk1 GoldbachLean.Wu2008.WuReal.wk2
  GoldbachLean.Li2024.Lemma31.lk1 GoldbachLean.Li2024.Lemma31.lk2
  GoldbachLean.Wu2008.WuReal.Admissible GoldbachLean.Wu2008.WuReal.e13

/-- Wu's own values are admissible. -/
theorem GoldbachLean.Wu2008.WuReal.wu_admissible :
    GoldbachLean.Wu2008.WuReal.Admissible GoldbachLean.Wu2008.WuReal.wk1 GoldbachLean.Wu2008.WuReal.wk2 := by norm_num

namespace GoldbachLean.Wu2008.WuSum

local notation "ltP" s => {q ∈ s ×ˢ s | q.1 < q.2}

private lemma sifted_le {N a q y} :
    WuSieve.Sifted N y a → a.Coprime N → q ∣ a → q.Prime → y ≤ q := fun hs hc hd hq =>
  not_lt.1 fun h => hs q hq h (hq.coprime_iff_not_dvd.1 (hc.coprime_dvd_left hd)) hd

section
variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ) (p₁ p₂ p₃ p₄ : ℕ)

local notation "rN" => range N

/-- Pairs `(p₁, p₂)` of primes below `N`, both coprime to `N`, satisfying `C p₁ p₂`. -/
def P2 (C : _ → _ → _) :=
  {q ∈ rN ×ˢ rN | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧ C q.1 q.2}

/-- Quadruples `(p₁, p₂, p₃, p₄)` of primes below `N`, all coprime to `N`, satisfying `C`. -/
def P4 (C : _ → _ → _ → _ → _) :=
  {q ∈ rN ×ˢ rN ×ˢ rN ×ˢ rN | q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
    q.2.2.2.Prime ∧ q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
    C q.1 q.2.1 q.2.2.1 q.2.2.2}

local notation "Ny" κ:max => (N : ℝ) ^ κ
local notation "Nk" => Ny k1
local notation "N2" => Ny k2
local notation "Nm" => Ny (WuReal.em k1)
local notation "N3" => Ny WuReal.e13
local notation "c7" => p₁ * p₂ ^ 2 < N
local notation "c10" R => Nk ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ R
local notation "S3" A:max z => ∑ p ∈ WuSieve.PS N Nk z, WuSieve.S A p N Nk
local notation "S5" A:max C => ∑ q ∈ P2 N C, WuSieve.S A (q.1 * q.2) N Nk
local notation "S7" A:max C => ∑ q ∈ P2 N C, WuSieve.S A (q.1 * q.2) (N * q.1) q.2
local notation "S10" A:max C => ∑ q ∈ P4 N C,
  WuSieve.S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1

/-- Υ₁ = S(A; P(N), N^κ₁). -/
def Y1 := WuSieve.S A 1 N Nk
/-- Υ₂ = S(A; P(N), N^κ₂). -/
def Y2 := WuSieve.S A 1 N N2
/-- Υ₃ = Σ_{N^κ₁ ≤ p < N^{1/3}, (p,N)=1} S(A_p; P(N), N^κ₁). -/
def Y3 := S3 A N3
/-- Υ₄ = Σ_{N^κ₁ ≤ p < N^{1/2−3κ₁}, (p,N)=1} S(A_p; P(N), N^κ₁). -/
def Y4 := S3 A Nm
/-- The range of Υ₅: N^κ₁ ≤ p₁ < p₂ < N^κ₂. -/
def C5 := Nk ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < N2
/-- Υ₅ = Σ_{N^κ₁ ≤ p₁ < p₂ < N^κ₂} S(A_{p₁p₂}; P(N), N^κ₁). -/
def Y5 := S5 A (C5 N k1 k2)
/-- The range of Υ₆: N^κ₁ ≤ p₁ < N^κ₂ ≤ p₂ < N^{1/2−3κ₁}. -/
def C6 := Nk ≤ p₁ ∧ p₁ < N2 ∧ N2 ≤ p₂ ∧ p₂ < Nm
/-- Υ₆ = Σ_{N^κ₁ ≤ p₁ < N^κ₂ ≤ p₂ < N^{1/2−3κ₁}} S(A_{p₁p₂}; P(N), N^κ₁). -/
def Y6 := S5 A (C6 N k1 k2)
/-- The range of Υ₇: N^{1/2−3κ₁} ≤ p₁ < p₂ < (N/p₁)^{1/2}, written p₁ p₂² < N. -/
def C7 := Nm ≤ p₁ ∧ p₁ < p₂ ∧ c7
/-- Υ₇ = Σ S(A_{p₁p₂}; P(Np₁), p₂) over the range `C7`. -/
def Y7 := S7 A (C7 N k1)
/-- The range of Υ₈: N^κ₁ ≤ p₁ < N^{1/3} ≤ p₂ < (N/p₁)^{1/2}. -/
def C8 := Nk ≤ p₁ ∧ p₁ < N3 ∧ N3 ≤ p₂ ∧ c7
/-- Υ₈ = Σ S(A_{p₁p₂}; P(Np₁), p₂) over the range `C8`. -/
def Y8 := S7 A (C8 N k1)
/-- The range of Υ₉: N^κ₂ ≤ p₁ < N^{1/2−3κ₁} ≤ p₂ < (N/p₁)^{1/2}. -/
def C9 := N2 ≤ p₁ ∧ p₁ < Nm ∧ Nm ≤ p₂ ∧ c7
/-- Υ₉ = Σ S(A_{p₁p₂}; P(Np₁p₂), (N/p₁p₂)^{1/2}) over the range `C9`, the intended sieve set. -/
def Y9 := ∑ q ∈ P2 N (C9 N k1 k2), WuSieve.S A (q.1 * q.2) (N * q.1 * q.2) √(↑N / (q.1 * q.2))
/-- The range of Υ₁₀: N^κ₁ ≤ p₁ < p₂ < p₃ < p₄ < N^κ₂. -/
def C10 := c10 p₃ < p₄ ∧ p₄ < N2
/-- Υ₁₀ = Σ S(A_{p₁p₂p₃p₄}; P(Np₁), p₂) over the range `C10`, the intended sieve set. -/
def Y10 := S10 A (C10 N k1 k2)
/-- The repaired range of Υ₁₁: N^κ₁ ≤ p₁ < p₂ < p₃ < N^κ₂ ≤ p₄ < N^{1/2−3κ₁}. Wu prints the
shorter p₄ < N^{1/2−2κ₁}/p₃. -/
def C11 := c10 p₃ < N2 ∧ N2 ≤ p₄ ∧ p₄ < Nm
/-- Υ₁₁ = Σ S(A_{p₁p₂p₃p₄}; P(Np₁), p₂) over the repaired range `C11`. -/
def Y11 := S10 A (C11 N k1 k2)

/-- D₁,₂ for `A`: the number of `a ∈ A` with at most two prime factors counted with multiplicity. -/
def D12 := #{a ∈ A | Ω a ≤ 2}
/-- The error term: members of `A` sifted at `N^κ₁` that are not squarefree. -/
def Esq := #{a ∈ A | WuSieve.Sifted N Nk a ∧ ¬ Squarefree a}

local notation:55 "WU" T:max A:max a:max b:max =>
  (3 * Y1 A N a + Y2 A N b + Y5 A N a b + Y6 A N a b : T) - Y3 A N a - Y4 A N a
    - 2 * Y7 A N a - Y8 A N a - Y9 A N a b - Y10 A N a b - Y11 A N a b

/-- **Wu 2008, Lemma 2.2, (2.2), with Υ₁₁ repaired**, for any finite set `A` of integers
`0 < a < N` coprime to `N`, any `N > 1` and any admissible `κ₁, κ₂`. -/
theorem lemma22_sum : WuReal.Admissible k1 k2 → 1 < N →
    (∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) →
    WU ℤ A k1 k2 ≤ 4 * D12 A + 4 * Esq A N k1 := fun hA hN hAN => by
  simp only [Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, D12, Esq, WuSieve.S, card_filter,
    sum_comm (t := A), one_dvd, true_and]
  push_cast
  simp only [mul_sum A, ← sum_add_distrib, ← sum_sub_distrib]
  obtain ⟨_, hk12, _, _⟩ := hA
  have hN1 : (1 : ℝ) < N := mod_cast hN
  have hN0 := zero_lt_one.trans hN1
  have hK12 := Real.rpow_lt_rpow_of_exponent_lt hN1 hk12
  have hK2M : N2 < Nm := Real.rpow_lt_rpow_of_exponent_lt hN1 (by unfold WuReal.em; linarith)
  have hKM3 : Nm ≤ N3 := by unfold WuReal.em WuReal.e13; gcongr <;> linarith
  have : (N : ℝ) ≤ N2 * Nm * N3 ^ 2 := by
    simp only [sq, ← Real.rpow_add hN0, WuReal.em, WuReal.e13]; nth_rw 1 [← Real.rpow_one N]
    gcongr <;> linarith
  have hK3 : N3 * N3 * N3 = N := by norm_num [← Real.rpow_add hN0]
  set K2 := N2; set KM := Nm; set K3 := N3
  refine sum_le_sum fun a ha => ?_
  obtain ⟨ha0, haN, hcop⟩ := hAN a ha
  by_cases hs : WuSieve.Sifted N Nk a
  swap
  · simp [hs, show ¬ WuSieve.Sifted N K2 a from fun h => hs fun q hq => (h q hq <| ·.trans hK12)]
    split_ifs <;> omega
  simp only [sum_boole, hs, and_true, true_and, ite_true]
  set y2 : ℤ := if WuSieve.Sifted N K2 a then 1 else 0
  have : y2 ≤ 1 := by dsimp [y2]; split_ifs <;> omega
  set P := a.primeFactors
  have mP {p} := @Nat.mem_primeFactors_of_ne_zero a p ha0.ne'
  have hpf {p} (hp : p ∈ P) : Nk ≤ p ∧ p < N ∧ p.Prime ∧ p.Coprime N ∧ p ∣ a := by
    obtain ⟨hpr, hpa⟩ := mP.1 hp
    exact ⟨sifted_le hs hcop hpa hpr, (Nat.le_of_dvd ha0 hpa).trans_lt haN, hpr,
      hcop.coprime_dvd_left hpa, hpa⟩
  let Pf (z : ℝ) := P.filter fun p : ℕ => (p : ℝ) < z
  have mPf : Monotone Pf := fun _ _ h => P.monotone_filter_right fun _ _ => (·.trans_le h)
  have hps (z) : #(Pf z) ≤ #{p ∈ WuSieve.PS N Nk z | p ∣ a} := card_le_card fun p => by
    simp +contextual [Pf, WuSieve.PS, Nat.Coprime, Nat.lt_ceil, *]
  have := hps K3; have := hps KM
  have := card_le_card (mPf hKM3)
  set As := Pf K2
  set Bs := Pf KM \ As
  have hAB : #Bs + #As = #(Pf KM) := card_sdiff_add_card_eq_card (mPf hK2M.le)
  have hp2s (C T) : (∀ x ∈ P, ∀ y ∈ P, C x y → (x, y) ∈ T) →
      #{q ∈ P2 N C | q.1 * q.2 ∣ a} ≤ #T := fun h => card_le_card fun q hq => by
    simp [P2] at hq
    exact h q.1 (mP.2 ⟨hq.1.2.1, dvd_of_mul_right_dvd hq.2⟩)
      q.2 (mP.2 ⟨hq.1.2.2.1, dvd_of_mul_left_dvd hq.2⟩) hq.1.2.2.2.2.2
  have hy6 := card_product As Bs ▸ hp2s (C6 N k1 k2) (As ×ˢ Bs) (by
    simp +contextual [C6, As, Bs, Pf, K2, KM])
  have hy5 := As.card_product_filter_lt ▸ hp2s (C5 N k1 k2) (ltP As) fun _ _ _ _ ⟨_, c12, c2⟩ => by
    simp [As, Pf, K2, *, (Nat.cast_lt.2 c12).trans c2]
  rcases le_or_gt #P 2 with hP2 | hP3
  · have : (#As).choose 2 + #As * #Bs ≤ #(Pf KM) := by
      have : #(Pf KM) ≤ #P := P.card_filter_le _
      rcases h : #As with _ | _ | _ | _ <;> norm_num [h] <;> omega
    split_ifs with h1 <;> try omega
    cases h1 (by rwa [ArithmeticFunction.cardFactors_apply,
      ← List.toFinset_card_of_nodup ((Nat.squarefree_iff_nodup_primeFactorsList ha0.ne').1 ‹_›),
      a.toFinset_factors])
  · trans 0; rotate_left; · split_ifs <;> omega
    replace hP3 : 2 < P.sort.length := by simp [hP3]
    rcases e : P.sort with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, l⟩⟩⟩ <;> simp [e] at hP3
    have ⟨hp1, hp2P, hp3, h12, h23, hqP⟩ : p1 ∈ P ∧ p2 ∈ P ∧ p3 ∈ P ∧ p1 < p2 ∧ p2 < p3 ∧
        ∀ q ∈ P, ¬ p3 ≤ q → q = p1 ∨ q = p2 := by
      simp [← mem_sort LE.le, e]; grind [P.sortedLT_sort.pairwise, List.pairwise_cons]
    have h12r : (p1 : ℝ) < p2 := mod_cast h12
    have h23r : (p2 : ℝ) < p3 := mod_cast h23
    have hy2 : p1 ∈ As → y2 = 0 := fun h => ite_eq_right fun h2 =>
      (mem_filter.1 h).2.not_ge <| sifted_le h2 hcop (mP.1 hp1).2 (mP.1 hp1).1
    have hd12 (l) (h2 : List.toFinset l ⊆ P := by simp [insert_subset_iff, *])
        (h1 : l.Nodup := by simp; omega) : l.prod ∣ a := by
      simpa [l.prod_toFinset (·) h1] using
        (prod_dvd_prod_of_subset _ _ _ h2).trans a.prod_primeFactors_dvd
    have hs12 : WuSieve.Sifted (N * p1) p2 a := fun q hq hqy hqD hqa => hqD <|
      (by have := hqP q (mP.2 ⟨hq, hqa⟩); have := Nat.cast_lt.1 hqy; omega : q = p1) ▸
        dvd_mul_left _ _
    rcases lt_or_ge (p2 : ℝ) K2 with hp2_2 | hp2_2
    · set A2 := As \ {p1, p2}
      have hp1A : p1 ∈ As := mem_filter.2 ⟨hp1, h12r.trans hp2_2⟩
      have hA2_card : #A2 + 2 = #As := card_pair h12.ne ▸ card_sdiff_add_card_eq_card (by
        simp [insert_subset_iff, As, Pf, hp1A, hp2P, hp2_2])
      have hA2 {q} : q ∈ A2 → q ∈ P ∧ (q : ℝ) < K2 ∧ p2 < q := fun hq => by
        simp [A2, As, Pf] at hq
        exact ⟨hq.1.1, hq.1.2, by have := hqP q hq.1.1; omega⟩
      have hp4 (C T) (hT : ∀ r ∈ T, r.1 ∈ A2 ∧ r.2 ∈ P ∧ r.1 < r.2 ∧ C p1 p2 r.1 r.2) :
          #T ≤ #{q ∈ P4 N C | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧
            WuSieve.Sifted (N * q.1) q.2.1 a} :=
        card_le_card_of_injOn (fun r => (p1, p2, r)) (fun r hr => by
          have h := hT r hr; have := hA2 h.1
          simpa [P4, Nat.Coprime, mul_assoc, *] using hd12 [p1, p2, r.1, r.2])
          fun _ _ _ _ => by simp
      have := A2.card_product_filter_lt.symm.trans_le <|
        hp4 (C10 N k1 k2) (ltP A2) fun _ => by simp +contextual [C10, K2, *]
      have := card_product A2 Bs ▸ hp4 (C11 N k1 k2) (A2 ×ˢ Bs) fun r hr => by
        simp [Bs, As, Pf] at hr
        simp [C11, K2, KM, Nat.cast_lt.1 ((hA2 hr.1).2.1.trans_le (hr.2.2 hr.2.1.1)), *]
      simp [← hA2_card, Nat.choose_succ_succ, add_mul] at hy5 hy6
      have := hy2 hp1A; omega
    · have d123 : p1 * p2 * p3 ∣ a := by simpa [mul_assoc] using hd12 [p1, p2, p3]
      have hm1 := (Nat.le_of_dvd ha0 d123).trans_lt haN
      have := (mP.1 hp1).1.pos; have := (mP.1 hp2P).1.pos
      have hm2 : p1 * p2 ^ 2 < N := by nlinarith
      have hp1_lt3 : (p1 : ℝ) < K3 := not_le.1 fun h => by
        have := h.trans h12r.le; have := this.trans h23r.le
        exact (hK3 ▸ show (p1 : ℝ) * p2 * p3 < N from mod_cast hm1).not_ge (by gcongr)
      have hp1_3 : p1 ∈ Pf K3 := mem_filter.2 ⟨hp1, hp1_lt3⟩
      have hp2 (C) (S' : _ → _) : C p1 p2 → S' (p1, p2) →
          1 ≤ #{q ∈ P2 N C | q.1 * q.2 ∣ a ∧ S' q} := fun hC hS =>
        one_le_card.2 ⟨(p1, p2), by simp [P2, Nat.Coprime, dvd_of_mul_right_dvd d123, *]⟩
      have hp78 (C) (hC) := hp2 C (fun q => WuSieve.Sifted (N * q.1) q.2 a) hC hs12
      have := (le_or_gt K3 p2).elim
        (fun hp2_3 => add_le_add (one_le_card.2 ⟨p1, hp1_3⟩)
          (hp78 (C8 N k1) ⟨(hpf hp1).1, hp1_lt3, hp2_3, hm2⟩))
        fun hp2_3 => (one_lt_card.2 ⟨p1, hp1_3, p2, mem_filter.2 ⟨hp2P, hp2_3⟩, h12.ne⟩).trans_le
          le_self_add
      rcases subset_singleton_iff.1 (show As ⊆ {p1} from fun q hq => by
          simp [As, Pf] at hq ⊢; have := hqP q hq.1; have := Nat.cast_lt.1 (hq.2.trans_le hp2_2)
          omega) with h0 | h1
      · simp only [h0, card_empty, Nat.choose] at hy5 hy6 hAB
        have hp1_2 : K2 ≤ p1 := by simp [As, Pf] at h0; exact h0 hp1
        rcases le_or_gt KM p1 with hp1_M | hp1_M
        · have := hp78 (C7 N k1) ⟨hp1_M, h12, hm2⟩; omega
        · have hp1M : p1 ∈ Pf KM := mem_filter.2 ⟨hp1, hp1_M⟩
          rcases lt_or_ge (p2 : ℝ) KM with hp2_M | hp2_M
          · have := one_lt_card.2 ⟨p1, hp1M, p2, mem_filter.2 ⟨hp2P, hp2_M⟩, h12.ne⟩; omega
          · have := one_le_card.2 ⟨p1, hp1M⟩
            rcases lt_or_ge (p3 : ℝ) K3 with hp3_3 | hp3_3
            · have := two_lt_card.2 ⟨p1, hp1_3, p2, mem_filter.2 ⟨hp2P, h23r.trans hp3_3⟩,
                p3, mem_filter.2 ⟨hp3, hp3_3⟩, by omega⟩
              omega
            · have := hp2 (C9 N k1 k2) (fun q => WuSieve.Sifted (N * q.1 * q.2)
                √(↑N / (q.1 * q.2)) a) ⟨hp1_2, hp1_M, hp2_M, hm2⟩ fun q hq hqy hqD hqa => by
                  by_cases hle : p3 ≤ q
                  · rw [Real.lt_sqrt q.cast_nonneg, lt_div_iff₀ (by positivity)] at hqy
                    have := hp3_3.trans (Nat.cast_le.2 hle)
                    linarith [show K2 * KM * K3 ^ 2 ≤ (p1 : ℝ) * p2 * (q : ℝ) ^ 2 by gcongr]
                  · rcases hqP q (mP.2 ⟨hq, hqa⟩) hle with rfl | rfl <;>
                      exact hqD (by simp [dvd_mul_of_dvd_left])
              omega
      · have := hy2 (by simp [h1])
        simp only [h1, card_singleton, Nat.choose] at hy5 hy6 hAB; omega

/-- Wu's sequence `A = {N − p : p < N prime, p ∤ N}`. -/
def wuA := {p ∈ rN | p.Prime ∧ ¬ p ∣ N}.image (N - ·)

local notation "WUE" a:max b =>
  WU ℝ (wuA N) a b ≤ 4 * D12 (wuA N) + 4 * (N / (Ny a - 1))

/-- **(2.2) for Wu's own sequence `A = {N − p}`, with Υ₁₁ repaired and the error explicit:**
Wu's `O(N^{1−κ₁})` is at most `4N/(N^κ₁ − 1)`. -/
theorem lemma22_wuA : WuReal.Admissible k1 k2 → 1 < N → 1 < Nk → WUE k1 k2 :=
    fun hA hN hNk => by
  have hok : ∀ a ∈ wuA N, 0 < a ∧ a < N ∧ a.Coprime N := by
    simp +contextual [wuA, forall_mem_image, -mem_image, le_of_lt, Nat.Prime.coprime_iff_not_dvd]
    exact fun _ _ h _ => ⟨by omega, h.pos⟩
  have := Int.cast_le (R := ℝ).2 (lemma22_sum _ _ _ _ hA hN hok)
  push_cast at this
  have hN0 := N.cast_nonneg (α := ℝ)
  have := Nat.le_ceil Nk
  have := Nat.ceil_pos.2 (zero_lt_one.trans hNk)
  set M := ⌈Nk⌉₊
  let g (k : ℕ) : ℝ := N / (M - 1 + k)
  have h1 : (Esq (wuA N) N k1 : ℝ) ≤ g 0 - g N := by
    rw [← sum_range_sub' g N]
    refine (Nat.cast_le.2 ((card_le_card (t := Finset.biUnion rN fun k =>
      {x ∈ Ioc 0 N | (M + k) ^ 2 ∣ x}) fun a ha => ?_).trans card_biUnion_le)).trans ?_
    · simp at ha; have h := hok a ha.1
      obtain ⟨q, hqp, hqq⟩ := by simpa [Nat.squarefree_iff_prime_squarefree] using ha.2.2
      have hqa := dvd_of_mul_left_dvd hqq; have := Nat.le_of_dvd h.1 hqa
      simp; exact ⟨q - M, by omega, by omega,
        by rwa [sq, Nat.add_sub_of_le (Nat.ceil_le.2 <| sifted_le ha.2.1 h.2.2 hqa hqp)]⟩
    · simp only [Nat.Ioc_filter_dvd_card_eq_div, Nat.cast_sum]
      refine sum_le_sum fun k _ => Nat.cast_div_le.trans ?_
      have : (0 : ℝ) < M - 1 + k := by linarith [k.cast_nonneg (α := ℝ)]
      dsimp [g]; push_cast; rw [← add_assoc]; field_simp; nlinarith
  have : 0 ≤ g N := div_nonneg hN0 (by linarith)
  simp [g] at h1
  linarith [show (N : ℝ) / (M - 1) ≤ N / (Nk - 1) by gcongr]

/-! ## Li 2024, Lemma 3.1: Wu's Lemma 2.2 at κ₁ = 1/11.49, κ₂ = 1/6.18, with the range of S₁₅
repaired. R. Li, arXiv 2405.05727 v4, Mathematical Reports 2026. -/

/-- Li's parameters satisfy Wu's hypotheses. -/
theorem _root_.GoldbachLean.Li2024.Lemma31.li_admissible :
    WuReal.Admissible GoldbachLean.Li2024.Lemma31.lk1 GoldbachLean.Li2024.Lemma31.lk2 := by norm_num

/-- **Li 2024, Lemma 3.1, with S₁₅'s range repaired**, for A = {N − p}, explicit error. -/
theorem _root_.GoldbachLean.Li2024.Lemma31.lemma31_repaired :
    1 < N → 1 < Ny GoldbachLean.Li2024.Lemma31.lk1 →
      WUE GoldbachLean.Li2024.Lemma31.lk1 GoldbachLean.Li2024.Lemma31.lk2 :=
  lemma22_wuA _ _ _ GoldbachLean.Li2024.Lemma31.li_admissible

end
end GoldbachLean.Wu2008.WuSum
end
