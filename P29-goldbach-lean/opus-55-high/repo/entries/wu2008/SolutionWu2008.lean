import Mathlib

open Finset

noncomputable section
open scoped Classical

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)

set_option hygiene false in
notation "ℸ" k:max => (N : ℝ) ^ k

def GoldbachLean.Wu2008.WuSieve.Sifted D (y : ℝ) a := ∀ q : ℕ, q.Prime → q < y → ¬ q ∣ D → ¬ q ∣ a

def GoldbachLean.Wu2008.WuSieve.S e D y := #{a ∈ A | e ∣ a ∧ Sifted D y a}

def GoldbachLean.Wu2008.WuSieve.PS (w z : ℝ) : Finset ℕ := {p ∈ range ⌈z⌉₊ | p.Prime ∧ w ≤ p ∧ p < z ∧ p.Coprime N}

def GoldbachLean.Wu2008.WuReal.wk1 : ℝ := 100 / 1327
def GoldbachLean.Wu2008.WuReal.wk2 : ℝ := 100 / 824
def GoldbachLean.Wu2008.WuReal.em := 1 / 2 - 3 * k1
def GoldbachLean.Wu2008.WuReal.e13 : ℝ := 1 / 3

def GoldbachLean.Wu2008.WuReal.Admissible := 1 / 18 ≤ k1 ∧ k1 < k2 ∧ 3 * k1 + k2 < 1 / 2 ∧ 3 * k1 - k2 ≤ 1 / 6

theorem GoldbachLean.Wu2008.WuReal.wu_admissible : Admissible wk1 wk2 := by
  unfold Admissible wk1 wk2
  norm_num

def GoldbachLean.Wu2008.WuSum.P2 (C : ℕ → ℕ → Prop) :=
  {q ∈ Finset.range N ×ˢ Finset.range N | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧ C q.1 q.2}

def GoldbachLean.Wu2008.WuSum.P4 (C : ℕ → ℕ → ℕ → ℕ → Prop) :=
  {q ∈ Finset.range N ×ˢ Finset.range N ×ˢ Finset.range N ×ˢ Finset.range N | q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
    q.2.2.2.Prime ∧ q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
    C q.1 q.2.1 q.2.2.1 q.2.2.2}


def GoldbachLean.Wu2008.WuSum.Y1 := GoldbachLean.Wu2008.WuSieve.S A 1 N (ℸ k1)
def GoldbachLean.Wu2008.WuSum.Y2 := GoldbachLean.Wu2008.WuSieve.S A 1 N (ℸ k2)
def GoldbachLean.Wu2008.WuSum.Y3 := ∑ p ∈ GoldbachLean.Wu2008.WuSieve.PS N (ℸ k1) (ℸ GoldbachLean.Wu2008.WuReal.e13), GoldbachLean.Wu2008.WuSieve.S A p N (ℸ k1)
def GoldbachLean.Wu2008.WuSum.Y4 := ∑ p ∈ GoldbachLean.Wu2008.WuSieve.PS N (ℸ k1) (ℸ (GoldbachLean.Wu2008.WuReal.em k1)), GoldbachLean.Wu2008.WuSieve.S A p N (ℸ k1)
def GoldbachLean.Wu2008.WuSum.C5 (p₁ p₂ : ℕ) := ℸ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < ℸ k2
def GoldbachLean.Wu2008.WuSum.Y5 := ∑ q ∈ P2 N (C5 N k1 k2), GoldbachLean.Wu2008.WuSieve.S A (q.1 * q.2) N (ℸ k1)
def GoldbachLean.Wu2008.WuSum.C6 (p₁ p₂ : ℕ) := ℸ k1 ≤ p₁ ∧ p₁ < ℸ k2 ∧ ℸ k2 ≤ p₂ ∧ p₂ < ℸ (GoldbachLean.Wu2008.WuReal.em k1)
def GoldbachLean.Wu2008.WuSum.Y6 := ∑ q ∈ P2 N (C6 N k1 k2), GoldbachLean.Wu2008.WuSieve.S A (q.1 * q.2) N (ℸ k1)
def GoldbachLean.Wu2008.WuSum.C7 (p₁ p₂ : ℕ) := ℸ (GoldbachLean.Wu2008.WuReal.em k1) ≤ p₁ ∧ p₁ < p₂ ∧ p₁ * p₂ ^ 2 < N
def GoldbachLean.Wu2008.WuSum.Y7 := ∑ q ∈ P2 N (C7 N k1), GoldbachLean.Wu2008.WuSieve.S A (q.1 * q.2) (N * q.1) q.2
def GoldbachLean.Wu2008.WuSum.C8 (p₁ p₂ : ℕ) := ℸ k1 ≤ p₁ ∧ p₁ < ℸ GoldbachLean.Wu2008.WuReal.e13 ∧ ℸ GoldbachLean.Wu2008.WuReal.e13 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
def GoldbachLean.Wu2008.WuSum.Y8 := ∑ q ∈ P2 N (C8 N k1), GoldbachLean.Wu2008.WuSieve.S A (q.1 * q.2) (N * q.1) q.2
def GoldbachLean.Wu2008.WuSum.C9 (p₁ p₂ : ℕ) := ℸ k2 ≤ p₁ ∧ p₁ < ℸ (GoldbachLean.Wu2008.WuReal.em k1) ∧ ℸ (GoldbachLean.Wu2008.WuReal.em k1) ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
def GoldbachLean.Wu2008.WuSum.Y9 := ∑ q ∈ P2 N (C9 N k1 k2), GoldbachLean.Wu2008.WuSieve.S A (q.1 * q.2) (N * q.1 * q.2) (√(N / (q.1 * q.2)))
def GoldbachLean.Wu2008.WuSum.C10 (p₁ p₂ p₃ p₄ : ℕ) := ℸ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧ p₄ < ℸ k2
def GoldbachLean.Wu2008.WuSum.Y10 := ∑ q ∈ P4 N (C10 N k1 k2), GoldbachLean.Wu2008.WuSieve.S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1
def GoldbachLean.Wu2008.WuSum.C11 (p₁ p₂ p₃ p₄ : ℕ) := ℸ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < ℸ k2 ∧ ℸ k2 ≤ p₄ ∧ p₄ < ℸ (GoldbachLean.Wu2008.WuReal.em k1)
def GoldbachLean.Wu2008.WuSum.Y11 := ∑ q ∈ P4 N (C11 N k1 k2), GoldbachLean.Wu2008.WuSieve.S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1

def GoldbachLean.Wu2008.WuSum.D12 := #{a ∈ A | ArithmeticFunction.cardFactors a ≤ 2}
def GoldbachLean.Wu2008.WuSum.Esq := #{a ∈ A | GoldbachLean.Wu2008.WuSieve.Sifted N (ℸ k1) a ∧ ¬ Squarefree a}

set_option hygiene false in
notation "𝔏" A:max k1:max k2:max => 3 * GoldbachLean.Wu2008.WuSum.Y1 A N k1 + GoldbachLean.Wu2008.WuSum.Y2 A N k2 + GoldbachLean.Wu2008.WuSum.Y5 A N k1 k2 + GoldbachLean.Wu2008.WuSum.Y6 A N k1 k2 - GoldbachLean.Wu2008.WuSum.Y3 A N k1 - GoldbachLean.Wu2008.WuSum.Y4 A N k1 - 2 * GoldbachLean.Wu2008.WuSum.Y7 A N k1 - GoldbachLean.Wu2008.WuSum.Y8 A N k1 - GoldbachLean.Wu2008.WuSum.Y9 A N k1 k2 - GoldbachLean.Wu2008.WuSum.Y10 A N k1 k2 - GoldbachLean.Wu2008.WuSum.Y11 A N k1 k2

set_option maxHeartbeats 1000000 in
theorem GoldbachLean.Wu2008.WuSum.lemma22_sum (hA : GoldbachLean.Wu2008.WuReal.Admissible k1 k2) (hN : 1 < N)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (𝔏 A k1 k2 : ℤ) ≤ 4 * D12 A + 4 * Esq A N k1 := by
  unfold Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 GoldbachLean.Wu2008.WuSieve.S D12 Esq
  simp only [card_filter, sum_comm (t := A)]
  push_cast [← card_filter, natCast_card_filter _ A, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  gcongr with n hn
  have hn := hAN n hn
  have : (1:ℝ) < N := Nat.one_lt_cast.2 hN
  set T1 := ℸ k1
  set T2 := ℸ k2
  set Tm := ℸ (GoldbachLean.Wu2008.WuReal.em k1)
  set T3 := ℸ GoldbachLean.Wu2008.WuReal.e13
  obtain ⟨t12, t2m, tm3, h33, h9⟩ : T1 ≤ T2 ∧ T2 ≤ Tm ∧ Tm ≤ T3 ∧ N ≤ T3 * (T3 * T3) ∧ N ≤ T3 * T3 * (T2 * Tm) := by
    unfold T1 T2 Tm T3 WuReal.em GoldbachLean.Wu2008.WuReal.e13
    simp [← Real.rpow_add (by positivity)]
    and_intros <;> first | apply Real.rpow_le_rpow_of_exponent_le | apply Real.self_le_rpow_of_one_le
    all_goals grind [GoldbachLean.Wu2008.WuReal.Admissible]
  have hS : ∀ {M y}, (∀ r ∈ n.primeFactors, ↑r < y → r ∣ M) → GoldbachLean.Wu2008.WuSieve.Sifted M y n := by
    unfold GoldbachLean.Wu2008.WuSieve.Sifted
    grind
  by_cases hs : GoldbachLean.Wu2008.WuSieve.Sifted N T1 n
  have hP : ∀ p ∈ n.primeFactors, p.Prime ∧ ¬ p ∣ N ∧ p < N ∧ ℸ k1 ≤ p := fun p hp => by
    grind [GoldbachLean.Wu2008.WuSieve.Sifted, Nat.le_of_mem_primeFactors hp, Nat.Prime.coprime_iff_not_dvd, hn.2.2.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)]
  simp only [hs, one_dvd, and_true, true_and, ite_true]
  trans ((4 * min 1 (3 - #n.primeFactors) : ℕ) : ℤ)
  have hd : ∀ s ⊆ n.primeFactors, ∏ p ∈ s, p ∣ n := fun s h => (prod_dvd_prod_of_subset _ _ _ h).trans n.prod_primeFactors_dvd
  set D := fun z : ℝ => {p ∈ n.primeFactors | (p:ℕ) < z}
  have hk : ∀ z, #(D z) ≤ #{p ∈ GoldbachLean.Wu2008.WuSieve.PS N T1 z | p ∣ n} := fun z => card_le_card (by
    grind [GoldbachLean.Wu2008.WuSieve.PS, Nat.lt_ceil, Nat.Prime.coprime_iff_not_dvd])
  have := hk Tm
  have := hk T3
  have : #(D Tm) ≤ #(D T3) := card_le_card (by grind)
  have hm : ∀ {z p}, p ∈ n.primeFactors → ↑p < z → p ∈ D z := by grind
  set W := {q ∈ n.primeFactors ×ˢ n.primeFactors | q.1 < q.2 ∧ q.1 < T2 ∧ q.2 < Tm}
  have : #{i ∈ P2 N (C5 N k1 k2) | i.1 * i.2 ∣ n} + #{i ∈ P2 N (C6 N k1 k2) | i.1 * i.2 ∣ n} ≤ #W := by
    rw [← card_union_of_disjoint (by grind [disjoint_left, P2, C5, C6])]
    apply card_le_card
    unfold W P2 C5 C6
    simp only [← Nat.cast_lt (α := ℝ)]
    grind [dvd_of_mul_right_dvd, dvd_of_mul_left_dvd]
  by_cases hP1 : #n.primeFactors ≤ 1
  have : #W = 0 := card_filter_eq_zero_iff.2 (by grind [card_le_one])
  omega
  obtain ⟨a, hA⟩ := n.primeFactors.exists_min_image id (card_pos.1 (by omega))
  obtain ⟨b, hb⟩ := (n.primeFactors.erase a).exists_min_image id (card_pos.1 (by grind))
  rw [mem_erase] at hb
  have hab : a < b := by grind
  have hSab : GoldbachLean.Wu2008.WuSieve.Sifted (N * a) b n := hS (by grind [Nat.cast_lt, dvd_mul_left])
  have m2 : ∀ C (Q : _ → Prop), Q (a, b) → C a b → 0 < #{i ∈ P2 N C | i.1 * i.2 ∣ n ∧ Q i} := fun C Q h hC => card_pos.2 ⟨(a, b), by
    simpa [P2, Nat.Prime.coprime_iff_not_dvd, *, prod_pair hab.ne] using hd {a, b} (by grind)⟩
  have m7 := (m2 · (fun i => GoldbachLean.Wu2008.WuSieve.Sifted (N * i.1) i.2 n) hSab)
  have h3l : 2 < #n.primeFactors → 2 ≤ #(D T3) + #{i ∈ P2 N (C8 N k1) | i.1 * i.2 ∣ n ∧ GoldbachLean.Wu2008.WuSieve.Sifted (N * i.1) i.2 n} ∧ ∃ c ∈ n.primeFactors, b < c ∧ (∀ r ∈ n.primeFactors, r = a ∨ r = b ∨ c ≤ r) ∧ a * b ^ 2 < N := fun h => by
    obtain ⟨c, hc⟩ := ((n.primeFactors.erase a).erase b).exists_min_image id (card_pos.1 (by grind))
    have hbc : b < c := by grind
    have := Nat.le_of_dvd hn.1 (hd {a, b, c} (by grind))
    rw [prod_insert (by grind), prod_pair hbc.ne] at this
    have hb2 : a * b ^ 2 < N := by nlinarith [hn.2.1]
    have : (a:ℝ)^3 < N := by norm_cast; nlinarith [Nat.mul_le_mul hab.le hab.le]
    have ha3 : a < T3 := lt_of_pow_lt_pow_left₀ 3 (by positivity) (by linarith)
    refine ⟨?_, c, by grind, hbc, by grind, hb2⟩
    have := card_pos.2 ⟨a, hm hA.1 ha3⟩
    by_cases hb3 : b < T3
    have := one_lt_card.2 ⟨a, hm hA.1 ha3, b, hm hb.1.2 hb3, hab.ne⟩
    omega
    have := m7 (C8 N k1) ⟨by grind, ha3, not_lt.1 hb3, hb2⟩
    omega
  by_cases ha2 : T2 ≤ a
  have hT := (ha2.trans <| Nat.cast_le.2 <| hA.2 · ·)
  have : #W = 0 := card_filter_eq_zero_iff.2 (by grind)
  by_cases h3 : 2 < #n.primeFactors <;> try omega
  obtain ⟨h38, c, h⟩ := h3l h3
  by_cases ham : a < Tm
  rcases le_or_gt Tm b with hbm | hbm
  have := card_pos.2 ⟨a, hm hA.1 ham⟩
  rcases le_or_gt T3 c with hc3 | hc3
  have := m2 (C9 N k1 k2) (fun i => GoldbachLean.Wu2008.WuSieve.Sifted (N * i.1 * i.2) √(N / (i.1 * i.2)) n) (hS fun r hr hrs => by
    rcases h.2.2.1 r hr with rfl | rfl | h <;> simp [mul_right_comm]
    have := hc3.trans (Nat.cast_le.2 h)
    exact absurd hrs (Real.sqrt_le_iff.2 ⟨r.cast_nonneg, div_le_of_le_mul₀ (by positivity) (sq_nonneg _) (h9.trans (by rw [sq]; gcongr))⟩).not_gt) ⟨ha2, ham, hbm, h.2.2.2⟩
  omega
  have := two_lt_card.2 ⟨a, by grind, b, hm hb.1.2 (hc3.trans' (by simpa using h.2.1)), c, hm h.1 hc3, by omega⟩
  omega
  have := one_lt_card.2 ⟨a, hm hA.1 ham, b, hm hb.1.2 hbm, hab.ne⟩
  omega
  have := m7 (C7 N k1) ⟨not_lt.1 ham, hab, h.2.2.2⟩
  omega
  rw [ite_eq_right (by grind [GoldbachLean.Wu2008.WuSieve.Sifted])]
  let F C := {i ∈ P4 N C | i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ n ∧ GoldbachLean.Wu2008.WuSieve.Sifted (N * i.1) i.2.1 n}
  have := card_le_card (show W ⊆ ({a} ×ˢ (D Tm).erase a ∪ {b} ×ˢ if b < T2 then ((D Tm).erase a).erase b else ∅) ∪ (F (C10 N k1 k2) ∪ F (C11 N k1 k2)).image (·.2.2) from fun ⟨p, q⟩ hq => by
    have hq := (mem_filter.1 hq).imp_left mem_product.1
    by_cases hpa : p = a
    grind
    rcases eq_or_ne p b with rfl | hpb
    simp [hq.2.2.1, hq.2.1.ne', (hab.trans hq.2.1).ne', hm hq.1.2 hq.2.2.2]
    have := hd {a, b, p, q} (by grind [insert_subset_iff])
    rw [prod_insert (by grind), prod_insert (by grind), prod_pair hq.2.1.ne] at this
    refine mem_union_right _ (mem_image.2 ⟨(a, b, p, q), ?_, rfl⟩)
    unfold F P4 C10 C11
    grind [Nat.Prime.coprime_iff_not_dvd, mul_assoc])
  grw [card_union_le, card_union_le, card_product] at this
  simp_all
  grind
  split_ifs <;> try omega
  rw [ArithmeticFunction.cardFactors_apply, ← List.toFinset_card_of_nodup ((Nat.squarefree_iff_nodup_primeFactorsList hn.1.ne').1 ‹_›), Nat.toFinset_factors] at *
  omega
  simp_all
  unfold GoldbachLean.Wu2008.WuSieve.Sifted
  grind

def GoldbachLean.Wu2008.WuSum.wuA := ((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)).image (fun p => N - p)

set_option hygiene false in
notation "𝔚" k1:max k2:max => (𝔏 (GoldbachLean.Wu2008.WuSum.wuA N) k1 k2 : ℝ) ≤ 4 * GoldbachLean.Wu2008.WuSum.D12 (GoldbachLean.Wu2008.WuSum.wuA N) + 4 * (N / (ℸ k1 - 1))

theorem GoldbachLean.Wu2008.WuSum.lemma22_wuA (hA : GoldbachLean.Wu2008.WuReal.Admissible k1 k2) (hN : 1 < N) (hNk : 1 < ℸ k1) :
    𝔚 k1 k2 := by
  have hAN : ∀ a ∈ wuA N, 0 < a ∧ a < N ∧ a.Coprime N := by
    unfold wuA
    grind [Nat.Prime.two_le, Nat.coprime_self_sub_left, Nat.Prime.coprime_iff_not_dvd]
  have := lemma22_sum _ N k1 k2 hA hN hAN
  rify at this
  set M := ⌈ℸ k1 - 1⌉₊
  have : (Esq (wuA N) N k1 : ℝ) ≤ N / (ℸ k1 - 1) := by
    grw [Esq, card_le_card (t := (Ioc M (N + M)).biUnion fun q => {a ∈ Ioc 0 N | q * q ∣ a}), card_biUnion_le]
    push_cast [Nat.Ioc_filter_dvd_card_eq_div]
    grw [Nat.cast_div_le]
    push_cast [div_eq_mul_inv, ← mul_sum, ← sq]
    grw [sum_Ioc_inv_sq_le_sub (Nat.ceil_pos.2 (by linarith)).ne' (by omega), sub_le_self _ (by positivity), inv_anti₀ (by linarith) (Nat.le_ceil _)]
    simp [Nat.squarefree_iff_prime_squarefree, subset_iff]
    intro a haA hs q hq hqa
    have h := hAN a haA
    have hqa' := dvd_of_mul_left_dvd hqa
    have : M < q := Nat.cast_lt.1 ((Nat.ceil_lt_add_one (by linarith)).trans_le (by linarith [not_lt.1 fun h' => hs q hq h' (hq.coprime_iff_not_dvd.1 (h.2.2.coprime_dvd_left hqa')) hqa']))
    have := Nat.le_of_dvd h.1 hqa'
    exact ⟨q, by omega, by omega, hqa⟩
  linarith

def GoldbachLean.Li2024.Lemma31.lk1 : ℝ := 100 / 1149
def GoldbachLean.Li2024.Lemma31.lk2 : ℝ := 100 / 618

theorem GoldbachLean.Li2024.Lemma31.li_admissible : GoldbachLean.Wu2008.WuReal.Admissible GoldbachLean.Li2024.Lemma31.lk1 GoldbachLean.Li2024.Lemma31.lk2 := by
  unfold GoldbachLean.Wu2008.WuReal.Admissible GoldbachLean.Li2024.Lemma31.lk1 GoldbachLean.Li2024.Lemma31.lk2
  norm_num

theorem GoldbachLean.Li2024.Lemma31.lemma31_repaired (hN : 1 < N) (hNk : 1 < ℸ GoldbachLean.Li2024.Lemma31.lk1) : 𝔚 GoldbachLean.Li2024.Lemma31.lk1 GoldbachLean.Li2024.Lemma31.lk2 :=
  GoldbachLean.Wu2008.WuSum.lemma22_wuA N GoldbachLean.Li2024.Lemma31.lk1 GoldbachLean.Li2024.Lemma31.lk2 GoldbachLean.Li2024.Lemma31.li_admissible hN hNk
