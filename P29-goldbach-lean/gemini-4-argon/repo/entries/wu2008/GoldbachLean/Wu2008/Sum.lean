module

public import Mathlib

open Finset
open scoped ArithmeticFunction.Omega

@[expose] public noncomputable section
open scoped Classical

namespace GoldbachLean.Wu2008.WuSieve

def Sifted (D) (y : ℝ) (a) :=
  ∀ q, Nat.Prime q → ↑q < y → ¬ q ∣ D → ¬ q ∣ a

def S (A e D y) :=
  #{a ∈ A | e ∣ a ∧ Sifted D y a}

abbrev PS (N) (w z : ℝ) :=
  {p ∈ range ⌈z⌉₊ | Nat.Prime p ∧ w ≤ p ∧ ↑p < z ∧ p.Coprime N}

end GoldbachLean.Wu2008.WuSieve

namespace GoldbachLean.Wu2008.WuReal

variable (k1 k2 : ℝ)

abbrev wk1 : ℝ := 100 / 1327
abbrev wk2 : ℝ := 100 / 824
abbrev em := 1 / 2 - 3 * k1
abbrev e13 : ℝ := 1 / 3

abbrev Admissible :=
  1 / 18 ≤ k1 ∧ k1 < k2 ∧ 3 * k1 + k2 < 1 / 2 ∧ 3 * k1 - k2 ≤ 1 / 6

theorem wu_admissible : Admissible wk1 wk2 := by norm_num [Admissible]

end GoldbachLean.Wu2008.WuReal

namespace GoldbachLean.Wu2008.WuSum
open GoldbachLean.Wu2008.WuSieve (Sifted S PS)
open GoldbachLean.Wu2008.WuReal (e13 em Admissible)

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ) (p₁ p₂ p₃ p₄ : ℕ)

set_option quotPrecheck false
local notation "E" κ:max => (N : ℝ) ^ κ
local notation "n1" => E k1
local notation "n2" => E k2
local notation "nm" => E (em k1)
local notation "n3" => E e13

abbrev P2 (C : _ → _ → Prop) :=
  {q ∈ range N ×ˢ range N | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧ C q.1 q.2}

abbrev P4 (C : _ → _ → _ → _ → Prop) :=
  {q ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N | q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
    q.2.2.2.Prime ∧ q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
    C q.1 q.2.1 q.2.2.1 q.2.2.2}

def Y1 := S A 1 N n1
def Y2 := S A 1 N n2
local notation "X" z:max => ∑ p ∈ PS N n1 z, S A p N n1
def Y3 := X n3
def Y4 := X nm
local notation "V" c:max => ∑ q ∈ P2 N (c N k1 k2), S A (q.1 * q.2) N n1
def C5 := n1 ≤ p₁ ∧ p₁ < p₂ ∧ ↑p₂ < n2
def Y5 := V C5
def C6 := n1 ≤ p₁ ∧ ↑p₁ < n2 ∧ n2 ≤ p₂ ∧ ↑p₂ < nm
def Y6 := V C6
local notation "Z" c:max => ∑ q ∈ P2 N (c N k1), S A (q.1 * q.2) (N * q.1) q.2
def C7 := nm ≤ p₁ ∧ p₁ < p₂ ∧ p₁ * p₂ ^ 2 < N
def Y7 := Z C7
def C8 := n1 ≤ p₁ ∧ ↑p₁ < n3 ∧ n3 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
def Y8 := Z C8
def C9 := n2 ≤ p₁ ∧ ↑p₁ < nm ∧ nm ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
def Y9 := ∑ q ∈ P2 N (C9 N k1 k2),
  S A (q.1 * q.2) (N * q.1 * q.2) (Real.sqrt (N / (q.1 * q.2)))
local notation "U" c:max =>
  ∑ q ∈ P4 N (c N k1 k2), S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1
def C10 := n1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧ ↑p₄ < n2
def Y10 := U C10
def C11 := n1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ ↑p₃ < n2 ∧ n2 ≤ p₄ ∧ ↑p₄ < nm
def Y11 := U C11

def D12 := #{a ∈ A | Ω a ≤ 2}
def Esq := #{a ∈ A | Sifted N n1 a ∧ ¬ Squarefree a}

abbrev pairsLT (S : Finset ℕ) := (S ×ˢ S).filter fun p => p.1 < p.2

lemma pairsLT_erase {S} (h : S.Nonempty) :
    #(pairsLT S) ≤ #(pairsLT (S.erase (S.min' h))) + #(S.erase (S.min' h)) :=
  (card_le_card fun ⟨a, b⟩ hab => by
    simp_all; have := S.min'_le a hab.1.1; omega).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left (card_image_le (f := (S.min' h, ·))) _))

lemma sifted_le {N a y p} (hcop : Nat.Coprime a N) (hs : Sifted N y a)
    (hp : p ∈ a.primeFactors) : y ≤ p := by
  obtain ⟨hpr, hpa, -⟩ := Nat.mem_primeFactors.1 hp
  exact not_lt.1 fun h => hs p hpr h (hpr.coprime_iff_not_dvd.1 (hcop.coprime_dvd_left hpa)) hpa

lemma swap1 {ι I} {P : _ → _ → Prop} [∀ i : ι, DecidablePred (P i)] :
    (∑ i ∈ I, #{a ∈ A | P i a}) = ∑ a ∈ A, #{i ∈ I | P i a} := by
  simp only [card_filter]; exact sum_comm

scoped notation "L" T:max A:max N:max k1:max k2:max R:max =>
  (3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 : T) - Y3 A N k1 - Y4 A N k1
    - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2
    ≤ 4 * D12 A + 4 * R

theorem lemma22_sum (hA : Admissible k1 k2) (hN : 1 < N)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    L ℤ A N k1 k2 (Esq A N k1) := by
  simp only [Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, D12, Esq, S, one_dvd, true_and, swap1 A]
  repeat rw [card_filter]
  push_cast
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_le_sum fun a ha => ?_
  obtain ⟨ha0, haN, hcop⟩ := hAN a ha
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hA
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have rle {x y : ℝ} (h : x ≤ y := by dsimp [WuReal.em, e13]; linarith) : E x ≤ E y :=
    Real.rpow_le_rpow_of_exponent_le hN1.le h
  have c2m : n2 ≤ nm := rle
  have cm3 : nm ≤ n3 := rle
  by_cases hs : Sifted N n1 a
  swap
  · have hs2 : ¬ Sifted N n2 a := fun h => hs fun q hq hqy => h q hq (hqy.trans_le (rle hA2.le))
    simp only [hs, hs2, and_false, false_and, filter_false, card_empty, ite_false, Nat.cast_zero]
    omega
  simp only [hs, true_and, ite_true]
  set P := a.primeFactors
  have mp {q} (hq : Nat.Prime q) (hd : q ∣ a) : q ∈ P := Nat.mem_primeFactors.2 ⟨hq, hd, ha0.ne'⟩
  have pok {p} (h : p ∈ P) : p.Prime ∧ p ∣ a ∧ p < N ∧ p.Coprime N := by
    obtain ⟨hp, hd, -⟩ := Nat.mem_primeFactors.1 h
    exact ⟨hp, hd, (Nat.le_of_dvd ha0 hd).trans_lt haN, hcop.coprime_dvd_left hd⟩
  have pcop {p q} (hp : p ∈ P) (hq : q ∈ P) (h : p < q := by omega) : p.Coprime q :=
    (Nat.coprime_primes (pok hp).1 (pok hq).1).2 h.ne
  have dvd2 {p q} (h1 : p ∈ P) (h2 : q ∈ P) (h : p < q := by omega) : p * q ∣ a :=
    (pcop h1 h2).mul_dvd_of_dvd_of_dvd (pok h1).2.1 (pok h2).2.1
  have dvd3 {p q r} (h1 : p ∈ P) (h2 : q ∈ P) (h3 : r ∈ P)
      (h12 : p < q := by omega) (h23 : q < r := by omega) : p * q * r ∣ a :=
    ((pcop h1 h3).mul_left (pcop h2 h3)).mul_dvd_of_dvd_of_dvd (dvd2 h1 h2) (pok h3).2.1
  have hk {p} (h : p ∈ P) := sifted_le hcop hs h
  let Pf (z : ℝ) := P.filter fun p : ℕ => ↑p < z
  have mPf {p q z} (hp : p ∈ P) (hq : ↑q < z) (h : p ≤ q := by omega) : p ∈ Pf z :=
    mem_filter.2 ⟨hp, (Nat.cast_le.2 h).trans_lt hq⟩
  have hPf {y z} (h : y ≤ z) : Pf y ⊆ Pf z := fun p hp =>
    mPf (mem_filter.1 hp).1 ((mem_filter.1 hp).2.trans_le h)
  have hPS (z) : #(Pf z) ≤ #{p ∈ PS N n1 z | p ∣ a ∧ True} :=
    card_le_card fun p hp => by
      obtain ⟨hpP, hpz⟩ := mem_filter.1 hp
      simp [Nat.Coprime, pok hpP, hk hpP, hpz, Nat.lt_ceil.2 hpz]
  have h3 := hPS n3
  have h4 := hPS nm
  have h34 := card_le_card (hPf cm3)
  have hAB := card_sdiff_add_card_eq_card (hPf c2m)
  set A' := Pf n2
  set B' := Pf nm \ A'
  have subP2 (C S) (h : ∀ p₁ ∈ P, ∀ p₂ ∈ P, C p₁ p₂ → (p₁, p₂) ∈ S) :
      #{q ∈ P2 N C | q.1 * q.2 ∣ a ∧ True} ≤ #S :=
    card_le_card fun ⟨p₁, p₂⟩ hq => by
      obtain ⟨hqP, hd, -⟩ := mem_filter.1 hq
      obtain ⟨h1, h2, -, -, hC⟩ := (mem_filter.1 hqP).2
      exact h p₁ (mp h1 (dvd_of_mul_right_dvd hd)) p₂ (mp h2 (dvd_of_mul_left_dvd hd)) hC
  have h5 := subP2 (C5 N k1 k2) (pairsLT A') fun p₁ m1 p₂ m2 ⟨_, h12, h2k2⟩ =>
    mem_filter.2 ⟨mem_product.2 ⟨mPf m1 h2k2, mPf m2 h2k2⟩, h12⟩
  have h6 := subP2 (C6 N k1 k2) (A' ×ˢ B') fun p₁ m1 p₂ m2 ⟨_, h1k2, h2k2, h2m⟩ =>
    mem_product.2 ⟨mPf m1 h1k2, mem_sdiff.2 ⟨mPf m2 h2m, fun h => h2k2.not_gt (mem_filter.1 h).2⟩⟩
  rw [card_product] at h6
  have hs2 {p} (hp : p ∈ A') : ¬ Sifted N n2 a := fun h =>
    (sifted_le hcop h (mem_filter.1 hp).1).not_gt (mem_filter.1 hp).2
  have least2 {S : Finset ℕ} (h : 2 ≤ #S) (hS : ∀ q ∈ P, ∀ b ∈ S, ↑q < (b : ℝ) → q ∈ S) :
      ∃ a1 ∈ S, ∃ b ∈ S, a1 < b ∧ Sifted (N * a1) b a ∧
        ∃ S2, #S = #S2 + 2 ∧ #(pairsLT S) ≤ #(pairsLT S2) + 2 * #S2 + 1 ∧
          (∀ y ∈ S2, y ∈ S ∧ b < y) ∧ ∀ q ∈ S, a1 ≤ q ∧ (q = a1 ∨ q = b ∨ q ∈ S2) := by
    have h1 : S.Nonempty := card_pos.1 (by omega)
    have hc1 := card_erase_of_mem (S.min'_mem h1)
    have hp1 := pairsLT_erase h1
    set S1 := S.erase (S.min' h1)
    have h2 : S1.Nonempty := card_pos.1 (by omega)
    have hc2 := card_erase_of_mem (S1.min'_mem h2)
    have hp2 := pairsLT_erase h2
    obtain ⟨hba, hb⟩ := mem_erase.1 (S1.min'_mem h2)
    refine ⟨_, S.min'_mem h1, _, hb, by have := S.min'_le _ hb; omega,
      fun q hqp hqy hqD hqa => hqy.not_ge <| Nat.cast_le.2 <| S1.min'_le q <|
        mem_erase.2 ⟨fun h => hqD (h ▸ dvd_mul_left _ _), hS q (mp hqp hqa) _ hb hqy⟩,
      S1.erase (S1.min' h2), by omega, by omega, fun y hy => ?_,
      fun q hq => ⟨S.min'_le q hq, by simp [S1, hq]; omega⟩⟩
    obtain ⟨hyb, hy1⟩ := mem_erase.1 hy
    exact ⟨mem_of_mem_erase hy1, by have := S1.min'_le y hy1; omega⟩
  rcases Nat.lt_or_ge (#A') 2 with hA' | hA'
  swap
  · obtain ⟨a1, ha1, a2, ha2, h12, hlow, A2, hcardA, hP, hA2sub, -⟩ :=
      least2 hA' fun q hq _ hb h => mPf hq (h.trans (mem_filter.1 hb).2)
    have ha1P := (mem_filter.1 ha1).1
    have ha2P := (mem_filter.1 ha2).1
    have hP4 (S C)
        (hS : ∀ x y, (x, y) ∈ S → x ∈ A2 ∧ y ∈ P ∧ x < y ∧ C a1 a2 x y) :
        #S ≤ #{q ∈ P4 N C | q.1 * q.2.1 * q.2.2.1 * q.2.2.2 ∣ a ∧ Sifted (N * q.1) ↑q.2.1 a} := by
      refine card_le_card_of_injOn (fun p => (a1, a2, p.1, p.2)) (fun ⟨x, y⟩ hp => ?_)
        (fun _ _ _ _ h => by simpa using h)
      obtain ⟨hx2, hyP, hxy, hC⟩ := hS x y hp
      obtain ⟨hxA, hxlt⟩ := hA2sub x hx2
      have hxP := (mem_filter.1 hxA).1
      exact mem_filter.2 ⟨by simp [Nat.Coprime, pok ha1P, pok ha2P, pok hxP, pok hyP, hC],
        (((pcop ha1P hyP).mul_left (pcop ha2P hyP)).mul_left (pcop hxP hyP)).mul_dvd_of_dvd_of_dvd
          (dvd3 ha1P ha2P hxP) (pok hyP).2.1, hlow⟩
    have h10 := hP4 (pairsLT A2) (C10 N k1 k2) fun x y hp => by
      obtain ⟨⟨hx, hy⟩, hxy⟩ := by simpa using hp
      have hyA := mem_filter.1 (hA2sub y hy).1
      exact ⟨hx, hyA.1, hxy, hk ha1P, h12, (hA2sub x hx).2, hxy, hyA.2⟩
    have h11 := hP4 (A2 ×ˢ B') (C11 N k1 k2) fun x y hp => by
      obtain ⟨hx, hy⟩ := mem_product.1 hp
      obtain ⟨hxA, hxlt⟩ := hA2sub x hx
      obtain ⟨⟨hyP, hym⟩, hy2⟩ := by simpa [B', Pf, A'] using hy
      have hxn2 := (mem_filter.1 hxA).2
      exact ⟨hx, hyP, by exact_mod_cast hxn2.trans_le (hy2 hyP), hk ha1P, h12, hxlt, hxn2, hy2 hyP, hym⟩
    rw [if_neg (hs2 ha1)]
    rw [hcardA, add_mul, ← card_product] at h6
    omega
  have hP0 : #(pairsLT A') = 0 := by
    simp; exact fun a b ha hb => (card_le_one_iff.1 (by omega) hb ha).le
  have : #A' * #B' ≤ #B' := by nlinarith
  by_cases hd : #P ≤ 2
  · by_cases hsq : Squarefree a
    · have : Ω a ≤ 2 := by
        rwa [ArithmeticFunction.cardFactors_apply, ← List.toFinset_card_of_nodup
          ((Nat.squarefree_iff_nodup_primeFactorsList ha0.ne').1 hsq), Nat.toFinset_factors]
      omega
    · rw [if_pos hsq]; omega
  obtain ⟨p1, hp1, p2, hp2, h12, hlow, P', hcardP, -, hP2sub, hq⟩ :=
    least2 (by omega : 2 ≤ #P) fun _ hq _ _ _ => hq
  have hP2ne : P'.Nonempty := card_pos.1 (by omega)
  let p3 := P'.min' hP2ne
  obtain ⟨hp3, h23⟩ := hP2sub p3 (P'.min'_mem hP2ne)
  have hab2 : p1 * p2 ^ 2 < N := by nlinarith [(Nat.le_of_dvd ha0 (dvd3 hp1 hp2 hp3)).trans_lt haN]
  have mP2 {C} (hC : C p1 p2) : (p1, p2) ∈ P2 N C := by
    simp [Nat.Coprime, pok hp1, pok hp2, hC]
  have hP2 (C) (hC : C p1 p2) :
      0 < #{q ∈ P2 N C | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) ↑q.2 a} :=
    card_pos.2 ⟨(p1, p2), mem_filter.2 ⟨mP2 hC, dvd2 hp1 hp2, hlow⟩⟩
  have c1 {z} (h : ↑p1 < z) : 0 < #(Pf z) := card_pos.2 ⟨p1, mPf hp1 h⟩
  have c2 {z} (h : ↑p2 < z) : 1 < #(Pf z) :=
    one_lt_card_iff.2 ⟨p1, p2, mPf hp1 h, mPf hp2 h, h12.ne⟩
  have c38 (ha3 : ↑p1 < n3) :
      2 ≤ #(Pf n3) + #{q ∈ P2 N (C8 N k1) | q.1 * q.2 ∣ a ∧ Sifted (N * q.1) ↑q.2 a} := by
    rcases lt_or_ge ↑p2 n3 with hb3 | hb3
    · have := c2 hb3; omega
    · have := c1 ha3; have := hP2 (C8 N k1) ⟨hk hp1, ha3, hb3, hab2⟩; omega
  rcases Nat.eq_zero_or_pos (#A') with hA0 | hA1
  swap
  · obtain ⟨a1, ha1⟩ := card_pos.1 hA1
    have ha1' := mem_filter.1 ha1
    rw [if_neg (hs2 ha1)]
    have := c38 ((Nat.cast_le.2 (hq a1 ha1'.1).1).trans_lt (ha1'.2.trans_le rle))
    omega
  rw [hA0, zero_mul] at h6
  have hp1n2 : n2 ≤ p1 := not_lt.1 fun h => (c1 h).ne' hA0
  have rprod (x) {y} (hy : x ≤ y := by gcongr) (h : (N : ℝ) ≤ x := by
      rw [sq]
      repeat rw [← Real.rpow_add (by positivity)]
      exact (Real.rpow_one _).symm.trans_le rle) : (N : ℝ) ≤ y := h.trans hy
  rcases lt_or_ge ↑p1 nm with hae | hae
  · have := c1 hae
    have := c38 (hae.trans_le cm3)
    rcases lt_or_ge ↑p2 nm with hbe | hbe
    · have := c2 hbe; omega
    rcases lt_or_ge ↑p3 n3 with hc3 | hc3
    · have := two_lt_card_iff.2 ⟨p1, p2, p3, mPf hp1 hc3, mPf hp2 hc3, mPf hp3 hc3,
        h12.ne, by omega, h23.ne⟩
      omega
    have hs9 : 0 < #{q ∈ P2 N (C9 N k1 k2) | q.1 * q.2 ∣ a ∧
        Sifted (N * q.1 * q.2) (Real.sqrt (N / (q.1 * q.2))) a} := by
      refine card_pos.2 ⟨(p1, p2), mem_filter.2 ⟨mP2 ⟨hp1n2, hae, hbe, hab2⟩,
        dvd2 hp1 hp2, fun q hqp hqlt hqD hqa => ?_⟩⟩
      rcases (hq q (mp hqp hqa)).2 with rfl | rfl | h
      · exact hqD (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
      · exact hqD (dvd_mul_left _ _)
      · have hq3 : n3 ≤ q := hc3.trans (by exact_mod_cast P'.min'_le q h)
        exact hqlt.not_ge ((Real.sqrt_le_left (by positivity)).2
          (div_le_of_le_mul₀ (by positivity) (by positivity) (rprod (n3 ^ 2 * (n2 * nm)))))
    omega
  · have := hP2 (C7 N k1) ⟨hae, h12, hab2⟩
    rcases lt_or_ge ↑p1 n3 with ha3 | ha3
    · have := c38 ha3; omega
    · have := ha3.trans (Nat.cast_le.2 h12.le)
      have : (N : ℝ) ≤ p1 * p2 ^ 2 := rprod (n3 * n3 ^ 2)
      exact (hab2.not_ge (by exact_mod_cast this)).elim

abbrev wuA := ((range N).filter fun p => p.Prime ∧ ¬ p ∣ N).image (N - ·)

local notation "W" => wuA N

theorem lemma22_wuA (hA : Admissible k1 k2) (hN : 1 < N) (hNk : 1 < n1) :
    L ℝ W N k1 k2 (N / (n1 - 1)) := by
  have hAN : ∀ a ∈ W, 0 < a ∧ a < N ∧ a.Coprime N := by
    simp; rintro _ p hpN hpr hnd rfl
    have := hpr.two_le
    exact ⟨by omega, by omega, (Nat.coprime_self_sub_left hpN.le).2 (hpr.coprime_iff_not_dvd.2 hnd)⟩
  have hR := (Int.cast_le (R := ℝ)).2 (lemma22_sum W N k1 k2 hA hN hAN)
  push_cast at hR
  let M := ⌈n1⌉₊
  have hM2 : 1 < M := Nat.one_lt_cast.1 (hNk.trans_le (Nat.le_ceil _))
  let f (i) := -((N : ℝ) / (i - 1 : ℕ))
  have h1 : (Esq W N k1 : ℝ) ≤ f (M + N) - f M := by
    rw [← sum_Ico_sub f (Nat.le_add_right M N)]
    refine' (Nat.mono_cast ((card_le_card fun a ha => ?_).trans card_biUnion_le)).trans ?_
    rotate_right
    · rw [Nat.cast_sum]
      refine sum_le_sum fun i hi => ?_
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      obtain ⟨hi0, hi1⟩ : 0 < i ∧ 0 < i - 1 := by have := (mem_Ico.1 hi).1; omega
      rw [show f (i + 1) - f i = (N : ℝ) / (i * (i - 1 : ℕ)) by
        dsimp [f]; field_simp; rw [Nat.cast_sub (by omega)]; push_cast; ring, le_div_iff₀ (by positivity)]
      exact_mod_cast le_trans (by gcongr; omega) (Nat.div_mul_le_self N (i * i))
    obtain ⟨haA, hs, hsq⟩ := mem_filter.1 ha
    obtain ⟨h0, hlt, hcop⟩ := hAN a haA
    obtain ⟨q, hq, hqq⟩ := by simpa [Nat.squarefree_iff_prime_squarefree] using hsq
    have hqa := (dvd_mul_right q q).trans hqq
    have := (Nat.le_of_dvd h0 hqa).trans hlt.le
    exact mem_biUnion.2 ⟨q, mem_Ico.2 ⟨Nat.ceil_le.2 (sifted_le hcop hs
      (Nat.mem_primeFactors.2 ⟨hq, hqa, h0.ne'⟩)), by omega⟩,
      mem_filter.2 ⟨mem_Ioc.2 ⟨h0, hlt.le⟩, hqq⟩⟩
  have : -f M ≤ N / (n1 - 1) := by
    dsimp [f]; rw [neg_neg, Nat.cast_sub hM2.le, Nat.cast_one]
    gcongr; exact Nat.le_ceil _
  linarith [show f (M + N) ≤ 0 from neg_nonpos.2 (by positivity)]

end GoldbachLean.Wu2008.WuSum

namespace GoldbachLean.Li2024.Lemma31
open GoldbachLean.Wu2008.WuReal GoldbachLean.Wu2008.WuSum

abbrev lk1 : ℝ := 100 / 1149
abbrev lk2 : ℝ := 100 / 618

theorem li_admissible : Admissible lk1 lk2 := by norm_num [Admissible]

theorem lemma31_repaired (N : ℕ) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ lk1) :
    L ℝ (wuA N) N lk1 lk2 (N / (↑N ^ lk1 - 1)) :=
  lemma22_wuA N lk1 lk2 li_admissible hN hNk

end GoldbachLean.Li2024.Lemma31
end
