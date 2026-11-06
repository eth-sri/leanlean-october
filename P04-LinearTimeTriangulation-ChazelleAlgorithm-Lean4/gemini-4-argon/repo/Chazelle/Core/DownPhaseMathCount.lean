module

public import Chazelle.Core.Setup
public import Chazelle.Cost.DownPhase

/-!
# Down phase, math (D10 rest, arithmetic): the chord-count bound (I3) across the levels

The level invariant of the down phase (design `docs/design-downphase-driver.md` §2.2) bounds the
chord count by (I3) `K · 2^b ≤ cnt λ · (2^p + 2^b)` with `b = ⌈βλ⌉`, i.e.
`K ≤ cnt λ (2^p / 2^⌈βλ⌉ + 1)`.  One level (merges, extraction, `T` restoration rounds) gives a
new count `K'` with

  `K' · G ≤ A · ((K + 1) · G + B · (n + 4 K))`

(`G = γ₁ + 1 ≥ 2^⌈βμ⌉` the granularity of the region maps, `A = 2^T` the restoration factor,
`B = 560 (D_H + 2)` from Lemma 2.3 per region; `DownPhaseMathLevel`).  This file defines one
bounded count function `cnt A B` that is preserved by every level (`cnt_step`) and holds after
the transition (`cnt_trans`):

* from the threshold `cntLam A B` on, the levels **contract**: `2^(⌈βλ⌉ - ⌈βμ⌉) ≥ 8 A` and
  `2^⌈βλ⌉ ≥ 32 A B`, so the constant `cntBase A B` is preserved;
* below the threshold only a bounded number of levels remain; there `cnt` grows by the fixed
  map `cntG A B` per level, `cnt λ = (cntG A B)^[cntLam - λ] (cntBase A B) ≤ cntMax A B`.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

/-! ## The count function -/

/-- The growth of the count bound at one level below the threshold. -/
def cntG (A B x : ℕ) : ℕ := 2 * A * x + A + 2 * A * B + 8 * A * B * x

/-- The threshold exponent: `8 A ≤ 2^L` and `32 A B ≤ 2^L`. -/
def cntL (A B : ℕ) : ℕ := Nat.clog 2 (8 * A + 32 * A * B)

/-- The threshold level `λ*`: from it on the levels contract. -/
def cntLam (A B : ℕ) : ℕ := 5 * (5 * cntL A B + 16)

/-- The count constant above the threshold (`2520` covers the transition). -/
def cntBase (A B : ℕ) : ℕ := 8 * A * B + A + 2520

/-- **The count bound of level `λ`** (the `cnt` of (I3)). -/
def cnt (A B lam : ℕ) : ℕ :=
  if cntLam A B ≤ lam then cntBase A B else (cntG A B)^[cntLam A B - lam] (cntBase A B)

/-- The bound on all count constants. -/
def cntMax (A B : ℕ) : ℕ := (cntG A B)^[cntLam A B] (cntBase A B)

theorem le_cntG {A : ℕ} (hA : 1 ≤ A) (B x : ℕ) : x ≤ cntG A B x := by
  have : x ≤ 2 * A * x := by
    calc x = 1 * x := (one_mul x).symm
      _ ≤ 2 * A * x := Nat.mul_le_mul_right _ (by omega)
  unfold cntG; omega

theorem iterate_le_iterate {A : ℕ} (hA : 1 ≤ A) (B x : ℕ) {k k' : ℕ} (h : k ≤ k') :
    (cntG A B)^[k] x ≤ (cntG A B)^[k'] x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [add_comm k d, Function.iterate_add_apply]
  generalize (cntG A B)^[k] x = y
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_cntG hA B _)

theorem cntBase_le_cnt {A : ℕ} (hA : 1 ≤ A) (B lam : ℕ) : cntBase A B ≤ cnt A B lam := by
  unfold cnt
  split_ifs
  · exact le_rfl
  · exact iterate_le_iterate hA B _ (Nat.zero_le _)

/-- **The count constants are bounded.** -/
theorem cnt_le_cntMax {A : ℕ} (hA : 1 ≤ A) (B lam : ℕ) : cnt A B lam ≤ cntMax A B := by
  unfold cnt cntMax
  split_ifs
  · exact iterate_le_iterate hA B _ (Nat.zero_le _)
  · exact iterate_le_iterate hA B _ (Nat.sub_le _ _)

/-! ## The threshold -/

theorem le_two_pow_cntL (A B : ℕ) : 8 * A + 32 * A * B ≤ 2 ^ cntL A B :=
  Nat.le_pow_clog (by norm_num) _

/-- **Contraction above the threshold**: with `b = ⌈βλ⌉`, `b' = ⌈β(b + 11)⌉`,
`8 A 2^b' ≤ 2^b` and `32 A B ≤ 2^b`. -/
theorem big_of_ge {A B lam : ℕ} (h : cntLam A B ≤ lam) :
    8 * A * 2 ^ Cost.ceilBeta (Cost.ceilBeta lam + 11) ≤ 2 ^ Cost.ceilBeta lam ∧
      32 * A * B ≤ 2 ^ Cost.ceilBeta lam := by
  have hL := le_two_pow_cntL A B
  set L := cntL A B
  rw [Setup.ceilBeta_eq lam, Setup.ceilBeta_eq]
  unfold cntLam at h
  set b := (lam + 4) / 5
  have hbL : 5 * L + 16 ≤ b := by omega
  have hb' : (b + 11 + 4) / 5 + L ≤ b := by omega
  have hpow : 2 ^ ((b + 11 + 4) / 5) * 2 ^ L ≤ 2 ^ b := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hb'
  have hLb : 2 ^ L ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  constructor
  · calc 8 * A * 2 ^ ((b + 11 + 4) / 5) ≤ 2 ^ L * 2 ^ ((b + 11 + 4) / 5) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ b := by rwa [mul_comm]
  · omega

/-! ## One level -/

/-- **The arithmetic of one level.**  From (I3) `K 2^b ≤ c (2^p + 2^b)` and the level bound
`K' G ≤ A ((K + 1) G + B (n + 4 K))` with `2^b' ≤ G`: (I3) `K' 2^b' ≤ c' (2^p + 2^b')` holds
either for `c' ≥ cntG A B c`, or for `c' = c` in the contracting case. -/
theorem step_arith {p b b' K K' n c c' A B G : ℕ}
    (hK : K * 2 ^ b ≤ c * (2 ^ p + 2 ^ b)) (hb : b ≤ p) (hb' : b' ≤ b) (hn : n ≤ 2 ^ p + 1)
    (hG : 2 ^ b' ≤ G) (hK' : K' * G ≤ A * ((K + 1) * G + B * (n + 4 * K)))
    (hc : cntG A B c ≤ c' ∨
      (c' = c ∧ A ≤ c ∧ 8 * A * B ≤ c ∧ 8 * A * 2 ^ b' ≤ 2 ^ b ∧ 32 * A * B ≤ 2 ^ b)) :
    K' * 2 ^ b' ≤ c' * (2 ^ p + 2 ^ b') := by
  have hY1 : 1 ≤ 2 ^ b' := Nat.one_le_two_pow
  have hYX : 2 ^ b' ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb'
  have hXP : 2 ^ b ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hb
  set P := 2 ^ p
  set X := 2 ^ b
  set Y := 2 ^ b'
  have hG0 : 0 < G := by omega
  have h1 : K' * Y ≤ A * (K + 1) * Y + A * B * (n + 4 * K) := by
    apply Nat.le_of_mul_le_mul_right _ hG0
    calc K' * Y * G = K' * G * Y := by ring
      _ ≤ A * ((K + 1) * G + B * (n + 4 * K)) * Y := Nat.mul_le_mul_right _ hK'
      _ = A * (K + 1) * Y * G + A * B * (n + 4 * K) * Y := by ring
      _ ≤ A * (K + 1) * Y * G + A * B * (n + 4 * K) * G :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hG) _
      _ = (A * (K + 1) * Y + A * B * (n + 4 * K)) * G := by ring
  have hK2 : K * X ≤ 2 * c * P := by
    calc K * X ≤ c * (P + X) := hK
      _ ≤ c * (P + P) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * c * P := by ring
  have hn2 : n ≤ 2 * P := by have : 1 ≤ P := Nat.one_le_two_pow; omega
  have eAn : A * B * n ≤ 2 * A * B * P := by
    calc A * B * n ≤ A * B * (2 * P) := Nat.mul_le_mul_left _ hn2
      _ = 2 * A * B * P := by ring
  have e0 : K' * Y ≤ A * (K * Y) + A * Y + A * B * n + 4 * A * B * K := by
    calc K' * Y ≤ A * (K + 1) * Y + A * B * (n + 4 * K) := h1
      _ = A * (K * Y) + A * Y + A * B * n + 4 * A * B * K := by ring
  rcases hc with hc | ⟨rfl, hAc, hABc, h8, h32⟩
  · have eKY : A * (K * Y) ≤ 2 * A * c * P := by
      calc A * (K * Y) ≤ A * (K * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hYX)
        _ ≤ A * (2 * c * P) := Nat.mul_le_mul_left _ hK2
        _ = 2 * A * c * P := by ring
    have eK : 4 * A * B * K ≤ 8 * A * B * c * P := by
      have : K ≤ K * X := Nat.le_mul_of_pos_right _ (by omega)
      calc 4 * A * B * K ≤ 4 * A * B * (K * X) := Nat.mul_le_mul_left _ this
        _ ≤ 4 * A * B * (2 * c * P) := Nat.mul_le_mul_left _ hK2
        _ = 8 * A * B * c * P := by ring
    calc K' * Y ≤ A * (K * Y) + A * Y + A * B * n + 4 * A * B * K := e0
      _ ≤ 2 * A * c * P + A * Y + 2 * A * B * P + 8 * A * B * c * P := by omega
      _ ≤ cntG A B c * P + cntG A B c * Y := by
          unfold cntG
          have : A * Y ≤ A * Y + (2 * A * c + 2 * A * B + 8 * A * B * c) * Y := by omega
          nlinarith
      _ ≤ c' * P + c' * Y :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hc) (Nat.mul_le_mul_right _ hc)
      _ = c' * (P + Y) := by ring
  · have hK2' : K * X ≤ 2 * (c' * P) := by rwa [← mul_assoc]
    have eKY : 4 * (A * (K * Y)) ≤ c' * P := by
      have : 8 * (A * (K * Y)) ≤ 2 * (c' * P) := by
        calc 8 * (A * (K * Y)) = K * (8 * A * Y) := by ring
          _ ≤ K * X := Nat.mul_le_mul_left _ h8
          _ ≤ 2 * (c' * P) := hK2'
      omega
    have eK : 16 * (A * B * K) ≤ c' * P := by
      have : 32 * (A * B * K) ≤ 2 * (c' * P) := by
        calc 32 * (A * B * K) = K * (32 * A * B) := by ring
          _ ≤ K * X := Nat.mul_le_mul_left _ h32
          _ ≤ 2 * (c' * P) := hK2'
      omega
    have eN : 4 * (A * B * n) ≤ c' * P := by
      calc 4 * (A * B * n) ≤ 4 * (2 * A * B * P) := Nat.mul_le_mul_left _ eAn
        _ = 8 * A * B * P := by ring
        _ ≤ c' * P := Nat.mul_le_mul_right _ hABc
    have eA : A * Y ≤ c' * Y := Nat.mul_le_mul_right _ hAc
    have e0' : K' * Y ≤ A * (K * Y) + A * Y + A * B * n + 4 * (A * B * K) := by
      have : 4 * A * B * K = 4 * (A * B * K) := by ring
      omega
    rw [mul_add]
    omega

/-- **(I3) across one level.**  Let `16 ≤ λ ≤ p`, `μ = ⌈βλ⌉ + 11`, and let the counts `K` (level
`λ`) and `K'` (level `μ`) satisfy the level bound with `2^⌈βμ⌉ ≤ G`.  If (I3) holds at `λ` with
`cnt A B λ`, it holds at `μ` with `cnt A B μ`. -/
theorem cnt_step {A B : ℕ} (hA : 1 ≤ A) {lam p K K' n G : ℕ} (h16 : 16 ≤ lam) (hlp : lam ≤ p)
    (hK : K * 2 ^ Cost.ceilBeta lam ≤ cnt A B lam * (2 ^ p + 2 ^ Cost.ceilBeta lam))
    (hn : n ≤ 2 ^ p + 1) (hG : 2 ^ Cost.ceilBeta (Cost.ceilBeta lam + 11) ≤ G)
    (hK' : K' * G ≤ A * ((K + 1) * G + B * (n + 4 * K))) :
    K' * 2 ^ Cost.ceilBeta (Cost.ceilBeta lam + 11) ≤
      cnt A B (Cost.ceilBeta lam + 11) * (2 ^ p + 2 ^ Cost.ceilBeta (Cost.ceilBeta lam + 11)) := by
  have hbl : Cost.ceilBeta lam ≤ lam := Cost.ceilBeta_le lam
  have hμ : Cost.ceilBeta lam + 11 < lam := Cost.ceilBeta_add_eleven_lt h16
  have hb' : Cost.ceilBeta (Cost.ceilBeta lam + 11) ≤ Cost.ceilBeta lam := by
    rw [Setup.ceilBeta_eq, Setup.ceilBeta_eq lam]; omega
  refine step_arith hK (hbl.trans hlp) hb' hn hG hK' ?_
  by_cases hbig : cntLam A B ≤ Cost.ceilBeta lam + 11
  · -- both levels above the threshold
    have hlam : cntLam A B ≤ lam := by omega
    right
    have e1 : cnt A B lam = cntBase A B := by unfold cnt; rw [ite_eq_left hlam]
    have e2 : cnt A B (Cost.ceilBeta lam + 11) = cntBase A B := by unfold cnt; rw [ite_eq_left hbig]
    obtain ⟨h8, h32⟩ := big_of_ge hlam
    rw [e1, e2]
    refine ⟨rfl, by unfold cntBase; omega, by unfold cntBase; omega, h8, h32⟩
  · -- the next level is below the threshold
    left
    have e2 : cnt A B (Cost.ceilBeta lam + 11) =
        (cntG A B)^[cntLam A B - (Cost.ceilBeta lam + 11)] (cntBase A B) := by
      unfold cnt; rw [ite_eq_right hbig]
    obtain ⟨k, hk, ek⟩ : ∃ k, k + 1 ≤ cntLam A B - (Cost.ceilBeta lam + 11) ∧
        cnt A B lam = (cntG A B)^[k] (cntBase A B) := by
      by_cases hl : cntLam A B ≤ lam
      · exact ⟨0, by omega, by unfold cnt; rw [ite_eq_left hl]; rfl⟩
      · exact ⟨cntLam A B - lam, by omega, by unfold cnt; rw [ite_eq_right hl]⟩
    rw [e2, ek, ← Function.iterate_succ_apply' (cntG A B)]
    exact iterate_le_iterate hA B _ hk

/-! ## The transition -/

/-- **(I3) after the transition.**  The top-chain map is `γ'_p`-granular with cap `4`, so by
Lemma 2.3 (`c 4 = 840`, size `2 (n - 1)`) `K₀ (γ'_p + 1) ≤ 840 (2 (n - 1) + 1)`; the transition
keeps at most `K₀` chords (T4).  Then (I3) holds at `λ = p`. -/
theorem cnt_trans {A : ℕ} (hA : 1 ≤ A) (B : ℕ) {K K₀ n p : ℕ} (hn : n - 1 ≤ 2 ^ p)
    (hK₀ : K₀ * (gradeGran p + 1) ≤ 840 * (2 * (n - 1) + 1)) (hK : K ≤ K₀) :
    K * 2 ^ Cost.ceilBeta p ≤ cnt A B p * (2 ^ p + 2 ^ Cost.ceilBeta p) := by
  have hg : 2 ^ Cost.ceilBeta p ≤ gradeGran p + 1 := by unfold gradeGran; omega
  have hc := cntBase_le_cnt hA B p
  have hP1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  calc K * 2 ^ Cost.ceilBeta p ≤ K₀ * (gradeGran p + 1) := Nat.mul_le_mul hK hg
    _ ≤ 840 * (2 * (n - 1) + 1) := hK₀
    _ ≤ 2520 * 2 ^ p := by omega
    _ ≤ cntBase A B * 2 ^ p := Nat.mul_le_mul_right _ (by unfold cntBase; omega)
    _ ≤ cnt A B p * (2 ^ p + 2 ^ Cost.ceilBeta p) := Nat.mul_le_mul hc (Nat.le_add_right _ _)

end

end DownMath

end Chazelle.Core
