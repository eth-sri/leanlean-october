module

public import GoldbachLean.Wu2008.Real

/-!
T1, unit U-1123, PC run 20261020T0003Z-10609. P0043 J. Wu, Chen's double sieve, Goldbach's
conjecture and the twin prime problem, 2, Acta Arith. 131, 2008, arXiv 0709.3764, Lemma 2.2, p. 371
of the journal version, with Υ₁₁ repaired to p₄ < N^{1/2−3κ₁} per F-0050, now for INTEGERS.

For an integer N > 1 and a squarefree integer 0 < a < N with every prime factor at least N^κ₁, the
terms Υ₂ to Υ₁₁ of Lemma 2.2 are written below as counts over the prime factors of a, with the
conditions exactly as products of primes against powers of N, and with the intended sieve sets:
"sifted by P(Np₁) at level p₂" for p₁ p₂ | a is `lowP`, every prime factor of a below p₂ is p₁;
Υ₉'s "every prime factor below (N/p₁p₂)^{1/2} is p₁ or p₂" is `N ≤ p₁ p₂ q²` or q = p₁ or q = p₂.
Any κ₁, κ₂ under Wu's hypotheses of Lemma 2.2, κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2, 3κ₁ − κ₂ ≤ 1/6,
as read on ar5iv 0709.3764 on 2026-10-20; Wu's own κ₁ = 1/13.27, κ₂ = 1/8.24 is `pointwise_wu`.
Υ₁ = 1 since a is sifted at N^κ₁.

Plain math twin, `pointwise_int`: 4·[Ω(a) ≤ 2] ≥ 3 + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁.
Proof: send each prime p | a to its real exponent log p / log N; this is strictly increasing and
turns every product condition into a linear one, so each count equals the count of
Wu2008Lemma22Real.lean, where the inequality is proved. Coprimality of a to N is not needed in
this pointwise form, since only prime factors of a are counted.
What this does not cover: a not squarefree, Wu's O(N^{1−κ₁}) term, and the summation over
A = {N − p}, which is linear once the inequality holds for each a.
KNOWN mathematics, Wu's lemma with its range fixed. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuInt
open Finset Real
open scoped ArithmeticFunction.Omega
open GoldbachLean.Wu2008.WuReal (e13)

@[expose] public noncomputable section
open scoped Classical

/-! ## Transfer lemmas -/

section transfer
variable {α β : Type*} [DecidableEq β]

lemma card_filter_image {s : Finset α} {f : α → β} (hf : Set.InjOn f s) {R : α → Prop}
    {Q : β → Prop} [DecidablePred R] [DecidablePred Q] (h : ∀ p ∈ s, R p ↔ Q (f p)) :
    #(s.filter R) = #((s.image f).filter Q) := by
  rw [filter_image, card_image_of_injOn (hf.mono (fun x hx => (mem_filter.1 hx).1))]
  congr 1
  exact filter_congr h

end transfer

variable (N : ℕ)

def ex (p : ℕ) : ℝ := Real.log p / Real.log N

variable {N}

section expo
variable (hN : 1 < N)
include hN

lemma logN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)

lemma x_lt_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : ex N p < ex N q ↔ p < q := by
  unfold ex
  rw [div_lt_div_iff_of_pos_right (logN_pos hN), Real.log_lt_log_iff (by exact_mod_cast hp)
    (by exact_mod_cast hq), Nat.cast_lt]

lemma x_le_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : ex N p ≤ ex N q ↔ p ≤ q := by
  rw [← not_lt, x_lt_iff hN hq hp, not_lt]

lemma x_eq_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : ex N p = ex N q ↔ p = q := by
  rw [le_antisymm_iff, x_le_iff hN hp hq, x_le_iff hN hq hp, ← le_antisymm_iff]

lemma lt_rpow_iff {p : ℕ} (hp : 0 < p) (κ : ℝ) : (p : ℝ) < (N : ℝ) ^ κ ↔ ex N p < κ := by
  unfold ex
  rw [Real.lt_rpow_iff_log_lt (by exact_mod_cast hp) (by positivity),
    div_lt_iff₀ (logN_pos hN)]

lemma rpow_le_iff {p : ℕ} (hp : 0 < p) (κ : ℝ) : (N : ℝ) ^ κ ≤ (p : ℝ) ↔ κ ≤ ex N p := by
  rw [← not_lt, lt_rpow_iff hN hp, not_lt]

lemma mul_sq_lt_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    p * q ^ 2 < N ↔ ex N p + 2 * ex N q < 1 := by
  have hL := logN_pos hN
  have h0 : (0 : ℝ) < ((p * q ^ 2 : ℕ) : ℝ) := by positivity
  rw [← Nat.cast_lt (α := ℝ), ← Real.log_lt_log_iff h0 (by positivity),
    Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow]
  unfold ex
  field_simp [hL.ne']
  ring_nf

lemma le_mul_mul_sq_iff {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    N ≤ p * q * r ^ 2 ↔ 1 ≤ ex N p + ex N q + 2 * ex N r := by
  have hL := logN_pos hN
  have h0 : (0 : ℝ) < ((p * q * r ^ 2 : ℕ) : ℝ) := by positivity
  rw [← Nat.cast_le (α := ℝ), ← Real.log_le_log_iff (by positivity) h0,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  unfold ex
  field_simp [hL.ne']
  ring_nf

end expo

variable (a : ℕ)

lemma pos_of_mem {p : ℕ} (hp : p ∈ a.primeFactors) : 0 < p :=
  (Nat.prime_of_mem_primeFactors hp).pos

/-- `p₁ = e`, `p₂ = f`: every prime factor of `a` below `f` is `e`. -/
def lowP (e f : ℕ) : Prop := ∀ q ∈ a.primeFactors, f ≤ q ∨ q = e

section counts
variable (hN : 1 < N)
include hN

lemma injP : Set.InjOn (ex N) (a.primeFactors : Set ℕ) :=
  fun p hp q hq h => (x_eq_iff hN (pos_of_mem a hp) (pos_of_mem a hq)).1 h

lemma lowP_iff {e f : ℕ} (he : 0 < e) (hf : 0 < f) :
    lowP a e f ↔ WuReal.low2 (a.primeFactors.image (ex N)) (ex N e) (ex N f) := by
  unfold lowP WuReal.low2
  rw [forall_mem_image]
  exact forall₂_congr fun q hq => by
    rw [x_le_iff hN hf (pos_of_mem a hq), x_eq_iff hN (pos_of_mem a hq) he]

end counts

/-! ## Vacuity: the F-0050 shape as an actual integer -/

end

end GoldbachLean.Wu2008.WuInt
