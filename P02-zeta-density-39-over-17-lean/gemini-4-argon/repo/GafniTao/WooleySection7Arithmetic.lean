module
public import GafniTao.WooleyPolynomialLemma63
public import GafniTao.WooleyIterationArithmetic

@[expose] public section

/-!
# Arithmetic ledger for Wooley Section 7

The source parameter `B'` is signed.  Keeping it in `ℤ` avoids silently
truncating the easy branch at zero.  The natural depth used in the hard branch
is introduced only after positivity has been proved.
-/

namespace GafniTao

noncomputable section

/-- Equation (7.2). -/
def wooleySection7NextB (k r b : ℕ) : ℕ :=
  ((k - r + 1) * b) ⌈/⌉ r

/-- Equation (7.3), as the signed integer occurring in the source. -/
def wooleySection7BPrimeInt (k r a b gamma : ℕ) : ℤ :=
  (((k - r + 1) * b : ℕ) : ℤ) - ((r * a : ℕ) : ℤ) -
    (((k - r) * gamma : ℕ) : ℤ)

theorem wooleySection7NextB_eq_wooleyNextB
    (k r b : ℕ) :
    wooleySection7NextB k r b = wooleyNextB k r b := rfl

theorem wooley_section7_nextB_mul_upper
    {k r b : ℕ} (hr : 1 ≤ r) :
    r * wooleySection7NextB k r b ≤ (k - r + 1) * b + r := by
  have hrPos : 0 < r := by omega
  let n := (k - r + 1) * b
  have hdiv : r * ((n + r - 1) / r) ≤ n + r - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (n + r - 1) r
  have hle : n + r - 1 ≤ n + r := Nat.sub_le _ _
  simpa [wooleySection7NextB, Nat.ceilDiv_eq_add_pred_div, n] using
    hdiv.trans hle

theorem wooley_section7_BPrimeInt_pos_toNat
    {k r a b gamma nu : ℕ}
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    0 < wooleySection7BPrimeInt k r a b gamma := by
  exact lt_of_le_of_lt (Int.natCast_nonneg nu) hBPrime

/-- The natural modulus depth used after the hard-branch assumption (7.5). -/
def wooleySection7BPrimeNat (k r a b gamma : ℕ) : ℕ :=
  (wooleySection7BPrimeInt k r a b gamma).toNat

theorem wooleySection7BPrimeNat_cast
    {k r a b gamma nu : ℕ}
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    (wooleySection7BPrimeNat k r a b gamma : ℤ) =
      wooleySection7BPrimeInt k r a b gamma := by
  exact Int.toNat_of_nonneg
    (wooley_section7_BPrimeInt_pos_toNat hBPrime).le


