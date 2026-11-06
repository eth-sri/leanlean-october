module
public import GafniTao.WooleySection7Omega
public import GafniTao.WooleySection7HardArithmetic
public import GafniTao.WooleyPadicSeparation
public import GafniTao.WooleyTupleDisplacement

@[expose] public section

/-!
# The valuation cancellation in Wooley equations (7.10)--(7.12)

The change of equations in Section 7 produces a common factor
`omega * p^d`, where `omega` is prime to the source prime.  This file keeps
the two logically distinct cancellations explicit: `omega` is a unit modulo
every prime power, whereas cancelling `p^d` lowers the modulus by exactly
`d`.  This is the arithmetic loss used in the definition of `B'` in (7.3).
-/

namespace GafniTao

noncomputable section

open Finset Polynomial

/-- The unit extracted from a separated residue difference stays invertible
modulo every power of the source prime. -/
theorem wooleySection7_unit_isUnit_primePower
    {p L : ℕ} {omega : ℤ}
    (hcop : Nat.Coprime p omega.natAbs) :
    IsUnit (omega : ZMod (p ^ L)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  simpa using hcop.pow_left L

/-- Exact integer divisibility cancellation underlying the passage from
modulus `p^(d+L)` to modulus `p^L`.  The coprime factor costs no modulus. -/
theorem wooleySection7_primePower_unit_cancel_dvd
    {p d L : ℕ} {omega z : ℤ} (hp : p ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hdiv : (p : ℤ) ^ (d + L) ∣ (p : ℤ) ^ d * omega * z) :
    (p : ℤ) ^ L ∣ z := by
  have hpd : (p : ℤ) ^ d ≠ 0 := pow_ne_zero d (by exact_mod_cast hp)
  have hcancel : (p : ℤ) ^ L ∣ omega * z := by
    rw [pow_add, mul_assoc] at hdiv
    exact (Int.mul_dvd_mul_iff_left hpd).mp hdiv
  have hcopInt : IsCoprime ((p : ℤ) ^ L) omega := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop.pow_left L
  exact hcopInt.dvd_of_dvd_mul_left hcancel

/-- Cancelling a larger row-dependent power yields every weaker common
modulus.  In Section 7 one takes `e = a*l + (k-r)*gamma` and bounds it by
`r*a + (k-r)*gamma`. -/
theorem wooleySection7_primePower_unit_cancel_to_common
    {p e d M : ℕ} {omega z : ℤ} (hp : p ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hed : e ≤ d) (hdM : d ≤ M)
    (hdiv : (p : ℤ) ^ M ∣ (p : ℤ) ^ e * omega * z) :
    (p : ℤ) ^ (M - d) ∣ z := by
  have heM : e ≤ M := hed.trans hdM
  have hrewrite : M = e + (M - e) := (Nat.add_sub_of_le heM).symm
  have hfirst : (p : ℤ) ^ (M - e) ∣ z := by
    apply wooleySection7_primePower_unit_cancel_dvd hp hcop
    rw [← hrewrite]
    exact hdiv
  have hle : M - d ≤ M - e := Nat.sub_le_sub_left hed M
  exact dvd_trans (pow_dvd_pow (p : ℤ) hle) hfirst

/-- Integral tuple displacement, before reduction modulo the Fourier
modulus.  Keeping this integer representative makes exact valuation losses
available to the Section 7 argument. -/
def wooleyIntegerTupleDisplacement {I : Type*}
    (s : ℕ) (value : I → ℤ)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) : ℤ :=
  (∑ i, value (xy.1 i)) - ∑ i, value (xy.2 i)

/-- Reduction of the integral displacement is exactly the displacement used
by finite Fourier orthogonality. -/
theorem wooleyIntegerTupleDisplacement_cast
    {I : Type*} (q k s : ℕ)
    (value : I → Fin k → ℤ)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) (j : Fin k) :
    (wooleyIntegerTupleDisplacement s (fun x => value x j) xy : ZMod q) =
      wooleyTupleDisplacement q k s
        (fun x l => (value x l : ZMod q)) xy j := by
  simp [wooleyIntegerTupleDisplacement, wooleyTupleDisplacement]

/-- The literal lower-degree system in (7.11). -/
def wooleySection7LowerSystem
    (r p d : ℕ) (Xi : Fin r → Polynomial ℤ) :
    WooleyPolynomialSystem r := fun l =>
  X ^ ((l : ℕ) + 1) + C ((p : ℤ) ^ d) * Xi l

theorem wooleySection7LowerSystem_spaced
    (r p d : ℕ) (Xi : Fin r → Polynomial ℤ) :
    (wooleySection7LowerSystem r p d Xi).Spaced p d := by
  exact ⟨Xi, fun _ => rfl⟩

end

end GafniTao
