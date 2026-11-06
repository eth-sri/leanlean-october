module
public import GafniTao.WooleyTaylorCoefficient

@[expose] public section

/-!
# Wooley's integral Omega matrix after equation (7.10)

This file packages the translated coefficients of the top `r` equations into
the literal integral matrix used in Section 7.  The source writes powers
`h^(k-r+l-i)` even when the exponent is negative.  We preserve that notation
as a Laurent identity over `ℚ`; integrality belongs to the matrix entry, not
to the displayed power by itself.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleySection7Node_succ_le
    {k r : ℕ} (hrk : r ≤ k) (l : Fin r) :
    wooleySection7Node k r l + 1 ≤ k := by
  unfold wooleySection7Node
  omega

/-- The integral coefficient supplied by the Laurent Taylor factorization
for row `i`, column `l` of the source matrix. -/
def wooleySection7OmegaEntry
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (i l : Fin r) : ℤ :=
  Classical.choose
    (wooley_taylorCoefficient_exists_laurent_omega
      (p := p) (c := c) (i := (i : ℕ) + 1)
      (j := wooleySection7Node k r l + 1) (k := k)
      h hh (wooleySection7Node_succ_le hrk l) (psi l))

/-- The source matrix `A=(Omega_il)`, with rows indexed by Taylor degree and
columns indexed by the top `r` source equations. -/
def wooleySection7OmegaMatrix
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i l => wooleySection7OmegaEntry (p := p) (c := c) hrk h hh psi i l

theorem wooleySection7OmegaEntry_spec
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (i l : Fin r) :
    let j := wooleySection7Node k r l + 1
    let degree := (i : ℕ) + 1
    ((taylor h
      (X ^ j + C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l)).coeff degree : ℚ) =
        (h : ℚ) ^ ((j : ℤ) - (degree : ℤ)) *
          (wooleySection7OmegaEntry (p := p) (c := c) hrk h hh psi i l : ℚ) ∧
    Int.ModEq ((p : ℤ) ^ c)
      (wooleySection7OmegaEntry (p := p) (c := c) hrk h hh psi i l)
      (Nat.choose j degree : ℤ) := by
  exact Classical.choose_spec
    (wooley_taylorCoefficient_exists_laurent_omega
      (p := p) (c := c) (i := (i : ℕ) + 1)
      (j := wooleySection7Node k r l + 1) (k := k)
      h hh (wooleySection7Node_succ_le hrk l) (psi l))

theorem wooleySection7OmegaMatrix_mod_prime
    {k r p c : ℕ} (hc : 1 ≤ c) (hrk : r ≤ k)
    (h : ℤ) (hh : h ≠ 0) (psi : Fin r → Polynomial ℤ)
    (i l : Fin r) :
    ((wooleySection7OmegaMatrix (p := p) (c := c) hrk h hh psi i l : ℤ) : ZMod p) =
      (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p) := by
  exact wooley_taylorOmega_mod_prime hc
    (wooleySection7OmegaEntry_spec (p := p) (c := c) hrk h hh psi i l).2


