module

public import NormalizerLean.Defs

@[expose] public section

/-!
# Infinite presented groups via affine (wreath) actions — T8(b)

A certificate gives, for each generator x ∈ {w, s}, a permutation σₓ of {0, …, n−1} and integers tₓ(i).
The generator x acts on ℕ × ℤ on the right by (i, m) ↦ (σₓ(i), m + tₓ(i)) for i < n, and trivially
for i ≥ n.  If every relator acts trivially, this is a homomorphism from the presented group to
(Perm (ℕ × ℤ))ᵐᵒᵖ; if moreover some word fixes the first coordinate 0 and translates by c ≠ 0, its
image has infinite order, so the presented group is infinite.  All conditions are decidable and are
checked by `decide`; the data come from `certs/infinite_cert.py` (Magma + Reidemeister–Schreier).
-/

namespace NormalizerLean

/-- Affine action data. -/
structure AffCert where
  n : ℕ
  σ : LGen → List ℕ
  σinv : LGen → List ℕ
  t : LGen → List ℤ

namespace AffCert

variable (D : AffCert)

variable {D}

end AffCert

end NormalizerLean
