/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialLinearDescent
public import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Algebra.IdealScalarDescent

/-! Scalar extension commutes with a polynomial image ideal.
Consequently a polynomial projection of a geometrically integral source
has a geometrically integral image. -/

public section
namespace CCDN
open MvPolynomial

/-- A polynomial `f` lies in the kernel of the coordinate map `Y i ↦ a i` into
`MvPolynomial (Fin n) K ⧸ I` if and only if the substitution `aeval a f` lies in `I`. -/
lemma mem_projectionCoordinateMap_ker
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K) (f : MvPolynomial (Fin m) K) :
    f ∈ RingHom.ker (projectionCoordinateMap I a) ↔ aeval a f ∈ I := by
  exact Ideal.Quotient.eq_zero_iff_mem

end CCDN
