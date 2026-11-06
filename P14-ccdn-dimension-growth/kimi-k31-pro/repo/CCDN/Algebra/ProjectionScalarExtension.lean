module

public import CCDN.Algebra.PolynomialLinearDescent
public import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.Algebra.IdealScalarDescent

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma mem_projectionCoordinateMap_ker
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K) (f : MvPolynomial (Fin m) K) :
    f ∈ RingHom.ker (projectionCoordinateMap I a) ↔ aeval a f ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

end
end CCDN
