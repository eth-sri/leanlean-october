module

public import Mathlib.RingTheory.AdjoinRoot
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Integral.FiniteFreeDescent

public section

@[expose] section

/-! The explicit unit-splitting functional needed for finite-free descent exists
for every positive-degree monic polynomial quotient. No field or irreducibility
hypothesis is used. -/

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Integral

noncomputable section
open Foundation

variable {R : Type*} [CommRing R] {f : Polynomial R}

/-- Constant coefficient of the unique remainder modulo a monic polynomial. -/
def monicQuotientProjection (hf : f.Monic) : AdjoinRoot f →ₗ[R] R :=
  (Polynomial.lcoeff R 0).comp (AdjoinRoot.modByMonicHom hf)

/-- The constant coefficient projection sends the quotient unit to one. -/
theorem monicQuotientProjection_one [Nontrivial R] (hf : f.Monic)
    (hdeg : 0 < f.natDegree) : monicQuotientProjection hf 1 = 1 := by
  have hmod : (1 : Polynomial R) %ₘ f = 1 :=
    (Polynomial.modByMonic_eq_self_iff hf).mpr (by
      simpa using
        Polynomial.natDegree_pos_iff_degree_pos.mp hdeg)
  change (AdjoinRoot.modByMonicHom hf (1 : AdjoinRoot f)).coeff 0 = 1
  rw [← map_one (AdjoinRoot.mk f), AdjoinRoot.modByMonicHom_mk, hmod]
  exact Polynomial.coeff_one_zero

end
end OAI.MatrixMultiplication.AuxiliarySeparation.Integral
