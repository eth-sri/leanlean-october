/- Small trace/adjugate
contractions against the full compact native SectorModel. No factor,
covariance, reduction, specialness or endpoint is assumed as a field. -/
module
public import Glennie.Native.SectorArgumentAction

@[expose] public section
namespace Glennie.SectorContraction
noncomputable section

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

/- Newton's polarized matrix adjugate expression. Its equality with the actual
polar adjugate, where needed by native U, is a separate producer obligation. -/
/- Polynomial adjugate contraction, including every singular hidden matrix. -/
theorem hidden_adjugate_gram (M : M3) :
    M.conjTranspose * sectorAdjointAdjugate M = star M.det • (1 : M3) := by
  simp only [sectorAdjointAdjugate, ← Matrix.conjTranspose_mul, Matrix.adjugate_mul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one]

/- Contract before expanding any hidden coordinates. This turns the cubic
hidden product into a determinant times one small complex trace. -/
theorem hidden_adjugate_trace (M S B : M3) :
    ((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace =
      star M.det*(S.conjTranspose*B).trace := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc M.conjTranspose, hidden_adjugate_gram]
  simp [Matrix.trace_smul, smul_eq_mul]

/- For the actual anti-Hermitian adjugate commutator, retain the crucial minus
sign. No invertibility of M or nonzero determinant is used. -/
theorem hidden_cubic_real (M S B : M3) (hS : S.conjTranspose = -S) :
    2*((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace.re =
      -2*(star M.det*(S*B).trace).re := by
  rw [hidden_adjugate_trace,hS,Matrix.neg_mul,Matrix.trace_neg]
  simp only [mul_neg,Complex.neg_re]
  ring

/- The purely complex scalar part cancels by two cyclic rotations. -/
theorem trace_comm_mul_sum (X Y : M3) :
    ((X*Y-Y*X)*(X+Y)).trace = 0 := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add]
  grind [Matrix.mul_assoc, Matrix.trace_mul_comm]

/- Polarized adjugate trace self-adjointness, valid even for arbitrary matrices.
The proof normalizes only scalar traces; it expands no native coordinates. -/
theorem trace_polar_transfer (C G B : M3) :
    (C*SectorArgumentAction.gamma G B).trace = (G*SectorArgumentAction.gamma C B).trace := by
  simp only [SectorArgumentAction.gamma, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  grind [Matrix.trace_mul_comm, Matrix.trace_mul_cycle']

end
end Glennie.SectorContraction
