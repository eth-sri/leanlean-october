module

public import NearlyMinimax.PopulationRowDerivatives

@[expose] public section

/-! The three actual polynomial families in U5(4), including the formal-response
derivative, share a degree-independent population derivative bound. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

def incrementFinRawVector r a b T
    (response : Bool) m  :=
  fun x i => MvPolynomial.eval x
    (MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
      (rawIncrementEntryPolynomial r a b T response m i))

theorem incrementFinVector_affine r a b T
    y m :
    incrementFinVector r a b T y m = incrementFinRawVector r a b T false m -
      y • incrementFinRawVector r a b T true m := by
  funext x i
  simp only [incrementFinVector, incrementFinPolynomial, incrementFinRawVector,
    MvPolynomial.eval_rename, incrementEntryPolynomial_affine,
    map_sub, map_mul, MvPolynomial.eval_C, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

end NearlyMinimax
