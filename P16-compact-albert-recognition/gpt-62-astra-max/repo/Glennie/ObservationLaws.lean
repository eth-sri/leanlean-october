module
public import Glennie.ObservationData
@[expose] public section
namespace Glennie.SubmissionR03
@[simp] theorem f0_eq : f0 = 0 := rfl
@[simp] theorem f1_eq : f1 = 1 := rfl
@[simp] theorem f2_eq : f2 = 2 := rfl
@[simp] theorem b0_eq : b0 = 0 := rfl
@[simp] theorem b1_eq : b1 = 1 := rfl
end Glennie.SubmissionR03

namespace Glennie.Compact.Affine20
export _root_.Glennie.SubmissionR03 (fullLedger mapAtoms)

/-! Projections of the 54-entry ledger, on variables. Proofs rewrite with these before any
comparison, so no unification has to unfold Albert products. -/

theorem ledger54_C (T : Triple) (i j k : Fin 3) :
    (fullLedger T).1 i j k = ledger (T 0) (T 1) (T 2) i j k := rfl

theorem ledger54_Q (T : Triple) (j k : Fin 3) :
    (fullLedger T).2.2.1 j k = inner (T 1 j) (T 2 k) := rfl

theorem ledger54_R (T : Triple) (k i : Fin 3) :
    (fullLedger T).2.2.2 k i = inner (T 2 k) (T 0 i) := rfl

theorem ledger54_map (g : CompactAutomorphism) (T : Triple) :
    fullLedger (mapAtoms g T) = fullLedger T := by
  exact Prod.ext (funext fun i => funext fun j => funext fun k => g.ledger_map _ _ _ i j k) (by simp [fullLedger, mapAtoms, g.inner_map])

end Glennie.Compact.Affine20
