/- Assemble the original twenty native columns without recomputing their400
   entries. The literal base, original HALF product, native dictionary,
   ordered contexts and rowLedger exponential family are used.
   No desired derivative, Jacobian, determinant or invertibility is assumed.
   No whole-fibre classification or common-velocity/shared-LU join is claimed. -/
module

public import Glennie.Compact.NativeFlatColumnsA
public import Glennie.Compact.NativeFlatColumnsB
public import Glennie.Compact.NativeFlatColumnsC
public import Glennie.Compact.NativeFlatColumnsD

@[expose] public section

namespace Glennie.Compact.NativeFlatRank20

open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily


/-- One continuous linear equivalence is the actual strict derivative of the
    same original family. Its SAME inverse obeys both inverse laws. No such
    equivalence, derivative equality or inverse is supplied as a hypothesis. -/
theorem native_rank20_strict_with_inverse :
    ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) =
        rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR] ∧
      HasStrictFDerivAt (rowLedger ![flatFrameP, flatFrameQ, flatFrameR])
        (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 ∧
      (∀ x : Fin 20 → ℝ,
        e.symm (rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR] x) = x) ∧
      (∀ y : Fin 20 → ℝ,
        rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR] (e.symm y) = y) := by
  obtain ⟨e, he⟩ := Glennie.Compact.Rank20.rank20_of_bridge ![flatFrameP, flatFrameQ, flatFrameR] fun r n => by
    fin_cases n <;> simp
  refine ⟨e, he, Glennie.Compact.Rank20.hasStrictFDerivAt_rowLedger_of_equiv _ e he, ?_⟩
  rw [← he]
  exact ⟨e.symm_apply_apply, e.apply_symm_apply⟩

end Glennie.Compact.NativeFlatRank20
