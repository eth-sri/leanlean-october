/- Assemble the original twenty native columns without recomputing their400
   entries. The literal base, original HALF product, native dictionary,
   ordered contexts and rowLedger exponential family are used.
   No desired derivative, Jacobian, determinant or invertibility is assumed.
   No whole-fibre classification or common-velocity/shared-LU join is claimed. -/
module

public import Glennie.Compact.NativeFlatColumns01
public import Glennie.Compact.NativeFlatColumns23
public import Glennie.Compact.NativeFlatColumns45
public import Glennie.Compact.NativeFlatColumns67
public import Glennie.Compact.NativeFlatColumns89
public import Glennie.Compact.NativeFlatColumns1011
public import Glennie.Compact.NativeFlatColumns1213
public import Glennie.Compact.NativeFlatColumns1415
public import Glennie.Compact.NativeFlatColumns1617
public import Glennie.Compact.NativeFlatColumns1819

@[expose] public section

namespace Glennie.Compact.NativeFlatRank20

open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

/-- All400 entries of the actual original native Jacobian, including every zero.
    Only the twenty column indices are split; each row remains universal. -/
theorem jacobianEntry_flatBase_all (r n : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r n = JQ r n := by
  fin_cases n
  · exact Glennie.Compact.NativeFlatColumns01.jacobianEntry_flatBase_column_zero r
  · exact Glennie.Compact.NativeFlatColumns01.jacobianEntry_flatBase_column_one r
  · exact Glennie.Compact.NativeFlatColumns23.jacobianEntry_flatBase_column_two r
  · exact Glennie.Compact.NativeFlatColumns23.jacobianEntry_flatBase_column_three r
  · exact Glennie.Compact.NativeFlatColumns45.jacobianEntry_flatBase_column_four r
  · exact Glennie.Compact.NativeFlatColumns45.jacobianEntry_flatBase_column_five r
  · exact Glennie.Compact.NativeFlatColumns67.jacobianEntry_flatBase_column_six r
  · exact Glennie.Compact.NativeFlatColumns67.jacobianEntry_flatBase_column_seven r
  · exact Glennie.Compact.NativeFlatColumns89.jacobianEntry_flatBase_column_eight r
  · exact Glennie.Compact.NativeFlatColumns89.jacobianEntry_flatBase_column_nine r
  · exact Glennie.Compact.NativeFlatColumns1011.jacobianEntry_flatBase_column_ten r
  · exact Glennie.Compact.NativeFlatColumns1011.jacobianEntry_flatBase_column_eleven r
  · exact Glennie.Compact.NativeFlatColumns1213.jacobianEntry_flatBase_column_twelve r
  · exact Glennie.Compact.NativeFlatColumns1213.jacobianEntry_flatBase_column_thirteen r
  · exact Glennie.Compact.NativeFlatColumns1415.jacobianEntry_flatBase_column_fourteen r
  · exact Glennie.Compact.NativeFlatColumns1415.jacobianEntry_flatBase_column_fifteen r
  · exact Glennie.Compact.NativeFlatColumns1617.jacobianEntry_flatBase_column_sixteen r
  · exact Glennie.Compact.NativeFlatColumns1617.jacobianEntry_flatBase_column_seventeen r
  · exact Glennie.Compact.NativeFlatColumns1819.jacobianEntry_flatBase_column_eighteen r
  · exact Glennie.Compact.NativeFlatColumns1819.jacobianEntry_flatBase_column_nineteen r

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
  obtain ⟨e, he⟩ := Glennie.Compact.Rank20.rank20_of_bridge
    ![flatFrameP, flatFrameQ, flatFrameR] jacobianEntry_flatBase_all
  refine ⟨e, he, ?_, ?_, ?_⟩
  · exact Glennie.Compact.Rank20.hasStrictFDerivAt_rowLedger_of_equiv
      ![flatFrameP, flatFrameQ, flatFrameR] e he
  · intro x
    have h : e.symm (e x) = x := e.symm_apply_apply x
    change e.symm ((e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) x) = x at h
    rw [he] at h
    exact h
  · intro y
    have h : e (e.symm y) = y := e.apply_symm_apply y
    change (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) (e.symm y) = y at h
    rw [he] at h
    exact h

end
end Glennie.Compact.NativeFlatRank20
