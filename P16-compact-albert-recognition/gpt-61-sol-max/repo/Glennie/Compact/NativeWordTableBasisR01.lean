/- The chosen Jordan words form a basis: coordinate equations give independence. -/
module

public import Glennie.Hilbert
public import AlbertGeometry.LinearSimp
public import Glennie.Native.CoordinateSimp
public import Glennie.Compact.NativeWordTableCoordinatesR01
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Module Glennie
set_option maxHeartbeats 0

theorem nativeWords_linearIndependent : LinearIndependent ℝ nativeWords := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := hc
  norm_num [Albert.ext_iff, Prod.ext_iff, Quaternion.ext_iff, albert_coords, Fin.sum_univ_succ, nativeWords, SubmissionR03.wordValues, SubmissionR03.f0, SubmissionR03.f1, SubmissionR03.f2, marks, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] at h
  fin_cases i <;> dsimp only <;> linarith! only [h]

theorem word_card_eq : Fintype.card (Fin 27) = finrank ℝ Albert := by
  exact albert_finrank.symm

def wordBasis : Basis (Fin 27) ℝ Albert :=
  basisOfLinearIndependentOfCardEqFinrank nativeWords_linearIndependent word_card_eq

theorem wordBasis_eq_nativeWords (i : Fin 27) : wordBasis i = nativeWords i :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

                                                                          
                                                                           

end
end Glennie.Compact.NativeWordTableR01
