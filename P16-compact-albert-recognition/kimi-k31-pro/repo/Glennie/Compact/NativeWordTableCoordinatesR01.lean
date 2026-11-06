/- Finite-coordinate representation for the native word table. -/
module
public import Glennie.Compact.NativeWordCoordinateBridgeR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie AlbertGeometry.NativeOperatorTrace
open scoped BigOperators
set_option autoImplicit false

def word0 : Word := .unit
def word1 : Word := .mark 0
def word2 : Word := .mark 1
def word3 : Word := .mark 2
def word4 : Word := .mul word1 word1
def word5 : Word := .mul word1 word2
def word6 : Word := .mul word1 word3
def word7 : Word := .mul word2 word2
def word8 : Word := .mul word2 word3
def word9 : Word := .mul word3 word3
def word10 : Word := .mul word1 word5
def word11 : Word := .mul word1 word6
def word12 : Word := .mul word1 word7
def word13 : Word := .mul word1 word8
def word14 : Word := .mul word1 word9
def word15 : Word := .mul word2 word6
def word16 : Word := .mul word2 word8
def word17 : Word := .mul word2 word9
def word18 : Word := .mul word4 word7
def word19 : Word := .mul word4 word8
def word20 : Word := .mul word4 word9
def word21 : Word := .mul word5 word8
def word22 : Word := .mul word5 word9
def word23 : Word := .mul word7 word9
def word24 : Word := .mul word1 word15
def word25 : Word := .mul word1 word16
def word26 : Word := .mul word1 word17

def column0 : Fin 27 → ℝ := ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def column1 : Fin 27 → ℝ := ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def column2 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
def column3 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]
def column4 : Fin 27 → ℝ := ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def column5 : Fin 27 → ℝ := ![0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0]
def column6 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]
def column7 : Fin 27 → ℝ := ![2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
def column8 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/2), 0, (-1/2), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/2), 0, 0, (-1/2)]
def column9 : Fin 27 → ℝ := ![2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]
def column10 : Fin 27 → ℝ := ![0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]
def column11 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]
def column12 : Fin 27 → ℝ := ![-2, 0, 2, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]
def column13 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/4), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]
def column14 : Fin 27 → ℝ := ![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]
def column15 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (1/4)]
def column16 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/4), 0, (1/4), (1/2), 0, 0, 0, (-1/4), 0, (-1/2), 0, 0, (-1/4), 0, 0, 0, (-1/2), 0, (-1/4), (1/4), 0]
def column17 : Fin 27 → ℝ := ![0, 0, 0, 2, 0, 0, (1/2), 0, (1/2), 0, 0, 0, 2, (-1/2), 0, 0, 0, 0, (1/2), 2, 0, 0, 0, 0, (1/2), (1/2), 0]
def column18 : Fin 27 → ℝ := ![2, 0, 2, 0, (1/2), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]
def column19 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]
def column20 : Fin 27 → ℝ := ![2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]
def column21 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (1/8), 0, 0, (-1/8), 0]
def column22 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 1, 0, 0, 0, 0, (-1/4), 0, 0]
def column23 : Fin 27 → ℝ := ![4, 4, 4, 0, 2, (1/2), 0, (-1/2), 0, 0, 2, 2, 0, 0, (-1/2), 0, 2, (-1/2), 0, 0, 2, -2, 0, (1/2), 0, 0, (-1/2)]
def column24 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]
def column25 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, (1/8), 0, (-1/8), (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]
def column26 : Fin 27 → ℝ := ![0, 0, 0, -1, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (1/4), (1/4), 0]

def words : Fin 27 → Word := ![word0, word1, word2, word3, word4, word5, word6, word7, word8, word9, word10, word11, word12, word13, word14, word15, word16, word17, word18, word19, word20, word21, word22, word23, word24, word25, word26]
def nativeWords (i : Fin 27) : Albert := nativeEval (words i)
def columns : Fin 27 → Fin 27 → ℝ := ![column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26]

theorem nativeWords_unit : nativeWords 0 = 1 := rfl
theorem nativeWords_markX : nativeWords 1 = witnessX := rfl
theorem nativeWords_markY : nativeWords 2 = witnessY := rfl
theorem nativeWords_markZ : nativeWords 3 = witnessZ := rfl

set_option maxHeartbeats 20000000 in
theorem nativeWords_decode (i : Fin 27) : nativeWords i = decode (columns i) := by
  fin_cases i <;> ext <;>
    norm_num [nativeWords, words, nativeEval, eval, marks,
      word0, word1, word2, word3, word4, word5, word6, word7, word8, word9,
      word10, word11, word12, word13, word14, word15, word16, word17, word18,
      word19, word20, word21, word22, word23, word24, word25, word26,
      columns, column0, column1, column2, column3, column4, column5, column6,
      column7, column8, column9, column10, column11, column12, column13, column14,
      column15, column16, column17, column18, column19, column20, column21,
      column22, column23, column24, column25, column26,
      decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom,
      witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ,
      quatK, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02,
      jordan_o12, octDot_coordinates, octMul, octConj, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, octNormSq,
      Quaternion.normSq_def', QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]

end
end Glennie.Compact.NativeWordTableR01
