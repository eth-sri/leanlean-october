/- Finite-coordinate representation for the native word table. -/
module
public import Glennie.Compact.NativeWordCoordinateBridgeR01

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open AlbertGeometry.NativeOperatorTrace
open scoped BigOperators

syntax "dtac" Lean.Parser.Tactic.simpArgs : tactic
macro_rules | `(tactic| dtac [$xs,*]) => `(tactic| ext <;> norm_num [decode, fullCoordinates_symm_apply, fullFrom, unflatten, octFrom, witnessX, witnessY, witnessZ, unit, octI, octK, octL, octJL, quatI, quatJ, quatK, oct_simps, $xs,*])


open Lean in
macro "wentry " n:num a:num b:num c:term : command => do
  let i (p s : String) (k : TSyntax `num) := mkIdent (.mkSimple s!"{p}{k.getNat}{s}")
  `(def $(i "word" "" n) : Word := .mul $(i "word" "" a) $(i "word" "" b)
    def $(i "value" "" n) : Albert := nativeEval $(i "word" "" n)
    def $(i "column" "" n) : Fin 27 → ℝ := $c
    set_option maxHeartbeats 2000000 in
    theorem $(i "value" "_decode" n) : $(i "value" "" n) = decode $(i "column" "" n) := by
      change jordan $(i "value" "" a) $(i "value" "" b) = decode $(i "column" "" n)
      simp [$(i "value" "_decode" a):term, $(i "value" "_decode" b):term]
      dtac [$(i "column" "" n):term, $(i "column" "" a):term, $(i "column" "" b):term])


def word0 : Word := .unit
def column0 : Fin 27 → ℝ := ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def word1 : Word := .mark 0
def value1 : Albert := nativeEval word1
def column1 : Fin 27 → ℝ := ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem value1_decode : value1 = decode column1 := by rfl

def word2 : Word := .mark 1
def value2 : Albert := nativeEval word2
def column2 : Fin 27 → ℝ := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

theorem value2_decode : value2 = decode column2 := by rfl

def word3 : Word := .mark 2
def value3 : Albert := nativeEval word3
def column3 : Fin 27 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0]

theorem value3_decode : value3 = decode column3 := by
  change witnessZ = decode column3
  dtac [column3]

wentry 4 1 1 ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

wentry 5 1 2 ![0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0, 0]

wentry 6 1 3 ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0]

wentry 7 2 2 ![2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

wentry 8 2 3 ![0, 0, 0, 0, 0, (-1/2), 0, (-1/2), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/2), 0, 0, (-1/2)]

wentry 9 3 3 ![2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]

wentry 10 1 5 ![0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0]

wentry 11 1 6 ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0]

wentry 12 1 7 ![-2, 0, 2, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

wentry 13 1 8 ![0, 0, 0, 0, 0, (1/4), 0, (1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

wentry 14 1 9 ![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

wentry 15 2 6 ![0, 0, 0, 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, (1/4)]

wentry 16 2 8 ![0, 0, 0, 0, 0, 0, (-1/4), 0, (1/4), (1/2), 0, 0, 0, (-1/4), 0, (-1/2), 0, 0, (-1/4), 0, 0, 0, (-1/2), 0, (-1/4), (1/4), 0]

wentry 17 2 9 ![0, 0, 0, 2, 0, 0, (1/2), 0, (1/2), 0, 0, 0, 2, (-1/2), 0, 0, 0, 0, (1/2), 2, 0, 0, 0, 0, (1/2), (1/2), 0]

wentry 18 4 7 ![2, 0, 2, 0, (1/2), 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 0]

wentry 19 4 8 ![0, 0, 0, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, (-1/2), 0, 0, (1/2), 0, 0, 0, 0, 0, (-1/4), 0, 0, (-1/4)]

wentry 20 4 9 ![2, 0, 2, 0, 0, 0, 0, 0, 0, 0, (1/2), 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (-1/2), 0, 0, 0, 0, 0]

wentry 21 5 8 ![0, 0, 0, 0, 0, 0, (-1/8), 0, 0, (1/8), 0, 0, 0, (-1/8), 0, 0, 0, 0, (1/8), 0, 0, 0, (1/8), 0, 0, (-1/8), 0]

wentry 22 5 9 ![0, 0, 0, -1, 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 0, 0, 0, 0, (1/4), 1, 0, 0, 0, 0, (-1/4), 0, 0]

wentry 23 7 9 ![4, 4, 4, 0, 2, (1/2), 0, (-1/2), 0, 0, 2, 2, 0, 0, (-1/2), 0, 2, (-1/2), 0, 0, 2, -2, 0, (1/2), 0, 0, (-1/2)]

wentry 24 1 15 ![0, 0, 0, 0, 0, (1/8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1/8)]

wentry 25 1 16 ![0, 0, 0, 0, 0, 0, (1/8), 0, (-1/8), (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1/4), 0, (-1/8), (1/8), 0]

wentry 26 1 17 ![0, 0, 0, -1, 0, 0, (-1/4), 0, (-1/4), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, (1/4), (1/4), 0]

def words : Fin 27 → Word := ![word0, word1, word2, word3, word4, word5, word6, word7, word8, word9, word10, word11, word12, word13, word14, word15, word16, word17, word18, word19, word20, word21, word22, word23, word24, word25, word26]
def nativeWords (i : Fin 27) : Albert := nativeEval (words i)
def columns : Fin 27 → Fin 27 → ℝ := ![column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10, column11, column12, column13, column14, column15, column16, column17, column18, column19, column20, column21, column22, column23, column24, column25, column26]

theorem nativeWords_unit : nativeWords 0 = 1 := rfl
theorem nativeWords_markX : nativeWords 1 = witnessX := rfl
theorem nativeWords_markY : nativeWords 2 = witnessY := rfl
theorem nativeWords_markZ : nativeWords 3 = witnessZ := rfl

theorem nativeWords_decode (i : Fin 27) : nativeWords i = decode (columns i) := by
  fin_cases i
  iterate 3 rfl
  exacts [value3_decode, value4_decode, value5_decode, value6_decode, value7_decode, value8_decode, value9_decode, value10_decode, value11_decode, value12_decode, value13_decode, value14_decode, value15_decode, value16_decode, value17_decode, value18_decode, value19_decode, value20_decode, value21_decode, value22_decode, value23_decode, value24_decode, value25_decode, value26_decode]
end
end Glennie.Compact.NativeWordTableR01
