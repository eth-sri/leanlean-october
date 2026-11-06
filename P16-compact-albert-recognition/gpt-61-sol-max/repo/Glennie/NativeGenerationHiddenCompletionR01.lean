/- Hidden completion from complex-sector membership and an invertible hidden matrix. -/
module
public import Glennie.NativeGenerationHiddenSpanR01

@[expose] public section
namespace Glennie.NativeGenerationHiddenCompletionR01
section
open Glennie.NativeGenerationCoordinatesR01
open Glennie.NativeGenerationPeirceTriangleR01
open Glennie.NativeGenerationHiddenActionsR01
open Glennie.NativeGenerationHiddenSpanR01



theorem hiddenOct_hiddenMatrix (z : Albert) (j : Fin 3) :
    hiddenOct (fun i => hiddenMatrix z i j) =
      ![-residual z.o12, residual z.o02, -residual z.o01] j := by
  fin_cases j <;> apply Prod.ext <;> apply Quaternion.ext <;>
    simp [hiddenOct, hiddenMatrix, hiddenColumn, NativeGenerationHiddenActionsR01.residual, complexOct, complexPart]

theorem raw_decomposition (z : Albert) :
    z = z.d0 • diagonalAlbert 1 0 0 + z.d1 • diagonalAlbert 0 1 0 +
      z.d2 • diagonalAlbert 0 0 1 + E01 z.o01 + E02 z.o02 + E12 z.o12 := by
  ext <;> simp [diagonalAlbert, E01, E02, E12]

/-- The missing hidden propagation bridge, reduced to explicit coordinate
operations and ordinary complex nonsingular matrix inversion. -/
theorem eq_top_of_complexSector_le_hidden_det
    (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (hC : complexSector ≤ K)
    (z : Albert) (hz : z ∈ K) (hdet : (hiddenMatrix z).det ≠ 0) : K = ⊤ := by
  have he0                            := complexAlbert_mem K hC 1 0 0 0 0 0
  have he1                            := complexAlbert_mem K hC 0 1 0 0 0 0
  have he2                            := complexAlbert_mem K hC 0 0 1 0 0 0
  have hz01                 := peirce01_mem K hJ he0 he1 z hz
  have hz02                 := peirce02_mem K hJ he0 he2 z hz
  have hz12                 := peirce12_mem K hJ he1 he2 z hz
  have hw : ∀ j : Fin 3, E02 (hiddenOct (fun i => hiddenMatrix z i j)) ∈ K := by
    intro j
    fin_cases j
    · simpa [hiddenOct_hiddenMatrix] using
        K.neg_mem (transfer12_to02_mem K hJ hC _ (residual_slot12_mem K hC _ hz12))
    · simpa [hiddenOct_hiddenMatrix] using residual_slot02_mem K hC _ hz02
    · simpa [hiddenOct_hiddenMatrix] using
        K.neg_mem (transfer01_to02_mem K hJ hC _ (residual_slot01_mem K hC _ hz01))
  have hi : ∀ j : Fin 3, E02 (octMul (complexOct Complex.I)
      (hiddenOct (fun i => hiddenMatrix z i j))) ∈ K :=
    fun j => common02_left_i_mem K hJ hC _ (hw j)
  have hall02 : ∀ q : Octonion, E02 q ∈ K := by
    intro q
    rw [← oct_complex_hidden_decomposition q, map_add]
    exact K.add_mem (complex_slot02_mem K hC _) (hidden_slot02_mem_of_columns K
      (hiddenMatrix z) hdet hw hi (hiddenColumn q))
  have hall01 : ∀ q : Octonion, E01 q ∈ K := by
    intro q
    have he := cross02_12 q (octScalar 1)
    simp only [octConj_scalar, octMul_scalar_right, one_smul] at he
    rw [← he]
    exact K.smul_mem 2 (hJ _ (hall02 q) _
      (complex_slot12_mem K hC 1))
  have hall12 : ∀ q : Octonion, E12 q ∈ K := by
    intro q
    have he := cross01_02 (octScalar 1) q
    simp only [octConj_scalar, octMul_scalar_left, one_smul] at he
    rw [← he]
    exact K.smul_mem 2 (hJ _
      (complex_slot01_mem K hC 1) _ (hall02 q))
  apply top_unique
  intro t ht
  rw [raw_decomposition t]
  aesop


end
end Glennie.NativeGenerationHiddenCompletionR01
