import GS.MatrixGeometry.BlockGroup
import GS.Unitary.Support
namespace GS.UnitaryManifold
abbrev BlockU {n : ℕ} (block : Fin n → ℕ) := GS.MatrixBase.BlockU ℂ block
export GS.MatrixBase (continuous_matrix_product continuous_matrix_conjTranspose
  closed_supported closed_unitary compact_blockU_set)
@[simp] theorem blockU_one_val {n : ℕ} (block : Fin n → ℕ) :
    ((1 : BlockU block) : GS.CMat n) = 1 := rfl
end GS.UnitaryManifold
