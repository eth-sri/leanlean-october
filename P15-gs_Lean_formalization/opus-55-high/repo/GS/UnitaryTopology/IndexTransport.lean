module

public import GS.UnitaryTopology.QuaternionRetraction
public import GS.NonmanifoldFinal.EuclideanTransport

@[expose] public section


/-!
# Column reindexing of the actual three-row rank cone

The maps preserve mathlib's matrix rank and the inherited matrix topology.
They allow a four-column-block Clifford construction to be stated at an
ordinary scalar matrix width.
-/
noncomputable section
namespace GS.UnitaryTopology

variable {κ ν : Type*} [Fintype κ] [Fintype ν]

section
variable (e : ℕ) (f : κ ≃ ν)
def productRankThreeReindex :
    ((Fin e → ℝ) × RankThreeCone κ) ≃ₜ ((Fin e → ℝ) × RankThreeCone ν) :=
  (Homeomorph.refl _).prodCongr
    { toFun W := ⟨W.val.reindex (Equiv.refl _) f, by simpa only [Matrix.rank_reindex] using W.property⟩
      invFun W := ⟨W.val.reindex (Equiv.refl _) f.symm, by simpa only [Matrix.rank_reindex] using W.property⟩
      left_inv W := by simp
      right_inv W := by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

@[simp] theorem productRankThreeReindex_zero :
    productRankThreeReindex e f (0,rankThreeZero) = (0,rankThreeZero) :=
  rfl

end

end GS.UnitaryTopology
