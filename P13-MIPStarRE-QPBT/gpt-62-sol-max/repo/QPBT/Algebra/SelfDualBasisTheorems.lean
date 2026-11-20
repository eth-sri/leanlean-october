module

public import QPBT.Algebra.SelfDualBasis

/-! # Trace and coordinate identities for self-dual bases

Blueprint `lem:downsize_field` and `lem:one`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,730-767`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

-- The paper-facing interface fixes `Fintype ι`; its value is needed only for the matrix sum.

/-- Item 2 of blueprint `lem:downsize_field`,
paper `04_preliminaries.tex:509-550`. -/
theorem trace_mul_eq_dotProduct_basisCoord {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : Basis.IsSelfDual b) (x y : K) :
    Algebra.trace F K (x * y) = dotProduct (b.equivFun x) (b.equivFun y) := by
  have htraceMatrix :
      LinearMap.BilinForm.toMatrix b (Algebra.traceForm F K) = 1 := by
    rw [← Algebra.traceMatrix_of_basis b]
    ext i j
    simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply] using hself i j
  calc
    _ = Algebra.traceForm F K x y := rfl
    _ = b.repr x ⬝ᵥ
        (LinearMap.BilinForm.toMatrix b (Algebra.traceForm F K)) *ᵥ b.repr y :=
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b
        (Algebra.traceForm F K) x y
    _ = _ := by
      simp [htraceMatrix, Module.Basis.equivFun_apply]

-- The finite carrier is part of the fixed source-aligned interface for the binary field model.

-- The finite carrier is part of the fixed source-aligned interface for the binary field model.

/-- Canonical specialization of item 2 of blueprint
`lem:downsize_field`, paper `04_preliminaries.tex:509-550`. -/
theorem binTrace_mul_eq_dotProduct {q : ℕ} (F : FixedFieldModel q)
    (x y : F.K) :
    binTrace F.K (x * y) = dotProduct (F.binaryCoordinates x) (F.binaryCoordinates y) := by
  apply trace_mul_eq_dotProduct_basisCoord F.basis
  simpa [Basis.IsSelfDual, IsDualBasisPair] using F.selfDual

/-- Fixed-model coordinate vector for item 3 of
blueprint `lem:downsize_field`, paper
`04_preliminaries.tex:509-550`. -/
noncomputable def kappaVec {q : ℕ} {ι : Type*} (F : FixedFieldModel q)
    (v : ι → F.K) : ι × Fin F.basisDim → ZMod 2 :=
  basisCoordVec F.basis v

-- The fixed interface supplies decidable basis indices for the multiplication-table calculation.

end MIPStarRE.QPBT
