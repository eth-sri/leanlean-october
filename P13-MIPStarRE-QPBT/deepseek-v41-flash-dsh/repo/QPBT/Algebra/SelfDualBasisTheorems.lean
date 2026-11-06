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
    ext i j
    simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply] using hself i j
  calc
    Algebra.trace F K (x * y) = Algebra.traceForm F K x y := rfl
    _ = b.repr x ⬝ᵥ
        (LinearMap.BilinForm.toMatrix b (Algebra.traceForm F K)) *ᵥ b.repr y :=
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b
        (Algebra.traceForm F K) x y
    _ = dotProduct (b.equivFun x) (b.equivFun y) := by
      simp [htraceMatrix, Module.Basis.equivFun_apply]
variable {K : Type*} [Field K]


/-- The binary Frobenius automorphism preserves the field trace, as used in
`lem:one`, paper `04_preliminaries.tex:739-747`. -/
private theorem trace_sq_eq_trace  [Finite K]
    [Algebra (ZMod 2) K] (x : K) :
    Algebra.trace (ZMod 2) K (x ^ 2) = Algebra.trace (ZMod 2) K x := by
  simpa [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using
    (Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) x)

-- The finite carrier is part of the fixed source-aligned interface for the binary field model.
set_option linter.unusedFintypeInType false in
/-- The trace-one assertion of blueprint
`lem:one`, paper `04_preliminaries.tex:730-765`. -/
theorem trace_basis_eq_one_of_selfDual_normal  [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (hk : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : Basis.IsSelfDual b) (hnormal : Basis.IsNormal b) (i : Fin k) :
    Algebra.trace (ZMod 2) K (b i) = 1 := by
  obtain ⟨α, hα⟩ := hnormal
  have htrace_pow (j : ℕ) :
      Algebra.trace (ZMod 2) K (α ^ (2 ^ j)) = Algebra.trace (ZMod 2) K α := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_mul, trace_sq_eq_trace, ih]
  let c : ZMod 2 := Algebra.trace (ZMod 2) K α
  have htrace_basis (j : Fin k) : Algebra.trace (ZMod 2) K (b j) = c := by
    rw [hα j]
    simpa [ZMod.card, c] using htrace_pow j.1
  have hc : c ≠ 0 := by
    intro hc
    have htrace_zero (z : K) : Algebra.trace (ZMod 2) K z = 0 := by
      rw [← b.sum_equivFun z, map_sum]
      simp [htrace_basis, hc]
    let i₀ : Fin k := ⟨0, hk.pos⟩
    have h := hself i₀ i₀
    rw [htrace_zero] at h
    simp at h
  have hc_one : c = 1 := by
    exact Fin.eq_one_of_ne_zero c hc
  exact (htrace_basis i).trans hc_one

-- The finite carrier is part of the fixed source-aligned interface for the binary field model.
variable {q : ℕ} (F : FixedFieldModel q)


/-- Fixed-model specialization of the trace-one assertion in blueprint
`lem:one`, paper `04_preliminaries.tex:730-765`. -/
theorem fixedFieldModel_trace_basis_eq_one 
    (i : Fin F.basisDim) : Algebra.trace (ZMod 2) F.K (F.basis i) = 1 := by
  apply trace_basis_eq_one_of_selfDual_normal F.basisDimOdd F.basis
  · simpa [Basis.IsSelfDual, IsDualBasisPair] using F.selfDual
  · simpa [Basis.IsNormal, ZMod.card] using F.normal

/-- Canonical specialization of item 2 of blueprint
`lem:downsize_field`, paper `04_preliminaries.tex:509-550`. -/
theorem binTrace_mul_eq_dotProduct 
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
