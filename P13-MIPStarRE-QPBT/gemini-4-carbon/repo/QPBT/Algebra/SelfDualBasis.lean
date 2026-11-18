module

public import QPBT.Algebra.FieldBasis

/-! # Binary coordinates for the fixed self-dual normal basis

The basis definitions and existence theorem live in the upstream
`FieldBasis` module; this file develops their coordinate consequences.

## References

- Blueprint `def:dual-self-dual-normal-basis` and
  `def:binary-representation`.
- `references/qpbt-paper/04_preliminaries.tex:494-502,669-700`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators Matrix

/-- Coordinates in the fixed model's chosen binary basis;
blueprint `def:binary-representation`, paper
`04_preliminaries.tex:669-700`. -/
noncomputable abbrev FixedFieldModel.binaryCoordinates {q : ℕ}
    (F : FixedFieldModel q) : F.K ≃ₗ[ZMod 2] (Fin F.basisDim → ZMod 2) :=
  kappa F.basis

/-- Matrix coordinate expansion for an arbitrary basis. This is the `chi_q`
construction of blueprint `def:subfields-kappa`,
paper `04_preliminaries.tex:462-475`; it is used in item 3 of blueprint
`lem:downsize_field`, paper lines 509-550. -/
noncomputable def chiOfBasis {F K ρ κ σ : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype κ] (b : Module.Basis κ F K) (M : Matrix ρ σ K) :
    Matrix (ρ × κ) (σ × κ) F :=
  fun p r => b.equivFun (M p.1 r.1 * b r.2) p.2

/-- Coordinates of a vector, block-indexed by its vector and basis indices.
This is the vector `kappa_q(v)` of blueprint
`def:subfields-kappa`, paper `04_preliminaries.tex:462-475`; it is used
in item 3 of blueprint `lem:downsize_field`, paper lines 509-550. -/
noncomputable def basisCoordVec {F K ι κ : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype κ] (b : Module.Basis κ F K) (v : ι → K) : ι × κ → F :=
  fun p => b.equivFun (v p.1) p.2

end MIPStarRE.QPBT
