module

public import QPBT.Combining.ExtendedLineGame.WrongVariableMass
public import QPBT.Combining.PairCompletion

/-!
# Transport of the polynomial-pair completion

The actual singleton outcomes are transported by the canonical field
equivalence before applying the algebraic completion.
Every original outcome is retained, including those outside the combining image.

## References

Paper `eq:qld-sgg-completeness` and the completion paragraph of `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

private theorem map_mem_polyFunc {K L : Type*} [CommSemiring K] [CommSemiring L]
    {n d : ℕ} (e : K →+* L) (p : Preliminaries.polyFunc n K d) :
    MvPolynomial.map e p.1 ∈ Preliminaries.polyFunc n L d := by
  intro s hs i
  exact (MvPolynomial.mem_restrictDegree _ _ _).mp p.2 s
    (MvPolynomial.support_map_subset e p.1 hs) i

/-- Exact singleton and coefficient-field equivalence for the actual rounded
outcomes. The degree certificates are transported through support inclusion. -/
def directPolynomialEquiv (P : AdmissibleParams) :
    DirectPolyTuple P.extendedDirectLd ≃
      Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d where
  toFun g := ⟨MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1,
    by exact map_mem_polyFunc _ _⟩
  invFun p := fun _ => ⟨MvPolynomial.map (extendedDirectScalarEquiv P).symm.toRingHom p.1,
    by exact map_mem_polyFunc _ _⟩
  left_inv g := by
    funext i
    have hi := @Subsingleton.elim (Fin 1) _ i 0
    subst i
    apply Subtype.ext
    exact (MvPolynomial.mapEquiv _ (extendedDirectScalarEquiv P)).symm_apply_apply _
  right_inv p := by
    apply Subtype.ext
    exact (MvPolynomial.mapEquiv _ (extendedDirectScalarEquiv P)).apply_symm_apply _

/-- The actual singleton outcome corresponding to a bounded polynomial pair. -/
def directCombinedEmbedding (P : AdmissibleParams) :
    PolyPair P ↪ DirectPolyTuple P.extendedDirectLd :=
  (combinedPolyEmbedding P).trans (directPolynomialEquiv P).symm.toEmbedding

section

variable {P : AdmissibleParams} {ι : Type*} [Fintype ι] [DecidableEq ι]
  (R : DirectPolyMeasTuple P.extendedDirectLd ι) (hR : Measurement.IsProjective R)
  (pair₀ : PolyPair P)

/-- Relabel the actual rounded measurement in the canonical coefficient field. -/
def canonicalPolynomialMeasurement :
    Quantum.Measurement (Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) ι :=
  R.postprocess (directPolynomialEquiv P)

/-- The canonical relabeling retains each original effect exactly. -/
@[simp] theorem canonicalPolynomialMeasurement_effect
    (p : Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) :
    (canonicalPolynomialMeasurement R).effect p =
      R.effect ((directPolynomialEquiv P).symm p) := by
  simpa only [canonicalPolynomialMeasurement, Equiv.apply_symm_apply] using (SandwichProduct.postprocess_effect_of_injective R _
    (directPolynomialEquiv P).injective ((directPolynomialEquiv P).symm p))

/-- The complete projective pair construction applied to the actual
rounded measurement, including all excluded outcomes at one chosen pair. -/
def directPairMeasurement : Quantum.Measurement (PolyPair P) ι :=
  completedPairMeasurement P (canonicalPolynomialMeasurement R) pair₀

include hR in
/-- Projectivity follows from completion and injective field transport. -/
theorem directPairMeasurement_projective :
    Measurement.IsProjective (directPairMeasurement R pair₀) :=
  (SandwichProduct.postprocess_isProjective _ (SandwichProduct.postprocess_isProjective R hR _) _)

end

/-- Evaluation of the actual retained outcome is the prescribed affine
combination, with the original joint sample and canonical field transport. -/
theorem directCombinedEmbedding_read (P : AdmissibleParams)
    (x : ExtendedPointQuestion P) (pair : PolyPair P) :
    extendedPolynomialRead x (directCombinedEmbedding P pair) =
      x.2.1 * evalAt .X x.1.1 pair + x.2.2 * evalAt .Z x.1.2 pair := by
  let u := (directPointExtendedQuestionEquiv P).symm x
  have heval : extendedPolynomialRead x (directCombinedEmbedding P pair) =
      MvPolynomial.eval (directPointToPauli u) (combinedPolyEmbedding P pair).1 := by
    let p :=
      directCombinedEmbedding P pair 0
    have hp := congrArg Subtype.val ((directPolynomialEquiv P).apply_symm_apply
      (combinedPolyEmbedding P pair))
    change MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom p.1 = _ at hp
    rw [← hp]
    simp
    exact (MvPolynomial.eval₂_comp (extendedDirectScalarEquiv P).toRingHom u p.1).symm
  rw [heval, combinedPolyEmbedding_eval]
  have hx' :=
    ((directPointExtendedQuestionEquiv P).apply_symm_apply x).symm.trans (directPointExtendedQuestionEquiv_apply P u)
  rw [hx']

end

end MIPStarRE.QPBT.ExtendedLineGame
