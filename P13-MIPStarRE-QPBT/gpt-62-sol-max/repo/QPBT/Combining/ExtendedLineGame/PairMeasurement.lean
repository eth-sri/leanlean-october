module

public import QPBT.Combining.ExtendedLineGame.RoundedPolynomialEstimates
public import QPBT.Combining.PairCompletion

/-!
# Transport of the polynomial-pair completion

The polynomial-pair embedding is transported to the direct coefficient field.
Completing its inverse assigns every original outcome to a pair.

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
  rw [MvPolynomial.mem_restrictDegree]
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
    have hi : i = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ i 0
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
    (R : ExtendedPolyMeas P ι) (pair₀ : PolyPair P)

/-- Keep every combined outcome at its pair label and send the rest to `pair₀`. -/
def directPairMeasurement : Measurement (PolyPair P) ι :=
  R.postprocess (Function.extend (directCombinedEmbedding P) id (fun _ => pair₀))

/-- Completing the outcome labels retains each embedded effect. -/
theorem directPairMeasurement_effect_le (pair : PolyPair P) :
    R.effect (directCombinedEmbedding P pair) ≤ (directPairMeasurement R pair₀).effect pair := by
  unfold directPairMeasurement
  simpa only [(directCombinedEmbedding P).injective.extend_apply, id_eq] using
    SandwichProduct.effect_le_postprocess_effect R
      (Function.extend (directCombinedEmbedding P) id (fun _ => pair₀)) (directCombinedEmbedding P pair)

/-- Completing the outcome labels preserves projectivity. -/
theorem directPairMeasurement_projective (hR : Measurement.IsProjective R) :
    Measurement.IsProjective (directPairMeasurement R pair₀) :=
  SandwichProduct.postprocess_isProjective R hR _

end

/-- Evaluation of the actual retained outcome is the prescribed affine
combination, with the original joint sample and canonical field transport. -/
theorem directCombinedEmbedding_read (P : AdmissibleParams)
    (x : ExtendedPointQuestion P) (pair : PolyPair P) :
    extendedPolynomialRead P x (directCombinedEmbedding P pair) =
      x.2.1 * evalAt .X x.1.1 pair + x.2.2 * evalAt .Z x.1.2 pair := by
  let u := (directPointExtendedQuestionEquiv P).symm x
  have hx := directPointExtendedQuestionEquiv_apply P u
  dsimp only [ExtendedPointQuestion.ofDirect] at hx
  have heval : extendedPolynomialRead P x (directCombinedEmbedding P pair) =
      MvPolynomial.eval (directPointToPauli P u) (combinedPolyEmbedding P pair).1 := by
    let p :=
      directCombinedEmbedding P pair (0 : Fin 1)
    have hp := congrArg Subtype.val ((directPolynomialEquiv P).apply_symm_apply
      (combinedPolyEmbedding P pair))
    change MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom p.1 = _ at hp
    rw [← hp]
    change extendedDirectScalarEquiv P (MvPolynomial.eval u p.1) = _
    rw [MvPolynomial.eval_map]
    exact (MvPolynomial.eval₂_comp (extendedDirectScalarEquiv P).toRingHom u p.1).symm
  rw [heval, combinedPolyEmbedding_eval]
  have hx' :=
    ((directPointExtendedQuestionEquiv P).apply_symm_apply x).symm.trans hx
  rw [hx']

end

end MIPStarRE.QPBT.ExtendedLineGame
