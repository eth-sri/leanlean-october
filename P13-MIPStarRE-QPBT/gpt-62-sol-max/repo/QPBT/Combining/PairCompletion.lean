module

public import QPBT.Combining.Defs
public import QPBT.Games.Sandwich.Support

/-!
# The embedding of global polynomial pairs

The combining map embeds pairs of bounded individual-degree polynomials into
extended polynomials. Substitution at the two basis coefficients gives a left
inverse, and evaluation of the combined polynomial gives the affine readout.

## References

- Blueprint `lem:qld-4-7`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
  `eq:qld-sgg-completeness` and the final completion paragraph.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators MatrixOrder

noncomputable section

section

variable {K : Type*} [CommSemiring K] {m : ℕ}
include K m

/-- Recover the two polynomial components by setting the unused block to zero
and the scalar coordinates to `(1,0)` or `(0,1)`. This algebraic substitution
is the left inverse implicit in the restriction to combined outcomes in
`eq:qld-sgg-completeness`, paper lines 1375--1380. Unlike evaluation as a
polynomial function on a finite field, it does not require a degree bound. -/
noncomputable def recoverCombinedPair
    (polynomial : MvPolynomial (Fin (2 * m + 2)) K) :
    MvPolynomial (Fin m) K × MvPolynomial (Fin m) K :=
  (MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl coordinate) => MvPolynomial.X coordinate
    | .inl (.inr _) => 0
    | .inr scalar => if scalar = 0 then 1 else 0) polynomial,
   MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl _) => 0
    | .inl (.inr coordinate) => MvPolynomial.X coordinate
    | .inr scalar => if scalar = 1 then 1 else 0) polynomial)

/-- Substitution recovers both components of a combined polynomial. This is
formalization support for the relabeling in `eq:qld-sgg-completeness`, paper
lines 1375--1380. -/
@[simp] theorem recoverCombinedPair_combinePoly
    (first second : MvPolynomial (Fin m) K) :
    recoverCombinedPair (combinePoly first second) = (first, second) := by
  simp [recoverCombinedPair, combinePoly, MvPolynomial.eval₂_rename,
    embX, embZ, alphaVar, betaVar, Function.comp_def, MvPolynomial.eval₂_eta]

end

/-- Distinct polynomial pairs label distinct combined outcomes. This justifies
restricting a measurement on extended polynomials to pairs without duplicating
an effect in `eq:qld-sgg-completeness`, paper lines 1375--1380. -/
theorem combinePoly_injective {K : Type*} [CommSemiring K] {m : ℕ} :
    Function.Injective (fun pair : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly pair.1 pair.2) := by
  exact (show Function.LeftInverse recoverCombinedPair
    (fun pair : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly pair.1 pair.2) from fun pair =>
        recoverCombinedPair_combinePoly pair.1 pair.2).injective

/-- The bounded polynomial-pair embedding used to restrict the global
measurement in `eq:qld-sgg-completeness`, paper lines 1375--1380. The degree
bound is inherited from `def:combine-map`; the two scalar coordinates have
degree one, allowed by admissibility. -/
noncomputable def combinedPolyEmbedding (P : AdmissibleParams) :
    PolyPair P ↪ MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d where
  toFun pair := ⟨combinePoly pair.1.1 pair.2.1,
    combinePoly_mem_polyFunc P.hd pair.1.2 pair.2.2⟩
  inj' := by
    intro first second heq
    have hpoly : combinePoly first.1.1 first.2.1 = combinePoly second.1.1 second.2.1 :=
      congrArg Subtype.val heq
    have hpair : (first.1.1, first.2.1) = (second.1.1, second.2.1) :=
      combinePoly_injective hpoly
    grind

/-- Evaluation of a combined outcome is the affine combination of its two
components.  This is the pointwise algebraic identity used when transferring
the global-pair measurement to the expanded point measurements in
`lem:qld-4-7`, paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1364--1380`.
It is a formalization-only consequence of `def:combine-map`; it does not assert
any consistency or quantitative error estimate.
-/
theorem combinedPolyEmbedding_eval (P : AdmissibleParams)
    (u : Fin (2 * P.m + 2) → PauliScalar P) (pair : PolyPair P) :
    MvPolynomial.eval u (combinedPolyEmbedding P pair).1 =
      u (alphaVar P.m) * evalAt .X (projX u) pair +
        u (betaVar P.m) * evalAt .Z (projZ u) pair := by
  change MvPolynomial.eval u (combinePoly pair.1.1 pair.2.1) = _
  rw [combinePoly_eval]
  rfl

end

end MIPStarRE.QPBT
