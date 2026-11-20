module

public import QPBT.Combining.ExtendedLineGame.RoundedPolynomialEstimates
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Scalar and base coefficients of the rounded polynomial outcomes

The singleton polynomial is transported through the canonical field equivalence
and Mathlib's equivalence between a polynomial in a sum of variables and an
iterated polynomial ring. Its individual-degree certificate controls both levels.
Splitting each base coefficient by either block gives the partial degrees used
in the fiber calculation. Independence of both wrong blocks identifies the
outcome with the existing bounded polynomial-pair combining map.

## References

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1310-1326`,
the coefficient expansion preceding `eq:qld-g-prime-bound`.
The partial coefficient argument and separated image are at lines 1341--1368,
`eq:qld-g-2` and `eq:qld-g-non-separable`; blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ExtendedLineGame

private theorem coeff_coeff_sumRingEquiv {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial (A ⊕ B) F) (a : A →₀ ℕ) (b : B →₀ ℕ) :
    ((MvPolynomial.sumRingEquiv F A B p).coeff a).coeff b =
      p.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b)) := by
  simp [MvPolynomial.sumRingEquiv,
    AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]

section

variable {F : Type*} [CommSemiring F]

private theorem totalDegree_le_of_exponents
    {n d : ℕ} (p : MvPolynomial (Fin n) F)
    (h : ∀ e ∈ p.support, ∀ i, e i ≤ d) : p.totalDegree ≤ n * d := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro e he
  simp [Finsupp.sum_fintype]
  refine LE.le.trans_eq (Finset.sum_le_sum fun i _ => h e he i) ?_
  simp

private theorem sumRingEquiv_degrees {k n d : ℕ}
    {p : MvPolynomial (Fin k ⊕ Fin n) F}
    (h : ∀ e ∈ p.support, ∀ i, e i ≤ d) :
    (∀ a, ((MvPolynomial.sumRingEquiv F (Fin k) (Fin n) p).coeff a).totalDegree ≤
      n * d) ∧ (MvPolynomial.sumRingEquiv F (Fin k) (Fin n) p).totalDegree ≤ k * d := by
  have hc (a : Fin k →₀ ℕ) (b : Fin n →₀ ℕ)
      (hb : b ∈ ((MvPolynomial.sumRingEquiv F _ _ p).coeff a).support) :
      Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b) ∈ p.support := by
    simpa only [MvPolynomial.mem_support_iff, coeff_coeff_sumRingEquiv] using hb
  constructor
  · intro a
    apply totalDegree_le_of_exponents
    intro b hb i
    simpa using h _ (hc a b hb) (Sum.inr i)
  · apply totalDegree_le_of_exponents
    intro a ha i
    obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr
      (MvPolynomial.mem_support_iff.mp ha)
    simpa using h _ (hc a b hb) (Sum.inl i)

end

/-- The two base blocks, in the order `x,z` used by the extended game. -/
def baseCoordinateEquiv (m : ℕ) : Fin (2 * m) ≃ Fin m ⊕ Fin m :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

/-- The scalar coordinates first, followed by the combined base coordinates. -/
def scalarBaseCoordinateEquiv (m : ℕ) : Fin (2 * m + 2) ≃ Fin 2 ⊕ Fin (2 * m) :=
  (finCombineEquiv m).trans
    ((Equiv.sumCongr (baseCoordinateEquiv m).symm (Equiv.refl _)).trans
      (Equiv.sumComm _ _))

section

variable (P : AdmissibleParams) (g : DirectPolyTuple P.extendedDirectLd)

variable {P} in
/-- The actual singleton outcome as a polynomial in `alpha,beta` with
coefficients in the `2m` base variables, over the canonical Pauli field. -/
def scalarPolynomial :
    MvPolynomial (Fin 2) (MvPolynomial (Fin (2 * P.m)) (PauliScalar P)) :=
  MvPolynomial.sumRingEquiv _ _ _
    (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1))

private theorem scalarPolynomial_renamed_exponents :
    ∀ e ∈ (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m)
      (MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1)).support,
      ∀ i, e i ≤ P.d := by
  intro e he i
  obtain ⟨v, hv, hvp⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _
    (MvPolynomial.mem_support_iff.mp he)
  have hvbound := (MvPolynomial.le_degreeOf_of_mem_support _ (MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr hvp))).trans (Preliminaries.degreeOf_le_of_mem_polyFunc (g 0).2
    ((scalarBaseCoordinateEquiv P.m).symm i))
  subst e
  simpa using hvbound

/-- Both degree bounds follow from the genuine individual-degree certificate:
every base coefficient has degree at most `2md`, and the outer scalar
polynomial has degree at most `2d`. No degree hypothesis is added. -/
theorem scalarPolynomial_degrees :
    (∀ a, ((scalarPolynomial g).coeff a).totalDegree ≤ 2 * P.m * P.d) ∧
      (scalarPolynomial g).totalDegree ≤ 2 * P.d := sumRingEquiv_degrees (scalarPolynomial_renamed_exponents P g)

section

variable (a : Fin 2 →₀ ℕ) (reverse : Bool)

variable {P} in
/-- Split a base coefficient into a polynomial in either varying block with
coefficients in the fixed block. The order parameter selects either `x` or `z`
as the varying block. This supports the two applications of `eq:qld-g-2` in
paper lines 1341--1358 and blueprint `lem:qld-4-7`. -/
def blockCoefficientPolynomial :
    MvPolynomial (Fin P.m) (MvPolynomial (Fin P.m) (PauliScalar P)) :=
  MvPolynomial.sumRingEquiv _ _ _ (MvPolynomial.rename
    ((baseCoordinateEquiv P.m).trans
      (if reverse then Equiv.sumComm _ _ else Equiv.refl _)) ((scalarPolynomial g).coeff a))

private theorem blockCoefficientPolynomial_renamed_exponents :
    ∀ e ∈ (MvPolynomial.rename ((baseCoordinateEquiv P.m).trans
      (if reverse then Equiv.sumComm _ _ else Equiv.refl _))
        ((scalarPolynomial g).coeff a)).support, ∀ i, e i ≤ P.d := by
  intro e he i
  let eqv := (baseCoordinateEquiv P.m).trans
    (if reverse then Equiv.sumComm _ _ else Equiv.refl _)
  obtain ⟨v, hv, hvp⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _
    (MvPolynomial.mem_support_iff.mp he)
  have hb := scalarPolynomial_renamed_exponents P g _
    (MvPolynomial.mem_support_iff.mpr (by simpa only [scalarPolynomial, coeff_coeff_sumRingEquiv] using hvp)) (.inr (eqv.symm i))
  change v _ ≤ P.d at hb
  subst e
  simpa only [Finsupp.mapDomain_equiv_apply] using hb

/-- Both partial degrees are at most `md`, for either choice of varying
block, directly from the actual outcome's individual-degree certificate.
This supplies the coefficient and fiber bounds in `eq:qld-g-2`, supporting
blueprint `lem:qld-4-7`; no degree or specialization premise is added. -/
theorem blockCoefficientPolynomial_degrees :
    (∀ e, ((blockCoefficientPolynomial g a reverse).coeff e).totalDegree ≤ P.m * P.d) ∧
      (blockCoefficientPolynomial g a reverse).totalDegree ≤ P.m * P.d := sumRingEquiv_degrees (blockCoefficientPolynomial_renamed_exponents P g a reverse)

end

end

private theorem eval_sumRingEquiv {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial (A ⊕ B) F) (u : B → F) (v : A → F) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u)
      (MvPolynomial.sumRingEquiv F A B p)) = MvPolynomial.eval (Sum.elim v u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp_all
  | mul_X p i hp => cases i <;> simp [hp]

section

variable (P : AdmissibleParams)

/-- Split the full joint uniform point into the base point and scalar point.
This is one equivalence of sample spaces, not four marginal identifications. -/
def scalarBaseQuestionEquiv :
    ((Fin (2 * P.m) → PauliScalar P) × (Fin 2 → PauliScalar P)) ≃
      ExtendedPointQuestion P :=
  (((baseCoordinateEquiv P.m).piCongrLeft fun _ => PauliScalar P).trans
    (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m => PauliScalar P)).prodCongr
      (finTwoArrowEquiv (PauliScalar P))

private theorem scalarBaseQuestionEquiv_direct
    (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) :
    (directPointExtendedQuestionEquiv P).symm (scalarBaseQuestionEquiv P (u, v)) =
      fun i => (extendedDirectScalarEquiv P).symm
        (Sum.elim v u (scalarBaseCoordinateEquiv P.m i)) := by
  apply (directPointExtendedQuestionEquiv P).injective
  simp [directPointExtendedQuestionEquiv_apply]
  apply Prod.ext
  · ext <;> simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, projX, projZ, embX, embZ, directPointToPauli, Equiv.piCongrLeft_apply]
  · simp [scalarBaseQuestionEquiv, scalarBaseCoordinateEquiv, alphaVar, betaVar, directPointToPauli]

/-- Evaluation of the nested polynomial is exactly the actual singleton readout,
including the canonical field transport and all four coordinate blocks. -/
theorem scalarPolynomial_eval
    (g : DirectPolyTuple P.extendedDirectLd)
    (u : Fin (2 * P.m) → PauliScalar P) (v : Fin 2 → PauliScalar P) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (scalarPolynomial g)) =
      extendedPolynomialRead (scalarBaseQuestionEquiv P (u, v)) g := by
  rw [scalarPolynomial, eval_sumRingEquiv, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  unfold extendedPolynomialRead evalDirectPolyTupleAt
  rw [scalarBaseQuestionEquiv_direct]
  have h := (MvPolynomial.eval₂_comp (extendedDirectScalarEquiv P).toRingHom
      (fun i => (extendedDirectScalarEquiv P).symm
        (Sum.elim v u (scalarBaseCoordinateEquiv P.m i))) (g 0).1).symm
  exact h

/-- Joint sample equivalence for the fiber calculation: the first input block
is fixed and the second varies. Reversal exchanges both the point blocks and
the scalar coefficients, so its ordered product is `ZX`. This supports the
two orders in `eq:qld-g-42/43` and blueprint `lem:qld-4-7`. -/
def fiberQuestionEquiv (reverse : Bool) :
    (((PauliPoint P) × (PauliPoint P)) ×
      (Fin 2 → PauliScalar P)) ≃ ExtendedPointQuestion P :=
  (if reverse then Equiv.refl _ else Equiv.prodComm _ _).prodCongr
    ((finTwoArrowEquiv (PauliScalar P)).trans
      (if reverse then Equiv.prodComm _ _ else Equiv.refl _))

/-- For a scalar-linear outcome, its actual readout equals the two specialized
coefficient polynomials in the corresponding block and scalar order. This is
an exact identity, with no field-size condition; support for `eq:qld-g-48`
and blueprint `lem:qld-4-7`. -/
theorem scalarPolynomial_linear_read_fiber
    (g : DirectPolyTuple P.extendedDirectLd)
    (hg : ∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1)
    (reverse : Bool) (x z : PauliPoint P) (v : Fin 2 → PauliScalar P) :
    extendedPolynomialRead (fiberQuestionEquiv P reverse ((z, x), v)) g =
      v 0 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
        (blockCoefficientPolynomial g (Finsupp.single (if reverse then 1 else 0) 1)
          reverse)) +
      v 1 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
        (blockCoefficientPolynomial g (Finsupp.single (if reverse then 0 else 1) 1)
          reverse)) := by
  obtain ⟨r, t, hg⟩ := hg
  let u : _ → PauliScalar P := fun i => Sum.elim x z
    (((baseCoordinateEquiv P.m).trans
      (if reverse then Equiv.sumComm _ _ else Equiv.refl _)) i)
  let v' := if reverse then ![v 1, v 0] else v
  have heq : scalarBaseQuestionEquiv P (u, v') =
      fiberQuestionEquiv P reverse ((z, x), v) := by
    cases reverse <;> simp [scalarBaseQuestionEquiv, fiberQuestionEquiv, u, v',
      Equiv.piCongrLeft_apply]
  rw [← heq, ← scalarPolynomial_eval, hg]
  simp_rw [blockCoefficientPolynomial, eval_sumRingEquiv, MvPolynomial.eval_rename, hg]
  have h01 : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
    intro h
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp only [map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  cases reverse <;>
    simp only [Bool.false_eq_true, MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h01, Ne.symm h01,
      ↓reduceIte, mul_one, mul_zero, zero_add, add_zero]
  · change MvPolynomial.eval u r * v 0 + MvPolynomial.eval u t * v 1 =
      v 0 * MvPolynomial.eval u r + v 1 * MvPolynomial.eval u t
    ring
  · change MvPolynomial.eval u r * v 1 + MvPolynomial.eval u t * v 0 =
      v 0 * MvPolynomial.eval u t + v 1 * MvPolynomial.eval u r
    ring

end

private theorem sumRingEquiv_rename_inr {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial B F) :
    MvPolynomial.sumRingEquiv F A B (MvPolynomial.rename Sum.inr p) =
      MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp_all
  | mul_X p i hp => simp [hp]

private theorem blockCoefficientPolynomial_const {P : AdmissibleParams}
    {g : DirectPolyTuple P.extendedDirectLd} {a : Fin 2 →₀ ℕ} {reverse : Bool}
    (h : ∃ r, blockCoefficientPolynomial g a reverse = MvPolynomial.C r) :
    ∃ r : Poly P, (scalarPolynomial g).coeff a = MvPolynomial.rename
      (fun i => ((baseCoordinateEquiv P.m).trans
        (if reverse then Equiv.sumComm _ _ else Equiv.refl _)).symm (.inr i)) r.1 := by
  obtain ⟨r, hr⟩ := h
  have hmem : r ∈ Preliminaries.polyFunc P.m (PauliScalar P) P.d := by
    apply mem_polyFunc_of_degreeOf_le
    intro i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro b hb
    have hcoeff :
        ((blockCoefficientPolynomial g a reverse).coeff 0).coeff b ≠ 0 := by
      simpa [hr, MvPolynomial.coeff_C] using MvPolynomial.mem_support_iff.mp hb
    have hsupport : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (0, b) ∈
        (MvPolynomial.rename ((baseCoordinateEquiv P.m).trans
          (if reverse then Equiv.sumComm _ _ else Equiv.refl _))
            ((scalarPolynomial g).coeff a)).support := by
      simpa only [blockCoefficientPolynomial, coeff_coeff_sumRingEquiv,
        MvPolynomial.mem_support_iff] using hcoeff
    simpa using blockCoefficientPolynomial_renamed_exponents P g a reverse _ hsupport (.inr i)
  refine ⟨⟨r, hmem⟩, ?_⟩
  let eqv := (baseCoordinateEquiv P.m).trans
    (if reverse then Equiv.sumComm _ _ else Equiv.refl _)
  apply MvPolynomial.rename_injective eqv eqv.injective
  apply (MvPolynomial.sumRingEquiv (PauliScalar P) (Fin P.m) (Fin P.m)).injective
  change blockCoefficientPolynomial g a reverse = _
  rw [hr, MvPolynomial.rename_rename]
  have heq : eqv ∘ (fun i => eqv.symm (.inr i)) = Sum.inr := by
    funext i
    exact eqv.apply_symm_apply _
  rw [heq, sumRingEquiv_rename_inr]

private theorem scalarExpansion_combinePoly (P : AdmissibleParams)
    (f h : MvPolynomial (Fin P.m) (PauliScalar P)) :
    MvPolynomial.sumRingEquiv _ _ _
      (MvPolynomial.rename (scalarBaseCoordinateEquiv P.m) (combinePoly f h)) =
    MvPolynomial.C (MvPolynomial.rename
      (fun i => (baseCoordinateEquiv P.m).symm (.inl i)) f) * MvPolynomial.X (0 : Fin 2) +
    MvPolynomial.C (MvPolynomial.rename
      (fun i => (baseCoordinateEquiv P.m).symm (.inr i)) h) * MvPolynomial.X 1 := by
  have hX : scalarBaseCoordinateEquiv P.m ∘ embX P.m =
      Sum.inr ∘ (fun i => (baseCoordinateEquiv P.m).symm (.inl i)) := by
    funext i
    simp [scalarBaseCoordinateEquiv, embX]
  have hZ : scalarBaseCoordinateEquiv P.m ∘ embZ P.m =
      Sum.inr ∘ (fun i => (baseCoordinateEquiv P.m).symm (.inr i)) := by
    funext i
    simp [scalarBaseCoordinateEquiv, embZ]
  simp [combinePoly, MvPolynomial.rename_X, MvPolynomial.rename_rename, hX, hZ]
  simp [← MvPolynomial.rename_rename]
  simp only [sumRingEquiv_rename_inr]
  have ha : scalarBaseCoordinateEquiv P.m (alphaVar P.m) = .inl 0 := by
    simp [scalarBaseCoordinateEquiv, alphaVar]
  have hb : scalarBaseCoordinateEquiv P.m (betaVar P.m) = .inl 1 := by
    simp [scalarBaseCoordinateEquiv, betaVar]
  simp_all
  ring

/-- Scalar-linearity and independence of both wrong blocks place the actual
outcome in the existing bounded `combinePoly` image. The two components have
individual degree at most `d`, not merely total degree at most `md`.
This identifies the separated image in `eq:qld-g-non-separable` with
`def:combine-map`, supporting blueprint `lem:qld-4-7`. -/
theorem exists_polyPair_of_scalar_separated (P : AdmissibleParams)
    (g : DirectPolyTuple P.extendedDirectLd)
    (hlin : ∃ r t : MvPolynomial (Fin (2 * P.m)) (PauliScalar P),
      scalarPolynomial g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1)
    (hX : ∃ r, blockCoefficientPolynomial g (Finsupp.single 0 1) true = MvPolynomial.C r)
    (hZ : ∃ r, blockCoefficientPolynomial g (Finsupp.single 1 1) false = MvPolynomial.C r) :
    ∃ pair : PolyPair P,
      MvPolynomial.map (extendedDirectScalarEquiv P).toRingHom (g (0 : Fin 1)).1 =
        combinePoly pair.1.1 pair.2.1 := by
  obtain ⟨f, hf⟩ := blockCoefficientPolynomial_const hX
  obtain ⟨h, hh⟩ := blockCoefficientPolynomial_const hZ
  refine ⟨(f, h), ?_⟩
  apply MvPolynomial.rename_injective (scalarBaseCoordinateEquiv P.m)
    (scalarBaseCoordinateEquiv P.m).injective
  apply (MvPolynomial.sumRingEquiv (PauliScalar P) (Fin 2) (Fin (2 * P.m))).injective
  change scalarPolynomial g = _
  rw [scalarExpansion_combinePoly]
  obtain ⟨r, t, hlin⟩ := hlin
  have h01 : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
    intro h
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp_all

end ExtendedLineGame

end

end MIPStarRE.QPBT
