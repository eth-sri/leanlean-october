module

public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.Test.PauliBasisTest

/-!
# Polynomial combination and restricted line distributions

This file contains the concrete definitions at the foundation of the
Chapter 15 combining argument.  A pair of bounded individual-degree
polynomials is embedded into the two coordinate blocks of an extended
polynomial.  On lines, explicit affine reparameterizations are composed with
coefficient-list polynomials.  The original-dimensional restricted line laws
are formed before decoding, while their field seed is still present.

## References

The combining map is blueprint
`def:combine-map`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The restricted laws are blueprint `def:ith-restricted-line`,
with paper origin in the same source at lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- The bounded individual-degree polynomial outcome used by the global
pair measurement.  This is the actual `polyFunc` subtype from
`def:polyfunc`, not a coefficient-box replacement. -/
noncomputable abbrev Poly (P : AdmissibleParams) :=
  ↥(MIPStarRE.LDT.Preliminaries.polyFunc P.m (PauliScalar P) P.d)

/-- Pairs of bounded polynomial representatives returned by the global
measurement in `lem:qld-4-7`. -/
noncomputable abbrev PolyPair (P : AdmissibleParams) := Poly P × Poly P

section

variable (m : ℕ)
include m

/-- This equivalence decomposes the extended coordinate set into the `X` block,
    the `Z` block, and the two scalar coordinates.  It supports blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
def finCombineEquiv :
    Fin (2 * m + 2) ≃ ((Fin m ⊕ Fin m) ⊕ Fin 2) :=
  (finCongr (by omega)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin 2))))

/-- Embed an `X`-block coordinate into the extended coordinate set. -/
def embX : Fin m → Fin (2 * m + 2) :=
  fun i => (finCombineEquiv m).symm (.inl (.inl i))

/-- Embed a `Z`-block coordinate into the extended coordinate set. -/
def embZ : Fin m → Fin (2 * m + 2) :=
  fun i => (finCombineEquiv m).symm (.inl (.inr i))

/-- The extended coordinate occupied by the scalar `alpha`. -/
def alphaVar : Fin (2 * m + 2) :=
  (finCombineEquiv m).symm (.inr 0)

/-- The extended coordinate occupied by the scalar `beta`. -/
def betaVar : Fin (2 * m + 2) :=
  (finCombineEquiv m).symm (.inr 1)

end

section

variable {K : Type*} {m : ℕ} (u : Fin (2 * m + 2) → K)
include K m u

/-- Project an extended point onto its `X` coordinate block. -/
def projX : Fin m → K :=
  fun i => u (embX m i)

/-- Project an extended point onto its `Z` coordinate block. -/
def projZ : Fin m → K :=
  fun i => u (embZ m i)

end

/-- Project an extended point to the block for basis `W`. -/
abbrev PauliKind.projectPoint {K : Type*} {m : ℕ} (W : PauliKind)
    (u : Fin (2 * m + 2) → K) := W.component (projX u, projZ u)

section

variable {K : Type*} [CommSemiring K]
include K

section

variable {m : ℕ}
    (f g : MvPolynomial (Fin m) K)
include m f g

/-- Combine two multivariate polynomials by the formula
`alpha * f(x) + beta * g(z)` from `def:combine-map`.

Blueprint `def:combine-map`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983`. -/
noncomputable def combinePoly : MvPolynomial (Fin (2 * m + 2)) K :=
  MvPolynomial.X (alphaVar m) * MvPolynomial.rename (embX m) f +
    MvPolynomial.X (betaVar m) * MvPolynomial.rename (embZ m) g

/-- Evaluation of `combinePoly` is the displayed combining formula. -/
theorem combinePoly_eval (u : Fin (2 * m + 2) → K) :
    MvPolynomial.eval u (combinePoly f g) =
      u (alphaVar m) * MvPolynomial.eval (projX u) f +
        u (betaVar m) * MvPolynomial.eval (projZ u) g := by
  change MvPolynomial.eval u (combinePoly f g) =
    u (alphaVar m) * MvPolynomial.eval (u ∘ embX m) f +
      u (betaVar m) * MvPolynomial.eval (u ∘ embZ m) g
  simp [combinePoly, MvPolynomial.eval_rename]

end

/-- A fresh variable times an injectively renamed bounded polynomial retains
the same individual-degree bound.  This is a formalization-only auxiliary for
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983`. -/
private theorem x_mul_rename_mem_polyFunc
    {m n d : ℕ} (hd : 1 ≤ d) {e : Fin m → Fin n} (he : Function.Injective e)
    {a : Fin n} (ha : ∀ i, e i ≠ a) {p : MvPolynomial (Fin m) K}
    (hp : p ∈ polyFunc m K d) :
    MvPolynomial.X a * MvPolynomial.rename e p ∈ polyFunc n K d := by
  classical
  have hrenOutside {j : Fin n} (hj : j ∉ Set.range e) :
      (MvPolynomial.rename e p).degreeOf j = 0 := by
    apply Nat.le_zero.mp
    rw [MvPolynomial.degreeOf_le_iff]
    intro s hs
    rw [MvPolynomial.support_rename_of_injective he] at hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    simp [Finsupp.mapDomain_notin_range _ _ hj]
  have hrenAll (j : Fin n) : (MvPolynomial.rename e p).degreeOf j ≤ d := by
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [MvPolynomial.degreeOf_rename_of_injective he]
      exact degreeOf_le_of_mem_polyFunc hp i
    · simp_all
  have haRange : a ∉ Set.range e := by
    rintro ⟨i, hi⟩
    exact ha i hi
  refine (MvPolynomial.mem_restrictDegree _ _ _).mpr ?_
  intro s hs j
  refine MvPolynomial.degreeOf_le_iff.mp ?_ s hs
  by_cases hj : j = a
  · subst j
    rw [mul_comm]
    exact (MvPolynomial.degreeOf_mul_X_self a _).trans (by
      rw [hrenOutside haRange]
      omega)
  · rw [mul_comm, MvPolynomial.degreeOf_mul_X_of_ne _ hj]
    exact hrenAll j

/-- The combining polynomial has individual degree at most `d` when
`hd : 1 ≤ d`.  The coordinate blocks are disjoint: `f` depends only on the
`x` variables and `g` only on the `z` variables, so multiplication by `alpha`
or `beta` preserves the degree bound on those old coordinates and gives degree
one only in the corresponding fresh coordinate.  Thus `hd` supplies exactly
the needed bound on the two fresh coordinates; no `d + 1` bound is introduced.
The statement is the well-definedness assertion in
blueprint
`def:combine-map`, with source context
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-983` and the
boundary-hypothesis discussion in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/
theorem combinePoly_mem_polyFunc {m d : ℕ}
    (hd : 1 ≤ d) {f g : MvPolynomial (Fin m) K}
    (hf : f ∈ polyFunc m K d) (hg : g ∈ polyFunc m K d) :
    combinePoly f g ∈ polyFunc (2 * m + 2) K d := by
  have hsymm :=
    (finCombineEquiv m).symm.injective
  have hX : Function.Injective (embX m) := by
    intro i j hij
    simpa using hsymm hij
  have hZ : Function.Injective (embZ m) := by
    intro i j hij
    simpa using hsymm hij
  have haX : ∀ i, embX m i ≠ alphaVar m := by
    intro i hi
    simpa using hsymm hi
  have haZ : ∀ i, embZ m i ≠ betaVar m := by
    intro i hi
    simpa using hsymm hi
  exact Submodule.add_mem _ (x_mul_rename_mem_polyFunc hd hX haX hf)
    (x_mul_rename_mem_polyFunc hd hZ haZ hg)

end

/-- Evaluate one member of a global polynomial pair at a point, selecting the
component by Pauli basis.  This is formalization-only support for
`lem:qld-4-7`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`. -/
def evalAt {P : AdmissibleParams} (W : PauliKind)
    (u : PauliPoint P) (pair : PolyPair P) : PauliScalar P :=
  match W with
  | .X => MvPolynomial.eval u pair.1.1
  | .Z => MvPolynomial.eval u pair.2.1

section

variable {K : Type*} [CommSemiring K] {c : ℕ}
    (aX bX aZ bZ uα vα uβ vβ : K)
    (f g : Fin (c + 1) → K)
include K c aX bX aZ bZ uα vα uβ vβ f g

/-- The univariate polynomial before coefficient extraction in
`combineLinePoly`.  The four first scalars describe the affine parameters on
the two projected lines; the last four are the affine `alpha` and `beta`
coordinates of the extended line. -/
noncomputable def combineLinePolynomial : Polynomial K :=
  (Polynomial.C uα + Polynomial.C vα * Polynomial.X) *
      (linePolynomialOfCoefficients f).comp
        (Polynomial.C aX + Polynomial.C bX * Polynomial.X) +
    (Polynomial.C uβ + Polynomial.C vβ * Polynomial.X) *
      (linePolynomialOfCoefficients g).comp
        (Polynomial.C aZ + Polynomial.C bZ * Polynomial.X)

/-- The polynomial underlying `combineLinePoly` has degree at most `c + 1`.
This is the degree assertion accompanying Equation `eq:combine-lines` in
blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
theorem combineLinePolynomial_natDegree_le :
    (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).natDegree ≤ c + 1 := by
  have affineDegree : ∀ u v : K,
      (Polynomial.C u + Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
    intro u v
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp [Polynomial.natDegree_C]
    · refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C]
      simpa using Polynomial.natDegree_X_le (R := K)
  have summandDegree : ∀ (a b u v : K) (h : Fin (c + 1) → K),
      ((Polynomial.C u + Polynomial.C v * Polynomial.X) *
        (linePolynomialOfCoefficients h).comp
          (Polynomial.C a + Polynomial.C b * Polynomial.X)).natDegree ≤ c + 1 := by
    intro a b u v h
    refine Polynomial.natDegree_mul_le.trans ?_
    have hfactor := affineDegree u v
    have hcomp : ((linePolynomialOfCoefficients h).comp
        (Polynomial.C a + Polynomial.C b * Polynomial.X)).natDegree ≤ c := by
      refine Polynomial.natDegree_comp_le.trans ?_
      calc
        _ ≤ c * 1 :=
          Nat.mul_le_mul (linePolynomialOfCoefficients_natDegree_le h) (affineDegree a b)
        _ = c := by ring
    omega
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (summandDegree aX bX uα vα f) (summandDegree aZ bZ uβ vβ g))

/-- Combine two degree-`c` line polynomials using explicit affine
reparameterizations.  Coefficients through degree `c + 1` are extracted from
the genuine composed polynomial, so the definition has no incompatibility
fallback.

This is Equation `eq:combine-lines` in blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
noncomputable def combineLinePoly : Fin (c + 1 + 1) → K :=
  fun i => (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).coeff i.val

end

/-- Compatibility of an extended line with two projected lines and their
explicit affine parameters. These data witness the projection-inclusion
condition preceding Equation `eq:combine-lines`. The theorem
`exists_isCombineLineCompatible_of_projection_mem` in `Combining/LinePolynomial.lean`
constructs them from that condition, including zero directions. Compatibility
alone does not make every coefficient answer a function on a singleton line;
see issue Dengnifer/MIPStarRE-QPBT-bak#695. -/
def IsCombineLineCompatible {K : Type*} [Field K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K)
    (uX vX uZ vZ : Fin m → K)
    (aX bX aZ bZ uα vα uβ vβ : K) : Prop :=
  u (alphaVar m) = uα ∧ v (alphaVar m) = vα ∧
    u (betaVar m) = uβ ∧ v (betaVar m) = vβ ∧
    ∀ t : K,
      projX (u + t • v) = uX + (aX + bX * t) • vX ∧
        projZ (u + t • v) = uZ + (aZ + bZ * t) • vZ

/-- Under explicit line compatibility, `combineLinePoly` satisfies the
advertised line equation and the two projected points have the stated affine
parameters.  This is the specification obligation for Equation
blueprint
`eq:combine-lines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
theorem combineLinePoly_spec {K : Type*} [Field K] {m c : ℕ}
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (aX bX aZ bZ uα vα uβ vβ : K) (f g : Fin (c + 1) → K)
    (hcompat : IsCombineLineCompatible u v uX vX uZ vZ
      aX bX aZ bZ uα vα uβ vβ) :
    ∀ t : K,
      projX (u + t • v) = uX + (aX + bX * t) • vX ∧
      projZ (u + t • v) = uZ + (aZ + bZ * t) • vZ ∧
      evalCoefficient
          (combineLinePoly aX bX aZ bZ uα vα uβ vβ f g) t =
        (uα + t * vα) * evalCoefficient f (aX + bX * t) +
          (uβ + t * vβ) * evalCoefficient g (aZ + bZ * t) := by
  intro t
  obtain ⟨-, -, -, -, hlines⟩ := hcompat
  refine ⟨(hlines t).1, (hlines t).2, ?_⟩
  have hdeg := combineLinePolynomial_natDegree_le aX bX aZ bZ uα vα uβ vβ f g
  have heval :
      evalCoefficient (combineLinePoly aX bX aZ bZ uα vα uβ vβ f g) t =
        (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).eval t := by
    rw [Polynomial.eval_eq_sum_range' (n := c + 1 + 1) (by omega) t]
    simp only [evalCoefficient, combineLinePoly]
    exact Fin.sum_univ_eq_sum_range
      (fun k =>
        (combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).coeff k * t ^ k)
      (c + 1 + 1)
  rw [heval, combineLinePolynomial]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp, linePolynomialOfCoefficients_eval]
  ring

/-! ## Generating laws for restricted lines -/

/-- Split an ambient low-degree vector into its point block and its
seed-direction block.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`. -/
def ldSpaceBlockEquiv (L : LdParams) :
    LdSpace L ≃
      (LdPoint L) × (ScalarQ L × (LdPoint L)) where
  toFun z := (LdSpace.point z, LdSpace.seed z, LdSpace.direction z)
  invFun w := fun i =>
    match i with
    | .inl (.inl j) => w.1 j
    | .inl (.inr _) => w.2.1
    | .inr j => w.2.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j <;> rfl
  right_inv w := rfl

section

variable (L : LdParams)
    (w : (LdPoint L) × (ScalarQ L × (LdPoint L)))
include L w

/-- The axis-line decoder read on the block decomposition. -/
def aLineDescOfBlock :
    LineDesc L :=
  aLineDescOf L ((ldSpaceBlockEquiv L).symm w)

/-- The diagonal-line decoder read on the block decomposition. -/
def dLineDescOfBlock  :
    LineDesc L :=
  dLineDescOf L ((ldSpaceBlockEquiv L).symm w)

end

section

variable (L : LdParams)
include L

/-- The source line decoded from its independent point, seed, and direction blocks. -/
def lineDescOfBlock (kind : LineKind)
    (w : (LdPoint L) × (ScalarQ L × (LdPoint L))) : LineDesc L :=
  match kind with
  | .axis => aLineDescOfBlock L w
  | .diagonal => dLineDescOfBlock L w

/-- A uniform scalar seed in the fiber of coordinate `i`, sampled by its residue. -/
def ldSeedFiberDist (i : Fin L.m) : Distribution (ScalarQ L) :=
  letI : Nonempty (SeedResidue L) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  (uniformDistribution (SeedResidue L)).map (seedOfIndexResidue L i)

theorem ldSeedFiberDist_isProbability (i : Fin L.m) :
    (ldSeedFiberDist L i).IsProbability := by
  letI := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact (uniformDistribution_isProbability _).map _

/-- Restrict the retained seed to a coordinate fiber, leaving the ambient point
and direction uniform and independent. -/
def restrictedLineDist (kind : LineKind) (i : Fin L.m) :
    Distribution (LinePointSample L) :=
  (Distribution.prod (uniformDistribution (LdPoint L))
    (Distribution.prod (ldSeedFiberDist L i) (uniformDistribution (LdPoint L)))).map
      (fun w => (lineDescOfBlock L kind w, w.1))

theorem restrictedLineDist_isProbability (kind : LineKind) (i : Fin L.m) :
    (restrictedLineDist L kind i).IsProbability :=
  (Distribution.prod_isProbability _ _ (uniformDistribution_isProbability _)
    (Distribution.prod_isProbability _ _ (ldSeedFiberDist_isProbability L i)
      (uniformDistribution_isProbability _))).map _

end

end

end MIPStarRE.QPBT
